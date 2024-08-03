{-|
Module      : Lavatv.Sim
Description : Hardware booleans
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Sim (
  Lavatv.Sim.Sim(unSim)
, Lavatv.Sim.simEval
, Lavatv.Sim.bulkSimEval
, Lavatv.Sim.simLift0
, Lavatv.Sim.simLift1
, Lavatv.Sim.simLift2
, Lavatv.Sim.simulate
) where

import Prelude
import Data.Dynamic

import Lavatv.Nat
import qualified Lavatv.Vec as V
import Lavatv.Core
import Lavatv.Uniq
import Lavatv.Retime

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

data Sim a (clk :: Nat) = Sim { unSim :: Signal }

instance Hard (Sim a clk) where
    sigsCount = 1
    unpack x = [unSim x]
    pack [x] = Sim x
    pack _ = error "bad size"

instance UHard (Sim a clk) where
    type ClockOf (Sim a clk) = clk
    type ReClock (Sim a clk) c = Sim a c

simEval :: Typeable a => Sim a 0 -> a
simEval (Sim { unSim=si }) = fromDyn (eval' si) (error "bad type")
  where
    eval' :: Signal -> Dynamic
    eval' (Signal { signal=Comb (Gate { name=name, sim=s }) v }) = maybe (error ("Gate `"++name++"` has no semantic")) ($ V.map eval' v) s
    eval' _ = error "unreachable"

bulkSimEval :: Typeable a => [Sim a 0] -> [a]
bulkSimEval l = ret
  where
    eval' :: IntMap Dynamic -> Signal -> IntMap Dynamic
    eval' rmap (Signal { uniq=u, signal=Comb (Gate { name=name, sim=s }) v }) =
        if IntMap.member (uniqVal u) rmap then rmap else
        let
          rmap1 = IntMap.insert (uniqVal u) ret' rmap
          rmap2 = V.foldl eval' rmap1 v
          ret' = maybe (error ("Gate `"++name++"` has no semantic")) ($ V.map (rmap2 `get`) v) s
        in rmap2
    eval' _ _ = error "unreachable"

    get :: forall a. IntMap a -> Signal -> a
    get rmap s = rmap IntMap.! (uniqVal $ uniq s)

    rmapFinal = foldl (\acc x -> eval' acc (unSim x)) IntMap.empty l

    ret :: [_] = map (\x -> fromDyn (rmapFinal `get` (unSim x)) (error "bad type")) l

simLift0 :: Typeable a => a -> Sim a 0
simLift0 x = sigwise0 0 ((gate "simLift0") { sim=gateSim0 \() -> x}) ()

simLift1 :: forall a b clk. (Typeable a, Typeable b, KnownNat clk) => (a -> b) -> (Sim a clk -> Sim b clk)
simLift1 f = sigwise1 (valueOf @clk) ((gate "simLift1") { sim=gateSim1 f })

simLift2 :: forall a b c clk. (Typeable a, Typeable b, Typeable c, KnownNat clk) => (a -> b -> c) -> (Sim a clk -> Sim b clk -> Sim c clk)
simLift2 f = sigwise2 (valueOf @clk) ((gate "simLift2") { sim=gateSim2 f })

simulate :: forall clk a b. (KnownPos clk, Typeable a, Typeable b) => (Sim a clk -> Sim b clk) -> [a] -> [b]
simulate circ inp = bulkSimEval (dynUnroll circ (map simLift0 inp))
