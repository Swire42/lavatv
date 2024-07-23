{-|
Module      : Lavatv.Sim
Description : Hardware booleans
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Sim (
  Lavatv.Sim.Sim(unSim)
, Lavatv.Sim.simLift0
, Lavatv.Sim.simEval
, Lavatv.Sim.bulkSimEval
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

data Sim a (clk :: Nat) = Sim { unSim :: Signal clk }

instance Hard (Sim a) where
    sigsCount = 1
    unpack x = [unSim x]
    pack [x] = Sim x
    pack _ = error "bad size"

simLift0 :: Typeable a => a -> Sim a 0
simLift0 x = sigwise0 (gate { sim=Just (\_ -> toDyn x)}) ()

simEval :: Typeable a => Sim a 0 -> a
simEval (Sim { unSim=si }) = fromDyn (eval' si) (error "bad type")
  where
    eval' :: Signal 0 -> Dynamic
    eval' (Signal { signal=Comb (Gate { sim=s }) v }) = maybe (error "no semantic") ($ V.map eval' v) s
    eval' _ = error "unreachable"

bulkSimEval :: Typeable a => [Sim a 0] -> [a]
bulkSimEval l = ret
  where
    eval' :: IntMap Dynamic -> Signal 0 -> IntMap Dynamic
    eval' rmap (Signal { uniq=u, signal=Comb (Gate { sim=s }) v }) =
        if IntMap.member (uniqVal u) rmap then rmap else
        let
          rmap1 = IntMap.insert (uniqVal u) ret' rmap
          rmap2 = V.foldl eval' rmap1 v
          ret' = maybe (error "no semantic") ($ V.map (rmap2 `get`) v) s
        in rmap2
    eval' _ _ = error "unreachable"

    get :: forall a clk. IntMap a -> Signal clk -> a
    get rmap s = rmap IntMap.! (uniqVal $ uniq s)

    rmapFinal = foldl (\acc x -> eval' acc (unSim x)) IntMap.empty l

    ret :: [_] = map (\x -> fromDyn (rmapFinal `get` (unSim x)) (error "bad type")) l

simLift1 :: forall a b clk. (Typeable a, Typeable b, Clock clk) => (a -> b) -> (Sim a clk -> Sim b clk)
simLift1 f = sigwise1 (gate { sim=Just (\(x `V.Cons` V.Nil) -> toDyn $ f $ fromDyn x (error "bad type"))})

simLift2 :: forall a b c clk. (Typeable a, Typeable b, Typeable c, Clock clk) => (a -> b -> c) -> (Sim a clk -> Sim b clk -> Sim c clk)
simLift2 f = sigwise2 (gate { sim=Just (\(x `V.Cons` (y `V.Cons` V.Nil)) -> toDyn $ f (fromDyn x (error "bad type")) (fromDyn y (error "bad type")))})

simulate :: forall clk a b. (LiveClock clk, Typeable a, Typeable b) => (Sim a clk -> Sim b clk) -> [a] -> [b]
simulate circ inp = bulkSimEval (dynUnroll circ (map simLift0 inp))
