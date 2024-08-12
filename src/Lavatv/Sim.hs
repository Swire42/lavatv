{-|
Module      : Lavatv.Sim
Description : Hardware booleans
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Sim (
  Lavatv.Sim.Sim(..)
, Lavatv.Sim.sigInfoSim
, Lavatv.Sim.SimAs(..)
, Lavatv.Sim.gateSimId
, Lavatv.Sim.simEval
, Lavatv.Sim.bulkSimEval
, Lavatv.Sim.simLift0
, Lavatv.Sim.simLift1
, Lavatv.Sim.simLift2
, Lavatv.Sim.simulate
) where

import Prelude
import Data.Dynamic
import Data.Kind

import Lavatv.Nat
import Lavatv.Vec(Vec)
import qualified Lavatv.Vec as V
import Lavatv.Core
import Lavatv.Uniq
import Lavatv.Retime

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

data Sim (a :: Type) (clk :: Nat) = Sim { unSim :: Signal }

sigInfoSim :: forall clk. KnownNat clk => SigInfo
sigInfoSim = SigInfo { sigClock=valueOf @clk, sigSmt2Type=error "Sim doesn't support verification" }

instance Hard (Sim a clk) where
    sigsCount = 1
    unpack x = [unSim x]
    pack [x] = Sim x
    pack _ = error "bad size"

instance UHard (Sim a clk) where
    type ClockOf (Sim a clk) = clk
    type ReClock (Sim a clk) c = Sim a c

    dontCare () = Sim $ sig_dontcare (sigInfoSim @clk)
    symbolic = Sim . sig_symbolic (sigInfoSim @clk)


class (UHard ha, KnownNat (ClockOf ha), Typeable a) => SimAs ha a where
    fromSim :: Sim a (ClockOf ha) -> ha
    toSim :: ha -> Sim a (ClockOf ha)

instance (Typeable a, KnownNat clk) => SimAs (Sim a clk) a where
    fromSim = id
    toSim = id

instance (KnownNat n, SimAs ha a) => SimAs (Vec n ha) [a] where
    fromSim s = V.fromList [fromSim $ simLift1 (!! k) s | k <- [0..(valueOf @n)-1]]
    toSim v = Sim $ sig_comb (sigInfoSim @(ClockOf ha)) ((gate "toSim") { gateSim=Just $ toDyn . V.toList . V.map @n @Dynamic @a (\x -> fromDyn x (error "bad type"))}) (V.map (unSim . toSim @ha @a) v)

instance (KnownNat n, SimAs ha a) => SimAs (Vec n ha) (Vec n a) where
    fromSim = fromSim . simLift1 V.toList
    toSim = simLift1 V.fromList . toSim

instance (SimAs ha a, SimAs hb b) => SimAs (ha, hb) (a, b) where
    fromSim s = (fromSim $ simLift1 fst s, fromSim $ simLift1 snd s)
    toSim (x, y) = simLift2 (,) (toSim x) (toSim y)


gateSimId :: forall (a :: Type). Typeable a => Gate 1
gateSimId = (gate "simId") { gateSim=gateSim1 (id @a) }

simEval :: Typeable a => Sim a 0 -> a
simEval (Sim { unSim=si }) = fromDyn (eval' si) (error "bad type")
  where
    eval' :: Signal -> Dynamic
    eval' (Signal { sigDef=Comb (GateOp (Gate { gateName=name, gateSim=s }) v) }) = maybe (error ("Gate `"++name++"` has no semantic")) ($ V.map eval' v) s
    eval' (Signal { sigDef=Comb (DontCare) }) = error "cannot simulate DontCare"
    eval' _ = error "unreachable"

bulkSimEval :: Typeable a => [Sim a 0] -> [a]
bulkSimEval l = ret
  where
    eval' :: IntMap Dynamic -> Signal -> IntMap Dynamic
    eval' rmap (Signal { sigUniq=u, sigDef=Comb (GateOp (Gate { gateName=name, gateSim=s }) v) }) =
        if IntMap.member (uniqVal u) rmap then rmap else
        let
          rmap1 = IntMap.insert (uniqVal u) ret' rmap
          rmap2 = V.foldl eval' rmap1 v
          ret' = maybe (error ("Gate `"++name++"` has no semantic")) ($ V.map (rmap2 `get`) v) s
        in rmap2
    eval' rmap (Signal { sigUniq=u, sigDef=Comb DontCare }) = IntMap.insert (uniqVal u) (error "cannot simulate DontCare") rmap
    eval' _ _ = error "unreachable"

    get :: forall a. IntMap a -> Signal -> a
    get rmap s = rmap IntMap.! (sigId s)

    rmapFinal = foldl (\acc x -> eval' acc (unSim x)) IntMap.empty l

    ret = map (\x -> fromDyn (rmapFinal `get` (unSim x)) (error "bad type")) l

simLift0 :: Typeable a => a -> Sim a 0
simLift0 x = Sim $ sig_comb0 (sigInfoSim @0) ((gate "simLift0") { gateSim=gateSim0 \() -> x}) ()

simLift1 :: forall a b clk. (Typeable a, Typeable b, KnownNat clk) => (a -> b) -> (Sim a clk -> Sim b clk)
simLift1 f x = Sim $ sig_comb1 (sigInfoSim @clk) ((gate "simLift1") { gateSim=gateSim1 f }) $ unSim x

simLift2 :: forall a b c clk. (Typeable a, Typeable b, Typeable c, KnownNat clk) => (a -> b -> c) -> (Sim a clk -> Sim b clk -> Sim c clk)
simLift2 f x y = Sim $ sig_comb2 (sigInfoSim @clk) ((gate "simLift2") { gateSim=gateSim2 f }) $ (unSim x, unSim y)

simulate_ :: forall clk a b. (KnownPos clk, Typeable a, Typeable b) => (Sim a clk -> Sim b clk) -> [a] -> [b]
simulate_ circ inp = bulkSimEval (dynUnroll circ (map simLift0 inp))

simulate :: forall a b ha hb. (SimAs ha a, SimAs hb b, KnownPos (ClockOf ha), ClockOf ha ~ ClockOf hb) => (ha -> hb) -> [a] -> [b]
simulate f = simulate_ (toSim . f . fromSim)
