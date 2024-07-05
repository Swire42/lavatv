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
, Lavatv.Sim.simLift1
, Lavatv.Sim.simLift2
) where

import Prelude
import Data.Dynamic
import Control.Arrow ((>>>))

import Lavatv.Nat
import qualified Lavatv.Vec as V
import qualified Lavatv.HPair as HP
import Lavatv.Core

data Sim a (clk :: Nat) = Sim { unSim :: Signal clk }

instance Hard (Sim a) where
    sigsCount = 1
    unpack x = [unSim x]
    pack [x] = Sim x
    pack _ = error "bad size"

simLift0 :: Typeable a => a -> Sim a 0
simLift0 x = sigwise0 (gate { sim=(\_ -> toDyn x)}) ()

simEval :: Typeable a => Sim a 0 -> a
simEval (Sim { unSim=si }) = fromDyn (eval' si) (error "bad type")
  where
    eval' :: Signal 0 -> Dynamic
    eval' (Signal { signal=Comb (Gate { sim=s }) v }) = (s $ V.map eval' v)

simLift1 :: forall a b clk. (Typeable a, Typeable b, Clock clk) => (a -> b) -> (Sim a clk -> Sim b clk)
simLift1 f = sigwise1 (gate { sim=(\(x `V.Cons` V.Nil) -> toDyn $ f $ fromDyn x (error "bad type"))})

simLift2 :: forall a b c clk. (Typeable a, Typeable b, Typeable c, Clock clk) => (a -> b -> c) -> (Sim a clk -> Sim b clk -> Sim c clk)
simLift2 f = sigwise2 (gate { sim=(\(x `V.Cons` (y `V.Cons` V.Nil)) -> toDyn $ f (fromDyn x (error "bad type")) (fromDyn y (error "bad type")))})
