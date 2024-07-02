{-|
Module      : Lavatv.Core
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Core (
  Lavatv.Core.Clock
, Lavatv.Core.LiveClock
, Lavatv.Core.Gate(..)
, Lavatv.Core.gate
, Lavatv.Core.Signal(..)
, Lavatv.Core.Hard(..)
, Lavatv.Core.sample'
, Lavatv.Core.sample
, Lavatv.Core.reg
, Lavatv.Core.delay
) where

import Prelude

import Lavatv.Nat
import qualified Lavatv.Vec as V

type Vec = V.Vec



type Clock clk = KnownNat clk
type LiveClock clk = (KnownNat clk, 1 <= clk)

data Gate (n :: Nat) = Gate { smt2 :: Vec n String -> String }

gate :: Gate _
gate = Gate { smt2=undefined }

data Signal (clk :: Nat) where
    Comb :: forall n clk. (KnownNat n, Clock clk) => Gate n -> Vec n (Signal clk) -> Signal clk
    Sample' :: forall clk. Clock clk => Signal 0 -> Signal clk
    Sample :: forall k clk. (KnownNat k, 1 <= k, LiveClock clk) => Signal clk -> Signal (k*clk)
    Reg :: forall k clk. (KnownNat k, 1 <= k, LiveClock clk) => Signal 0 -> Signal (k*clk) -> Signal clk

instance Show (Signal clk) where
    show (Comb g l) = (smt2 g) (V.map show l)
    show (Sample' x) = show x
    show (Sample x) = show x
    show (Reg i (x :: Signal (k*a))) = show i ++ " -" ++ show (valueOf @clk) ++ "> " ++ show x

class Hard h where
    dontCare :: forall a. (Clock a) => () -> h a
    lift1 :: forall a b. (Clock a, Clock b) => (Signal a -> Signal b) -> h a -> h b
    lift2 :: forall a b c. (Clock a, Clock b, Clock c) => (Signal a -> Signal b -> Signal c) -> h a -> h b -> h c

instance Hard Signal where
    dontCare = undefined
    lift1 = id
    lift2 = id

sample' :: forall h clk. (Hard h, Clock clk) => h 0 -> h clk
sample' = lift1 Sample'

sample :: forall h k clk. (Hard h, KnownNat k, 1 <= k, LiveClock clk) => h clk -> h (k*clk)
sample = lift1 Sample

reg :: forall h k clk. (Hard h, KnownNat k, 1 <= k, LiveClock clk) => h 0 -> h (k*clk) -> h clk
reg = lift2 Reg

delay :: forall h clk. (Hard h, LiveClock clk) => h 0 -> h clk -> h clk
delay i n = reg @_ @1 i n
