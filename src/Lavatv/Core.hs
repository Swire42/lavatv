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
, Lavatv.Core.Signal_(..)
, Lavatv.Core.Signal(..)
, Lavatv.Core.makeSignal
, Lavatv.Core.Hard(..)
, Lavatv.Core.comb
, Lavatv.Core.sigwise0
, Lavatv.Core.dontCare
, Lavatv.Core.sigwise1
, Lavatv.Core.sigwise2
, Lavatv.Core.sample'
, Lavatv.Core.sample
, Lavatv.Core.reg
, Lavatv.Core.delay
) where

import Prelude
import Data.Dynamic

import Lavatv.Nat
import Lavatv.Uniq
import qualified Lavatv.Vec as V

type Vec = V.Vec



type Clock clk = KnownNat clk
type LiveClock clk = (KnownNat clk, 1 <= clk)

data Gate (n :: Nat) = Gate { smt2 :: Maybe (Vec n String -> String), sim :: Maybe (Vec n Dynamic -> Dynamic) }

gate :: Gate _
gate = Gate { smt2=Nothing, sim=Nothing }

data Signal_ (clk :: Nat) where
    Comb :: forall n clk. (KnownNat n, Clock clk) => Gate n -> Vec n (Signal clk) -> Signal_ clk
    Sample' :: forall clk. LiveClock clk => Signal 0 -> Signal_ clk
    Sample :: forall k clk. (KnownNat k, 1 <= k, LiveClock clk) => Signal clk -> Signal_ (k*clk)
    Reg :: forall k clk. (KnownNat k, 1 <= k, LiveClock clk) => Signal 0 -> Signal (k*clk) -> Signal_ clk

data Signal (clk :: Nat) = Signal { uniq :: Uniq, signal :: Signal_ clk }

makeSignal :: Signal_ clk -> Signal clk
makeSignal signal_ = Signal { uniq=makeUniq (), signal=signal_ }

instance Show (Signal clk) where
    show (Signal { uniq=u, signal=Comb g l }) = show u ++ maybe "???" ($ V.map show l) (smt2 g)
    show (Signal { uniq=u, signal=Sample' x}) = show u ++ show x
    show (Signal { uniq=u, signal=Sample x}) = show u ++ show x
    show (Signal { uniq=u, signal=Reg @k i x}) = show i ++ " -" ++ show u ++ show (valueOf @clk) ++ "> " ++ show x

class Hard h where
    sigsCount :: Int
    unpack :: h clk -> [Signal clk]
    pack :: [Signal clk] -> h clk

instance Hard Signal where
    sigsCount = 1
    unpack x = [x]
    pack [x] = x
    pack _ = error "bad size"

comb :: forall n clk. (KnownNat n, Clock clk) => Gate n -> Vec n (Signal clk) -> Signal clk
comb g ins = makeSignal $ Comb g ins

sigwise0 :: forall h clk. (Hard h, Clock clk) => Gate 0 -> () -> h clk
sigwise0 g () = pack $ map (\_ -> comb g V.Nil) $ replicate (sigsCount @h) ()

dontCare :: forall h clk. (Hard h, Clock clk) => () -> h clk
dontCare () = sigwise0 undefined ()

sigwise1 :: forall h1 h2 clk. (Hard h1, Hard h2, Clock clk) => Gate 1 -> h1 clk -> h2 clk
sigwise1 g = pack . map (comb g . V.construct1) . unpack

sigwise2 :: forall h1 h2 h3 clk. (Hard h1, Hard h2, Hard h3, Clock clk) => Gate 2 -> h1 clk -> h2 clk -> h3 clk
sigwise2 g a b = pack $ map (comb g . V.construct2) $ unpack a `zip` unpack b

sample' :: forall h clk. (Hard h, LiveClock clk) => h 0 -> h clk
sample' = pack . map (makeSignal . Sample') . unpack

sample :: forall h k clk. (Hard h, KnownNat k, 1 <= k, LiveClock clk) => h clk -> h (k*clk)
sample = pack . map (makeSignal . Sample) . unpack

reg :: forall h k clk. (Hard h, KnownNat k, 1 <= k, LiveClock clk) => h 0 -> h (k*clk) -> h clk
reg a b = pack $ zipWith (\x y -> makeSignal $ Reg x y) (unpack a) (unpack b)

delay :: forall h clk. (Hard h, LiveClock clk) => h 0 -> h clk -> h clk
delay i n = reg @_ @1 i n
