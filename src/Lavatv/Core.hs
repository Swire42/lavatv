{-|
Module      : Lavatv.Core
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Core (
  Lavatv.Core.Gate(..)
, Lavatv.Core.gate
, Lavatv.Core.Signal_(..)
, Lavatv.Core.Signal(..)
, Lavatv.Core.makeSignal
, Lavatv.Core.Hard(..)
, Lavatv.Core.UHard(..)
, Lavatv.Core.SpedUp
, Lavatv.Core.sig_comb
, Lavatv.Core.sigwise0
, Lavatv.Core.sigwise1
, Lavatv.Core.sigwise2
, Lavatv.Core.sig_sample'
, Lavatv.Core.sig_sample
, Lavatv.Core.sig_reg
, Lavatv.Core.sig_delay
) where

import Prelude
import Data.Kind
import Data.Dynamic
import Control.Exception

import Lavatv.Nat
import Lavatv.Uniq
import qualified Lavatv.Vec as V

type Vec = V.Vec

data Gate (n :: Nat) = Gate { smt2 :: Maybe (Vec n String -> String), sim :: Maybe (Vec n Dynamic -> Dynamic) }

gate :: Gate _
gate = Gate { smt2=Nothing, sim=Nothing }

data Signal_ = forall n. KnownNat n => Comb (Gate n) (Vec n Signal)
             | Sample' Int Signal
             | Sample Int Signal
             | Reg Signal Int Signal

data Signal = Signal { uniq :: Uniq, clock :: Int, signal :: Signal_ }

makeSignal :: Int -> Signal_ -> Signal
makeSignal clock_ signal_ = Signal { uniq=makeUniq (), clock=clock_, signal=signal_ }

instance Show Signal where
    show (Signal { uniq=u, signal=Comb g l }) = show u ++ maybe "???" ($ V.map show l) (smt2 g)
    show (Signal { uniq=u, signal=Sample' _ x}) = show u ++ show x
    show (Signal { uniq=u, signal=Sample _ x}) = show u ++ show x
    show (Signal { uniq=u, clock=clk, signal=Reg i _ x}) = show i ++ " -" ++ show u ++ show clk ++ "> " ++ show x

class Hard h where
    sigsCount :: Int
    unpack :: h -> [Signal]
    pack :: [Signal] -> h

class (Hard h) => UHard h where
    type ClockOf h :: Nat
    type ReClock h (c :: Nat) :: Type

    cstsample :: forall clk. (KnownPos clk, ClockOf h ~ 0, UHard (ReClock h clk)) => h -> ReClock h clk
    cstsample = pack . map (sig_sample' (valueOf @clk)) . unpack

    upsample :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (SpedUp h k)) => h -> SpedUp h k
    upsample = pack . map (sig_sample (valueOf @k)) . unpack

    reg :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (ReClock h 0), UHard (SpedUp h k)) => ReClock h 0 -> SpedUp h k -> h
    reg ini nxt = pack $ zipWith (\i n -> sig_reg i (valueOf @k) n) (unpack ini) (unpack nxt)

    delay :: (KnownPos (ClockOf h), UHard (ReClock h 0)) => ReClock h 0 -> h -> h
    delay ini nxt = pack $ zipWith (\i n -> sig_reg i 1 n) (unpack ini) (unpack nxt)

    dontCare :: KnownNat (ClockOf h) => () -> h
    dontCare = dontCare_ (valueOf @(ClockOf h))

type SpedUp h (k :: Nat) = ReClock h (k * ClockOf h)

instance (KnownNat n, Hard h) => Hard (Vec n h) where
    sigsCount = (valueOf @n) * sigsCount @h
    unpack x = ifZero @n [] (let h `V.Cons` t = x in unpack h ++ unpack t)
    pack [] = V.replicate (pack [])
    pack l = ifZero @n V.Nil (let (lx, ly) = splitAt (sigsCount @h) l in pack lx `V.Cons` pack ly)

instance (KnownNat n, UHard h) => UHard (Vec n h) where
    type ClockOf (Vec n h) = ClockOf h
    type ReClock (Vec n h) c = Vec n (ReClock h c)

instance (Hard a, Hard b) => Hard (a, b) where
    sigsCount = sigsCount @a + sigsCount @b
    unpack (x, y) = unpack x ++ unpack y
    pack l = let (lx, ly) = splitAt (sigsCount @a) l in (pack lx, pack ly)

instance (UHard a, UHard b, ClockOf a ~ ClockOf b) => UHard (a, b) where
    type ClockOf (a, b) = ClockOf a
    type ReClock (a, b) c = (ReClock a c, ReClock b c)

sig_comb :: forall n. KnownNat n => Int -> Gate n -> Vec n Signal -> Signal
sig_comb clk g ins = assert (V.all ((clk ==) . clock) ins) $ makeSignal clk $ Comb g ins

sigwise0 :: forall h. Hard h => Int -> Gate 0 -> () -> h
sigwise0 clk g () = pack $ map (\_ -> sig_comb clk g V.Nil) $ replicate (sigsCount @h) ()

dontCare_ :: forall h. Hard h => Int -> () -> h
dontCare_ clk () = sigwise0 clk (gate {smt2=Just (\_ -> "???")}) ()

sigwise1 :: forall h1 h2. (Hard h1, Hard h2) => Int -> Gate 1 -> h1 -> h2
sigwise1 clk g = pack . map (sig_comb clk g . V.construct1) . unpack

sigwise2 :: forall h1 h2 h3. (Hard h1, Hard h2, Hard h3) => Int -> Gate 2 -> h1 -> h2 -> h3
sigwise2 clk g a b = pack $ map (sig_comb clk g . V.construct2) $ unpack a `zip` unpack b

sig_sample' :: Int -> Signal -> Signal
sig_sample' clk sig = assert (clk > 0) $ assert (clock sig == 0) $ makeSignal clk $ Sample' clk sig

sig_sample :: Int -> Signal -> Signal
sig_sample k sig = assert (k > 0) $ assert (clock sig > 0) $ makeSignal (k * clock sig) $ Sample k sig

sig_reg :: Signal -> Int -> Signal -> Signal
sig_reg ini k nxt = assert (k > 0) $
            assert (clock ini == 0) $
            assert (clock nxt > 0) $
            assert ((clock nxt `mod` k) == 0) $
            makeSignal (clock nxt `div` k) $
            Reg ini k nxt

sig_delay :: Signal -> Signal -> Signal
sig_delay i n = sig_reg i 1 n
