{-|
Module      : Lavatv.Core
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Core (
  Lavatv.Core.Gate(..)
, Lavatv.Core.gate
, Lavatv.Core.gateFun0
, Lavatv.Core.gateFun1
, Lavatv.Core.gateFun2
, Lavatv.Core.gateFun3
, Lavatv.Core.gateSim0
, Lavatv.Core.gateSim1
, Lavatv.Core.gateSim2
, Lavatv.Core.gateSim3
, Lavatv.Core.SigComb(..)
, Lavatv.Core.Signal_(..)
, Lavatv.Core.Signal(..)
, Lavatv.Core.makeSignal
, Lavatv.Core.Hard(..)
, Lavatv.Core.UHard(..)
, Lavatv.Core.SpedUp
, Lavatv.Core.sig_comb
, Lavatv.Core.sigwiseDontCare
, Lavatv.Core.sigwiseSymbolic
, Lavatv.Core.sigwise0
, Lavatv.Core.sigwise1
, Lavatv.Core.sigwise2
, Lavatv.Core.sig_cstsample
, Lavatv.Core.sig_upsample
, Lavatv.Core.sig_reg
, Lavatv.Core.sig_delay
) where

import Prelude
import Data.Kind
import Data.Dynamic
import Control.Exception
import Control.Arrow ((>>>))

import Lavatv.Nat
import Lavatv.Uniq
import qualified Lavatv.Vec as V

type Vec = V.Vec

data Gate (n :: Nat) = Gate { name :: String, smt2 :: Maybe (Vec n String -> String), sim :: Maybe (Vec n Dynamic -> Dynamic) }

gate :: String -> Gate _
gate name = Gate { name=name, smt2=Nothing, sim=Nothing }

gateFun0 :: (() -> a) -> Maybe (Vec 0 a -> a)
gateFun0 f = Just $ \_ -> f ()

gateFun1 :: (a -> a) -> Maybe (Vec 1 a -> a)
gateFun1 f = Just $ V.destruct1 >>> \x -> f x

gateFun2 :: (a -> a -> a) -> Maybe (Vec 2 a -> a)
gateFun2 f = Just $ V.destruct2 >>> \(x, y) -> f x y

gateFun3 :: (a -> a -> a -> a) -> Maybe (Vec 3 a -> a)
gateFun3 f = Just $ V.destruct3 >>> \(x, y, z) -> f x y z

gateSim0 :: Typeable a => (() -> a) -> Maybe (Vec 0 Dynamic -> Dynamic)
gateSim0 f = Just $ \_ -> toDyn $ f ()

gateSim1 :: (Typeable a, Typeable b) => (a -> b) -> Maybe (Vec 1 Dynamic -> Dynamic)
gateSim1 f = Just $ V.destruct1 >>> \x -> toDyn $ f (fromDyn x (error "bad type"))

gateSim2 :: (Typeable a, Typeable b, Typeable c) => (a -> b -> c) -> Maybe (Vec 2 Dynamic -> Dynamic)
gateSim2 f = Just $ V.destruct2 >>> \(x, y) -> toDyn $ f (fromDyn x (error "bad type")) (fromDyn y (error "bad type"))

gateSim3 :: (Typeable a, Typeable b, Typeable c, Typeable d) => (a -> b -> c -> d) -> Maybe (Vec 3 Dynamic -> Dynamic)
gateSim3 f = Just $ V.destruct3 >>> \(x, y, z) -> toDyn $ f (fromDyn x (error "bad type")) (fromDyn y (error "bad type")) (fromDyn z (error "bad type"))

data SigComb = forall n. KnownNat n => GateOp (Gate n) (Vec n Signal)
             | DontCare
             | Symbolic String

data Signal_ = Comb SigComb
             | CstSample Int Signal
             | UpSample Int Signal
             | Reg Signal Int Signal

data Signal = Signal { uniq :: Uniq, clock :: Int, signal :: Signal_ }

makeSignal :: Int -> Signal_ -> Signal
makeSignal clock_ signal_ = Signal { uniq=makeUniq (), clock=clock_, signal=signal_ }

class Hard h where
    sigsCount :: Int
    unpack :: h -> [Signal]
    pack :: [Signal] -> h

class (Hard h) => UHard h where
    type ClockOf h :: Nat
    type ReClock h (c :: Nat) :: Type

    cstsample :: forall clk. (KnownPos clk, ClockOf h ~ 0, UHard (ReClock h clk)) => h -> ReClock h clk
    cstsample = pack . map (sig_cstsample (valueOf @clk)) . unpack

    upsample :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (SpedUp h k)) => h -> SpedUp h k
    upsample = pack . map (sig_upsample (valueOf @k)) . unpack

    reg :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (ReClock h 0), UHard (SpedUp h k)) => ReClock h 0 -> SpedUp h k -> h
    reg ini nxt = pack $ zipWith (\i n -> sig_reg i (valueOf @k) n) (unpack ini) (unpack nxt)

    delay :: (KnownPos (ClockOf h), UHard (ReClock h 0)) => ReClock h 0 -> h -> h
    delay ini nxt = pack $ zipWith (\i n -> sig_reg i 1 n) (unpack ini) (unpack nxt)

    dontCare :: KnownNat (ClockOf h) => () -> h
    dontCare = sigwiseDontCare (valueOf @(ClockOf h))

    symbolic :: KnownNat (ClockOf h) => String -> h
    symbolic = sigwiseSymbolic (valueOf @(ClockOf h))

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
sig_comb clk g ins = assert (V.all ((clk ==) . clock) ins) $ makeSignal clk $ Comb $ GateOp g ins

sigwise0 :: forall h. Hard h => Int -> Gate 0 -> () -> h
sigwise0 clk g () = pack $ map (\_ -> sig_comb clk g V.Nil) $ replicate (sigsCount @h) ()

sigwiseDontCare :: forall h. Hard h => Int -> () -> h
sigwiseDontCare clk () = pack $ map (\() -> makeSignal clk (Comb DontCare)) $ replicate (sigsCount @h) ()

sigwiseSymbolic :: forall h. Hard h => Int -> String -> h
sigwiseSymbolic clk name = pack $ map (\n -> makeSignal clk (Comb (Symbolic (name++"_"++show n)))) $ [0..(sigsCount @h)-1]

sigwise1 :: forall h1 h2. (Hard h1, Hard h2) => Int -> Gate 1 -> h1 -> h2
sigwise1 clk g = pack . map (sig_comb clk g . V.construct1) . unpack

sigwise2 :: forall h1 h2 h3. (Hard h1, Hard h2, Hard h3) => Int -> Gate 2 -> h1 -> h2 -> h3
sigwise2 clk g a b = pack $ map (sig_comb clk g . V.construct2) $ unpack a `zip` unpack b

sig_cstsample :: Int -> Signal -> Signal
sig_cstsample clk sig = assert (clk > 0) $ assert (clock sig == 0) $ makeSignal clk $ CstSample clk sig

sig_upsample :: Int -> Signal -> Signal
sig_upsample k sig = assert (k > 0) $ assert (clock sig > 0) $ makeSignal (k * clock sig) $ UpSample k sig

sig_reg :: Signal -> Int -> Signal -> Signal
sig_reg ini k nxt = assert (k > 0) $
            assert (clock ini == 0) $
            assert (clock nxt > 0) $
            assert ((clock nxt `mod` k) == 0) $
            makeSignal (clock nxt `div` k) $
            Reg ini k nxt

sig_delay :: Signal -> Signal -> Signal
sig_delay i n = sig_reg i 1 n
