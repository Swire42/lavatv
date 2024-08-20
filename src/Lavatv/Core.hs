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
, Lavatv.Core.SigDef(..)
, Lavatv.Core.SigInfo(..)
, Lavatv.Core.Signal(..)
, Lavatv.Core.makeSignal
, Lavatv.Core.sigId
, Lavatv.Core.HUnit(..)
, Lavatv.Core.Hard(..)
, Lavatv.Core.UHard(..)
, Lavatv.Core.SpedUp
, Lavatv.Core.sig_comb
, Lavatv.Core.sig_comb0
, Lavatv.Core.sig_comb1
, Lavatv.Core.sig_comb2
, Lavatv.Core.sig_comb3
, Lavatv.Core.sig_dontcare
, Lavatv.Core.sig_symbolic
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
import Text.PrettyPrint

import Lavatv.Nat
import Lavatv.Uniq
import qualified Lavatv.Vec as V

type Vec = V.Vec

data Gate (n :: Nat) = Gate { gateName :: String, gateSmt2 :: Maybe (Vec n Doc -> Doc), gateSim :: Maybe (Vec n Dynamic -> Dynamic) }

gate :: String -> Gate _
gate name = Gate { gateName=name, gateSmt2=Nothing, gateSim=Nothing }

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

data SigInfo = SigInfo { sigClock :: Int, sigSmt2Type :: String }

data SigComb = forall n. KnownNat n => GateOp (Gate n) (Vec n Signal)
             | DontCare
             | Symbolic String

data SigDef = Comb SigComb
            | CstSample Int Signal
            | UpSample Int Signal
            | Reg Signal Int Signal

data Signal = Signal { sigUniq :: Uniq, sigInfo :: SigInfo, sigDef :: SigDef }

makeSignal :: SigInfo -> SigDef -> Signal
makeSignal info signal = Signal { sigUniq=makeUniq (), sigInfo=info, sigDef=signal }

sigId :: Signal -> Int
sigId = uniqVal . sigUniq

class Hard h where
    sigsCount :: Int
    unpack :: h -> [Signal]
    pack :: [Signal] -> h

class (Hard h, UHard (ReClock h 0), ClockOf (ReClock h 0) ~ 0, ReClock (ReClock h 0) 0 ~ ReClock h 0) => UHard h where
    type ClockOf h :: Nat
    type ReClock h (c :: Nat) :: Type

    cstsample :: forall clk. (KnownPos clk, ClockOf h ~ 0, UHard (ReClock h clk)) => h -> ReClock h clk
    cstsample = pack . map (sig_cstsample (valueOf @clk)) . unpack

    upsample :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (SpedUp k h)) => h -> SpedUp k h
    upsample = pack . map (sig_upsample (valueOf @(k * ClockOf h)) (valueOf @k)) . unpack

    reg :: forall k. (KnownPos k, KnownPos (ClockOf h), UHard (SpedUp k h)) => ReClock h 0 -> SpedUp k h -> h
    reg ini nxt = pack $ zipWith (\i n -> sig_reg (valueOf @(ClockOf h)) i (valueOf @k) n) (unpack ini) (unpack nxt)

    delay :: (KnownPos (ClockOf h)) => ReClock h 0 -> h -> h
    delay ini nxt = pack $ zipWith (\i n -> sig_reg (valueOf @(ClockOf h)) i 1 n) (unpack ini) (unpack nxt)

    dontcare :: KnownNat (ClockOf h) => () -> h

    symbolic :: KnownNat (ClockOf h) => String -> h

type SpedUp (k :: Nat) h = ReClock h (k * ClockOf h)

data HUnit (clk :: Nat) = HUnit

instance Hard (HUnit clk) where
    sigsCount = 0
    unpack HUnit = []
    pack [] = HUnit
    pack _ = error "bad size"

instance UHard (HUnit clk) where
    type ClockOf (HUnit clk) = clk
    type ReClock (HUnit clk) c = HUnit c

    dontcare () = HUnit
    symbolic _ = HUnit

instance (Hard a, Hard b) => Hard (a, b) where
    sigsCount = sigsCount @a + sigsCount @b
    unpack (x, y) = unpack x ++ unpack y
    pack l = let (lx, ly) = splitAt (sigsCount @a) l in (pack lx, pack ly)

instance (UHard a, UHard b, ClockOf a ~ ClockOf b) => UHard (a, b) where
    type ClockOf (a, b) = ClockOf a
    type ReClock (a, b) c = (ReClock a c, ReClock b c)

    dontcare () = (dontcare (), dontcare ())
    symbolic name = (symbolic (name++"_0"), symbolic (name++"_1"))

instance (KnownNat n, Hard h) => Hard (Vec n h) where
    sigsCount = (valueOf @n) * sigsCount @h
    unpack x = ifZero @n [] (let h `V.Cons` t = x in unpack h ++ unpack t)
    pack l = ifZero @n V.Nil (let (lx, ly) = splitAt (sigsCount @h) l in pack lx `V.Cons` pack ly)

instance (KnownNat n, UHard h) => UHard (Vec n h) where
    type ClockOf (Vec n h) = ClockOf h
    type ReClock (Vec n h) c = Vec n (ReClock h c)

    dontcare () = V.map dontcare $ V.replicate ()
    symbolic name = V.map (\i -> symbolic (name ++ "_" ++ show i)) $ V.fromList [0..(valueOf @n)-1]

sig_comb :: forall n. KnownNat n => SigInfo -> Gate n -> Vec n Signal -> Signal
sig_comb info g ins = assert (V.all ((sigClock info ==) . sigClock . sigInfo) ins) $ makeSignal info $ Comb $ GateOp g ins

sig_comb0 :: SigInfo -> Gate 0 -> () -> Signal
sig_comb0 info g () = sig_comb info g V.Nil

sig_comb1 :: SigInfo -> Gate 1 -> Signal -> Signal
sig_comb1 info g = sig_comb info g . V.construct1

sig_comb2 :: SigInfo -> Gate 2 -> (Signal, Signal) -> Signal
sig_comb2 info g = sig_comb info g . V.construct2

sig_comb3 :: SigInfo -> Gate 3 -> (Signal, Signal, Signal) -> Signal
sig_comb3 info g = sig_comb info g . V.construct3

sig_dontcare :: SigInfo -> Signal
sig_dontcare info = makeSignal info $ Comb $ DontCare

sig_symbolic :: SigInfo -> String -> Signal
sig_symbolic info name = makeSignal info $ Comb $ Symbolic name

sig_cstsample :: Int -> Signal -> Signal
sig_cstsample clk sig =
            assert (clk > 0) $
            makeSignal ((sigInfo sig) { sigClock=clk }) $
            CstSample clk (assert (sigClock (sigInfo sig) == 0) sig)

sig_upsample :: Int -> Int -> Signal -> Signal
sig_upsample clk k sig =
            assert (clk > 0) $
            assert (k > 0) $
            makeSignal ((sigInfo sig) { sigClock=clk }) $
            UpSample k (assert (k * sigClock (sigInfo sig) == clk) sig)

sig_reg :: Int -> Signal -> Int -> Signal -> Signal
sig_reg clk ini k nxt =
            assert (clk > 0) $
            assert (k > 0) $
            makeSignal ((sigInfo ini) { sigClock=clk }) $
            Reg
                (assert (sigClock (sigInfo ini) == 0) ini)
                k
                (assert (k * clk == sigClock (sigInfo nxt)) nxt)

sig_delay :: Int -> Signal -> Signal -> Signal
sig_delay clk i n = sig_reg clk i 1 n
