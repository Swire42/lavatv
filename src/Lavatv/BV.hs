{-|
Module      : Lavatv.BV
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.BV (
  Lavatv.BV.BV(..)
, Lavatv.BV.Bit
, Lavatv.BV.bvFromInt
, Lavatv.BV.bvZeros
, Lavatv.BV.bvOnes
, Lavatv.BV.bvNot
, Lavatv.BV.bvAnd
, Lavatv.BV.bvXor
, Lavatv.BV.bvOr
, Lavatv.BV.bvConcat
, Lavatv.BV.bvExtract
, Lavatv.BV.bit2bool
, Lavatv.BV.bool2bit
) where

import Prelude hiding ((<>))
import Control.Exception
import Text.PrettyPrint

import Lavatv.Nat
import Lavatv.Core
import Lavatv.Vec(Vec)
import qualified Lavatv.Vec as V
import Lavatv.Sim
import Lavatv.HBool

-- | Bit vector. LSB is the closest to Nil.
data BV (width :: Nat) (clk :: Nat) = BV { unBV :: Signal }

type Bit = BV 1

sigInfoBV :: forall width clk. (KnownPos width, KnownNat clk) => SigInfo
sigInfoBV = SigInfo { sigClock=valueOf @clk, sigSmt2Type="(_ BitVec "++show (valueOf @width)++")" }

instance Hard (BV w clk) where
    sigsCount = 1
    unpack x = [unBV x]
    pack [x] = BV x
    pack _ = error "bad size"

instance (KnownPos w, KnownNat clk) => UHard (BV w clk) where
    type ClockOf (BV w clk) = clk
    type ReClock (BV w clk) c = BV w c

    dontcare () = BV $ sig_dontcare (sigInfoBV @w @clk)
    symbolic = BV . sig_symbolic (sigInfoBV @w @clk)

instance (KnownPos w, KnownNat clk) => SimAs (BV w clk) (Vec w Bool) where
    fromSim = BV . sig_comb1 (sigInfoBV @w @clk) (gateSimId @(Vec w Bool)) . unSim
    toSim = Sim . sig_comb1 (sigInfoSim @clk) (gateSimId @(Vec w Bool)) . unBV

instance (KnownPos w, KnownNat clk) => SimAs (BV w clk) [Bool] where
    fromSim = fromSim . simLift1 (V.fromList @w)
    toSim = simLift1 (V.toList @w) . toSim

instance (KnownPos w, KnownNat clk) => SimAs (BV w clk) Integer where
    fromSim = fromSim . simLift1 (int2bits @w)
    toSim = simLift1 (bits2int @w) . toSim

instance (KnownNat clk) => SimAs (Bit clk) Bool where
    fromSim = fromSim . simLift1 V.construct1
    toSim = simLift1 V.destruct1 . toSim

instance (KnownNat clk, KnownPos w) => HEq (BV w clk) where
    heq a b = HBool $ sig_comb2 (sigInfoHBool @clk) ((gate "heq") {
          gateSmt2=(gateFun2 \x y -> parens $ text "=" <+> x <+> y)
        , gateSim=gateSim2 @(Vec w Bool) @(Vec w Bool) (==)
        }) (unBV a, unBV b)

-- | BV SMT2 litteral
bvLitt :: forall w. KnownPos w => Integer -> Doc
bvLitt val = text $ "#b" ++ (V.toList $ V.map (\bit -> if bit then '1' else '0') $ int2bits @w val)

bits2int :: forall w. KnownPos w => Vec w Bool -> Integer
bits2int = V.foldl (\acc bit -> acc*2 + if bit then 1 else 0) 0

int2bits :: forall w. KnownPos w => Integer -> Vec w Bool
int2bits val = assert (2^(valueOf @w) > val) $ V.map (\x -> x `mod` 2 == 1) $ V.iterate (`div` 2) val

bvFromInt :: forall w clk. (KnownPos w, KnownNat clk) => Integer -> BV w clk
bvFromInt val = assert (2^(valueOf @w) > val) $ BV $ sig_comb0 (sigInfoBV @w @clk) ((gate "bvFromInt") {
      gateSmt2=(gateFun0 \() -> bvLitt @w val)
    , gateSim=(gateSim0 \() -> int2bits @w val)
    }) ()

bvZeros :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk
bvZeros = bvFromInt 0

bvOnes :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk
bvOnes = bvFromInt (2^(valueOf @w)-1)

bvNot :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk -> BV w clk
bvNot a = BV $ sig_comb1 (sigInfoBV @w @clk) ((gate "bvNot") {
      gateSmt2=(gateFun1 \x -> parens $ (parens $ text "_ bvnot" <+> (int $ valueOf @w)) <+> x)
    , gateSim=gateSim1 (V.map @w not)
    }) (unBV a)

bvAnd :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvAnd a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvAnd") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvand" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w (&&))
    }) (unBV a, unBV b)

bvXor :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvXor a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvXor") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvxor" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w @Bool (/=))
    }) (unBV a, unBV b)

bvOr :: forall w clk. (KnownPos w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvOr a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvOr") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvor" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w (||))
    }) (unBV a, unBV b)

bvConcat :: forall wa wb clk. (KnownPos wa, KnownPos wb, KnownNat clk) => BV wa clk -> BV wb clk -> BV (wa+wb) clk
bvConcat a b = BV $ sig_comb2 (sigInfoBV @(wa+wb) @clk) ((gate "bvConcat") {
      gateSmt2=(gateFun2 \x y -> parens $ text "concat" <+> x <+> y)
    , gateSim=gateSim2 (V.append @wa @wb @Bool)
    }) (unBV a, unBV b)

bvExtract :: forall i j w clk. (KnownPos w, KnownNat i, KnownNat j, i+1 <= j, j <= w, KnownNat clk) => BV w clk -> BV (j-i) clk
bvExtract a = BV $ sig_comb1 (sigInfoBV @(j-i) @clk) ((gate "bvExtract") {
      gateSmt2=(gateFun1 \x -> parens $ (parens $ text "_ extract" <+> (int $ valueOf @(j-1)) <+> (int $ valueOf @i)) <+> x)
    , gateSim=gateSim1 (V.drop @j @i . V.take @j @w @Bool)
    }) (unBV a)

bit2bool :: forall clk. KnownNat clk => Bit clk -> HBool clk
bit2bool = heq bvOnes

bool2bit :: forall clk. KnownNat clk => HBool clk -> Bit clk
bool2bit x = hite x (bvOnes, bvZeros)
