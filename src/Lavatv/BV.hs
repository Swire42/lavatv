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
) where

import Prelude hiding ((<>))
import Control.Exception
import Text.PrettyPrint
import Data.Bits

import Lavatv.Nat
import Lavatv.Core
import qualified Lavatv.Vec as V

data BV (width :: Nat) (clk :: Nat) = BV { unBV :: Signal }

sigInfoBV :: forall width clk. (KnownNat width, KnownNat clk) => SigInfo
sigInfoBV = SigInfo { sigClock=valueOf @clk, sigSmt2Type="(_ BitVec "++show (valueOf @width)++")" }

instance Hard (BV w clk) where
    sigsCount = 1
    unpack x = [unBV x]
    pack [x] = BV x
    pack _ = error "bad size"

instance (KnownNat w, KnownNat clk) => UHard (BV w clk) where
    type ClockOf (BV w clk) = clk
    type ReClock (BV w clk) c = BV w c

    dontCare () = BV $ sig_dontcare (sigInfoBV @w @clk)
    symbolic = BV . sig_symbolic (sigInfoBV @w @clk)

type Bit = BV 1

-- | BV SMT2 litteral
bvLitt :: Int -> Int -> Doc
bvLitt width val = assert (2^width > val) $ text $ "#b" ++ [if testBit val k then '1' else '0' | k <- reverse [0..width-1]]

bvFromInt :: forall w clk. (KnownNat w, KnownNat clk) => Int -> BV w clk
bvFromInt val = assert (2^(valueOf @w) > val) $ BV $ sig_comb0 (sigInfoBV @w @clk) ((gate "bvFromInt") {
      gateSmt2=(gateFun0 \() -> bvLitt (valueOf @w) val)
    , gateSim=(gateSim0 \() -> V.fromList @w $ map (testBit val) [0..(valueOf @w)-1])
    }) ()

bvZeros :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
bvZeros = bvFromInt 0

bvOnes :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
bvOnes = bvFromInt (2^(valueOf @w)-1)

bvNot :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk
bvNot a = BV $ sig_comb1 (sigInfoBV @w @clk) ((gate "bvNot") {
      gateSmt2=(gateFun1 \x -> parens $ (parens $ text "_ bvnot" <+> (int $ valueOf @w)) <+> x)
    , gateSim=gateSim1 (V.map @w not)
    }) (unBV a)

bvAnd :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvAnd a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvAnd") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvand" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w (&&))
    }) (unBV a, unBV b)

bvXor :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvXor a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvXor") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvxor" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w @Bool (/=))
    }) (unBV a, unBV b)

bvOr :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvOr a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvOr") {
      gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvor" <+> (int $ valueOf @w)) <+> x <+> y)
    , gateSim=gateSim2 (V.zipWith @w (||))
    }) (unBV a, unBV b)
