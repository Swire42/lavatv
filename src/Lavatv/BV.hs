{-|
Module      : Lavatv.BV
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.BV (
  Lavatv.BV.BV(..)
, Lavatv.BV.Bit
, Lavatv.BV.zeros
, Lavatv.BV.ones
, Lavatv.BV.bvnot
, Lavatv.BV.bvand
, Lavatv.BV.bvxor
, Lavatv.BV.bvor
) where

import Prelude
import Control.Exception
import Text.PrettyPrint
import Text.Printf

import Lavatv.Nat
import Lavatv.Core

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
bvLitt w n = assert (2^w > n) $ text $ printf ("#b%0" ++ show w ++ "b") n

zeros :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
zeros = BV $ sig_comb0 (sigInfoBV @w @clk) ((gate "zeros") { gateSmt2=(gateFun0 \() -> bvLitt (valueOf @w) 0)}) ()

ones :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
ones = BV $ sig_comb0 (sigInfoBV @w @clk) ((gate "ones") { gateSmt2=(gateFun0 \() -> bvLitt (valueOf @w) (2^(valueOf @w)-1))}) ()

bvnot :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk
bvnot a = BV $ sig_comb1 (sigInfoBV @w @clk) ((gate "bvnot") { gateSmt2=(gateFun1 \x -> parens $ (parens $ text "_ bvnot" <+> (int $ valueOf @w)) <+> x) }) (unBV a)

bvand :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvand a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvand") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvand" <+> (int $ valueOf @w)) <+> x <+> y) }) (unBV a, unBV b)

bvxor :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvxor a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvxor") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvxor" <+> (int $ valueOf @w)) <+> x <+> y) }) (unBV a, unBV b)

bvor :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvor a b = BV $ sig_comb2 (sigInfoBV @w @clk) ((gate "bvor") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvor" <+> (int $ valueOf @w)) <+> x <+> y) }) (unBV a, unBV b)
