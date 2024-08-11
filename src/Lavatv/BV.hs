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

instance Hard (BV w clk) where
    sigsCount = 1
    unpack x = [unBV x]
    pack [x] = BV x
    pack _ = error "bad size"

instance UHard (BV w clk) where
    type ClockOf (BV w clk) = clk
    type ReClock (BV w clk) c = BV w c

type Bit = BV 1

-- | BV SMT2 litteral
bvLitt :: Int -> Int -> Doc
bvLitt w n = assert (2^w > n) $ text $ printf ("#b%0" ++ show w ++ "b") n

zeros :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
zeros = sigwise0 (valueOf @clk) ((gate "zeros") { gateSmt2=(gateFun0 \() -> bvLitt (valueOf @w) 0)}) ()

ones :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk
ones = sigwise0 (valueOf @clk) ((gate "ones") { gateSmt2=(gateFun0 \() -> bvLitt (valueOf @w) (2^(valueOf @w)-1))}) ()

bvnot :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk
bvnot = sigwise1 (valueOf @clk) ((gate "bvnot") { gateSmt2=(gateFun1 \x -> parens $ (parens $ text "_ bvnot" <+> (int $ valueOf @w)) <+> x) })

bvand :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvand = sigwise2 (valueOf @clk) ((gate "bvand") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvand" <+> (int $ valueOf @w)) <+> x <+> y) })

bvxor :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvxor = sigwise2 (valueOf @clk) ((gate "bvxor") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvxor" <+> (int $ valueOf @w)) <+> x <+> y) })

bvor :: forall w clk. (KnownNat w, KnownNat clk) => BV w clk -> BV w clk -> BV w clk
bvor = sigwise2 (valueOf @clk) ((gate "bvor") { gateSmt2=(gateFun2 \x y -> parens $ (parens $ text "_ bvor" <+> (int $ valueOf @w)) <+> x <+> y) })
