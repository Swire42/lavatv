{-|
Module      : Lavatv.BV
Description : Hardware bit vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.BV (
  Lavatv.BV.BV
, Lavatv.BV.Bit
, Lavatv.BV.zeros
, Lavatv.BV.ones
, Lavatv.BV.bvnot
, Lavatv.BV.bvand
, Lavatv.BV.bvxor
, Lavatv.BV.bvor
) where

import Prelude
import Control.Arrow ((>>>))

import Lavatv.Nat
import qualified Lavatv.Vec as V
import Lavatv.Core

data BV (width :: Nat) (clk :: Nat) = BV { unBV :: Signal clk }
  deriving Show

instance Hard (BV w) where
    sigsCount = 1
    unpack x = [unBV x]
    pack [x] = BV x
    pack _ = error "bad size"

type Bit = BV 1

zeros :: forall w clk. (KnownNat w, Clock clk) => BV w clk
zeros = sigwise0 (gate { smt2=Just (\V.Nil -> "#b"++replicate (valueOf @w) '0')}) ()

ones :: forall w clk. (KnownNat w, Clock clk) => BV w clk
ones = sigwise0 (gate { smt2=Just (\V.Nil -> "#b"++replicate (valueOf @w) '1')}) ()

bvnot :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk
bvnot = sigwise1 (gate { smt2=Just (V.destruct1 >>> \(x) -> "((_ bvnot "++(show $ valueOf @w)++") "++x++")") })

bvand :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvand = sigwise2 (gate { smt2=Just (V.destruct2 >>> \(x, y) -> "((_ bvand "++(show $ valueOf @w)++") "++x++" "++y++")") })

bvxor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvxor = sigwise2 (gate { smt2=Just (V.destruct2 >>> \(x, y) -> "((_ bvxor "++(show $ valueOf @w)++") "++x++" "++y++")") })

bvor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvor = sigwise2 (gate { smt2=Just (V.destruct2 >>> \(x, y) -> "((_ bvor "++(show $ valueOf @w)++") "++x++" "++y++")") })
