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
zeros = BV $ comb (gate { smt2= \V.Nil -> "#b"++replicate (valueOf @w) '0' }) V.Nil

ones :: forall w clk. (KnownNat w, Clock clk) => BV w clk
ones = BV $ comb (gate { smt2= \V.Nil -> "#b"++replicate (valueOf @w) '1' }) V.Nil

bvnot :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk
bvnot = undefined -- lift1 $ comb gate { smt2=(V.destruct1 >>> \(x) -> "((_ bvnot "++(show $ valueOf @w)++") "++x++")") } . V.construct1

bvand :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvand = undefined -- lift2 $ curry $ comb gate { smt2=(V.destruct2 >>> \(x, y) -> "((_ bvand "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2

bvxor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvxor = undefined -- lift2 $ curry $ comb gate { smt2=(V.destruct2 >>> \(x, y) -> "((_ bvxor "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2

bvor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvor = undefined -- lift2 $ curry $ comb gate { smt2=(V.destruct2 >>> \(x, y) -> "((_ bvor "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2
