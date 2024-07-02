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

data BV (width :: Nat) (clk :: Nat) = BV { sig :: Signal clk }
  deriving Show

instance Hard (BV w) where
    dontCare = BV . dontCare
    lift1 f = BV . f . sig
    lift2 f a b = BV $ f (sig a) (sig b)

type Bit = BV 1

zeros :: forall w clk. (KnownNat w, Clock clk) => BV w clk
zeros = BV $ Comb (Gate { smt2= \V.Nil -> "#b"++replicate (valueOf @w) '0' }) V.Nil

ones :: forall w clk. (KnownNat w, Clock clk) => BV w clk
ones = BV $ Comb (Gate { smt2= \V.Nil -> "#b"++replicate (valueOf @w) '1' }) V.Nil

bvnot :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk
bvnot = lift1 $ Comb Gate{ smt2=(V.destruct1 >>> \(x) -> "((_ bvnot "++(show $ valueOf @w)++") "++x++")") } . V.construct1

bvand :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvand = lift2 $ curry $ Comb Gate{ smt2=(V.destruct2 >>> \(x, y) -> "((_ bvand "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2

bvxor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvxor = lift2 $ curry $ Comb Gate{ smt2=(V.destruct2 >>> \(x, y) -> "((_ bvxor "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2

bvor :: forall w clk. (KnownNat w, Clock clk) => BV w clk -> BV w clk -> BV w clk
bvor = lift2 $ curry $ Comb Gate{ smt2=(V.destruct2 >>> \(x, y) -> "((_ bvor "++(show $ valueOf @w)++") "++x++" "++y++")") } . V.construct2
