{-|
Module      : Lavatv.HVec
Description : Hardware pairs
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.HPair (
  Lavatv.HPair.HPair(..)
, Lavatv.HPair.hfst
, Lavatv.HPair.hsnd
, Lavatv.HPair.huncurry
) where

import Prelude
import Data.Kind

import Lavatv.Nat
import Lavatv.Core

newtype HPair (a :: Nat -> Type) (b :: Nat -> Type) (clk :: Nat) = HPair { unHPair :: (a clk, b clk) }

hfst :: HPair a b clk -> a clk
hfst = fst . unHPair

hsnd :: HPair a b clk -> b clk
hsnd = snd . unHPair

huncurry :: (a clk -> b clk -> c clk) -> HPair a b clk -> c clk
huncurry f = uncurry f . unHPair

instance (Hard a, Hard b) => Hard (HPair a b) where
    dontCare () = HPair (dontCare (), dontCare ())
    lift1 f x = HPair (lift1 f (hfst x), lift1 f (hsnd x))
    lift2 f x y = HPair (lift2 f (hfst x) (hfst y), lift2 f (hsnd x) (hsnd y))

