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
import Control.Arrow ((***))

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
    sigsCount = (sigsCount @a) + (sigsCount @b)
    unpack x = unpack (hfst x) ++ unpack (hsnd x)
    pack = HPair . (pack *** pack) . splitAt (sigsCount @a)
