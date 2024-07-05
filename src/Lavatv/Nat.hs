{-|
Module      : Lavatv.Nat
Description : GHC.TypeLits and helper functions
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Nat (
  module GHC.TypeLits,
  Lavatv.Nat.valueOf,
  Lavatv.Nat.ifZero,
  Lavatv.Nat.ifEq,
) where

import Prelude
import GHC.TypeLits
import Data.Proxy

valueOf :: forall n. KnownNat n => Int
valueOf = fromInteger $ natVal @n Proxy

ifZero :: forall (n :: Nat) a. KnownNat n => (n ~ 0 => a) -> (1 <= n => a) -> a
ifZero a b = case (cmpNat @0 @n Proxy Proxy, cmpNat @1 @n Proxy Proxy) of
  (EQI, GTI) -> a
  (LTI, EQI) -> b
  (LTI, LTI) -> b
  _ -> error "unreachable"

ifEq :: forall n m a. (KnownNat n, KnownNat m) => (n ~ m => a) -> a -> a
ifEq x y = case (cmpNat @n @m Proxy Proxy) of
  EQI -> x
  _ -> y
