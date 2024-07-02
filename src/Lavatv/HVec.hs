{-|
Module      : Lavatv.HVec
Description : Hardware vectors
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.HVec (
  Lavatv.HVec.HVec
) where

import Prelude
import Data.Kind

import Lavatv.Nat
import qualified Lavatv.Vec as V
import Lavatv.Core

newtype HVec (n :: Nat) (h :: Nat -> Type) (clk :: Nat) = HVec { unHVec :: V.Vec n (h clk) }

instance (KnownNat n, Hard h) => Hard (HVec n h) where
    dontCare () = HVec $ V.map dontCare $ V.replicate ()
    lift1 f = HVec . V.map (lift1 f) . unHVec
    lift2 f a b = HVec $ V.zipWith (lift2 f) (unHVec a) (unHVec b)

