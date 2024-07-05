{-|
Module      : Lavatv.Uniq
Description : Unique values for observable sharing
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Uniq (
  Lavatv.Uniq.Uniq(uniqVal)
, Lavatv.Uniq.makeUniq
) where

import Prelude

import Data.IORef
import System.IO.Unsafe(unsafePerformIO)

newtype Uniq = Uniq { uniqVal :: Int } deriving Eq

{-# NOINLINE count #-}
-- Global unique values counter
count :: IORef Int
count = unsafePerformIO $ newIORef 0

{-# NOINLINE makeUniq #-}
-- Create a new unique value
makeUniq :: () -> Uniq
makeUniq () = Uniq $ unsafePerformIO $ atomicModifyIORef' count (\x -> (x + 1, x))

instance Show Uniq where
  show (Uniq { uniqVal=u }) = "{" ++ show u ++ "}"
