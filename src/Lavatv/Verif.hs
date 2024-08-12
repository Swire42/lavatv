{-|
Module      : Lavatv.Verif
Description : High-level SMT-based verification
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Verif (
  Lavatv.Verif.check
) where

import Prelude hiding ((<>))
import Text.PrettyPrint
import System.IO

import Lavatv.Core
import Lavatv.SMT
import Lavatv.HBool

check :: forall h. (UHard h, ClockOf h ~ 1) => Bool -> (h -> HBool 1) -> IO Bool
check verbose f = aux 0
  where
    ifVerb action = if verbose then action else return ()
    circ = withNetlist $ unHBool $ f $ symbolic "input"
    aux depth = do
        ifVerb (putStr (render $ text "Bounded, depth" <+> int depth <> text ": ") >> hFlush stdout)
        bmc <- checkBounded depth circ
        case bmc of
            False -> do
                ifVerb (putStrLn "falsifiable")
                return False
            True -> do
                ifVerb (putStrLn "verified")
                ifVerb (putStr (render $ text "Safe-neighborhood induction, depth" <+> int depth <> text ": ") >> hFlush stdout)
                ind <- checkSafeNeighborhood depth circ
                case ind of
                    True -> do
                        ifVerb (putStrLn "verified")
                        return True
                    False -> do
                        ifVerb (putStrLn "insufficient")
                        aux (depth+1)
