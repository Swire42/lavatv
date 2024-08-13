{-|
Module      : Lavatv.Verif
Description : High-level SMT-based verification
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Verif (
  Lavatv.Verif.checkAuto
, Lavatv.Verif.checkFixed
) where

import Prelude hiding ((<>))
import Text.PrettyPrint
import System.IO

import Lavatv.Core
import qualified Lavatv.Vec as V
import Lavatv.Retime
import Lavatv.SMT
import Lavatv.HBool

red = "\x1b[0;31m"
green = "\x1b[0;32m"
yellow = "\x1b[0;33m"
blue = "\x1b[0;34m"
reset = "\x1b[0m"

checkAuto :: forall h. (UHard h, ClockOf h ~ 1) => Bool -> (h -> HBool 1) -> IO Bool
checkAuto verbose f = checkAuto_ verbose (V.destruct1 . unroll f . V.construct1)

checkAuto_ :: forall h. (UHard h, ClockOf h ~ 1) => Bool -> (h -> HBool 1) -> IO Bool
checkAuto_ verbose f = aux 0
  where
    aux depth = do
        ret <- checkFixed_ verbose depth f
        case ret of
            Just x -> return x
            Nothing -> aux (depth+1)

checkFixed :: forall h. (UHard h, ClockOf h ~ 1) => Bool -> Int -> (h -> HBool 1) -> IO (Maybe Bool)
checkFixed verbose depth f = checkFixed_ verbose depth (V.destruct1 . unroll f . V.construct1)

checkFixed_ :: forall h. (UHard h, ClockOf h ~ 1) => Bool -> Int -> (h -> HBool 1) -> IO (Maybe Bool)
checkFixed_ verbose depth f = aux
  where
    ifVerb action = if verbose then action else return ()
    circ = withNetlist $ unHBool $ f $ symbolic "input"
    aux = do
        ifVerb (putStr (render $ text "Bounded, depth" <+> int depth <> text ": ") >> hFlush stdout)
        bmc <- checkBounded depth circ
        case bmc of
            False -> do
                ifVerb (putStrLn $ red++"falsifiable"++reset)
                return (Just False)
            True -> do
                ifVerb (putStrLn $ blue++"verified"++reset)
                ifVerb (putStr (render $ text "Safe-neighborhood induction, depth" <+> int depth <> text ": ") >> hFlush stdout)
                ind <- checkSafeNeighborhood depth circ
                case ind of
                    True -> do
                        ifVerb (putStrLn $ green++"verified"++reset)
                        return (Just True)
                    False -> do
                        ifVerb (putStrLn $ yellow++"insufficient"++reset)
                        return Nothing
