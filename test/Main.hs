module Main (main) where

import Lavatv
import Lavatv.Sim

main :: IO ()
main = print $ simulate @1 sim1 [1..1000]
