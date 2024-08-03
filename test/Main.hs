module Main (main) where

import Lavatv
import Lavatv.Sim
import Lavatv.Retime
import qualified Lavatv.Vec as V
import qualified Lavatv.Batch as B

main :: IO ()
main = do
    print $ simulate @1 sim1 [1..1000]
    print $ simulate @2 (B.unBatch . B.sweep . unroll @2 sim3 . B.collect (V.replicate $ simLift0 0) . (\x -> B.wrap x)) [1..1000]
