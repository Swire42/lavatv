module Main (main) where

import Lavatv
import Lavatv.Sim
import Lavatv.Retime
import qualified Lavatv.Vec as V
import qualified Lavatv.Batch as B

main :: IO ()
main = do
    print $ simulate @1 sim1 [1..1000]
    print $ simulate @2 (B.unBatch . B.sweep . unroll @2 sim3 . B.collect (V.replicate $ simLift0 0) . B.wrap) [1..1000]
    print $ simulate @3 (B.unBatch . B.sweep . B.unBatch . slowdown @2 (unroll @3 sim3) .B.Batch . B.collect (V.replicate $ simLift0 0) . B.Batch) [1..1000]
