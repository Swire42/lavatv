{-|
Module      : Lavatv.Retime
Description : Time transformations
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Retime (
  Lavatv.Retime.dynUnroll
) where

import Prelude

import Lavatv.Nat
import Lavatv.Core
import qualified Lavatv.Vec as V

type Vec = V.Vec

dynUnroll :: LiveClock clk => (Signal clk -> Signal clk) -> [Signal 0] -> [Signal 0]
dynUnroll f inp = limit inp $ aux out
  where
    symb = comb gate V.Nil
    out = f symb

    aux :: forall clk. Signal clk -> [Signal 0]
    aux (Signal { uniq=u, signal=Comb g l })
                                                | u == uniq symb = inp
                                                | otherwise = map (makeSignal . Comb g) $ V.transposeVL $ V.map aux l
    aux (Signal { uniq=_, signal=Sample' x}) = repeat x
    aux (Signal { uniq=_, signal=Sample @k x}) = concatMap (replicate (valueOf @k)) (aux x)
    aux (Signal { uniq=_, signal=Reg @k i x}) = i : lastN (valueOf @k) (aux x)

    everyN :: Int -> [a] -> [a]
    everyN _ [] = []
    everyN n (h:t) = h : (everyN n $ drop (n-1) t)

    lastN :: Int -> [a] -> [a]
    lastN n = everyN n . drop (n-1)

    limit :: [a] -> [b] -> [b]
    limit [] _ = []
    limit (_:ta) (hb:tb) = hb : limit ta tb
    limit _ _ = undefined
