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
import Data.List

import Lavatv.Nat
import Lavatv.Core
import Lavatv.Uniq
import qualified Lavatv.Vec as V

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

type Vec = V.Vec

dynUnroll :: forall clk a b. (Hard a, Hard b, LiveClock clk) => (a clk -> b clk) -> [a 0] -> [b 0]
dynUnroll f inp = limit inp $ map pack $ transpose $ map (rmapFinal `get`) (unpack out)
  where
    symb = map (\_ -> comb gate V.Nil) $ replicate (sigsCount @a) ()
    out = f (pack symb)
    rmapInit = IntMap.fromList $ map (uniqVal . uniq) symb `zip` transpose (map unpack inp)
    rmapFinal = foldl aux rmapInit (unpack out)
    
    aux :: forall clk'. IntMap [Signal 0] -> Signal clk' -> IntMap [Signal 0]
    aux rmap s = if IntMap.member (uniqVal $ uniq s) rmap then rmap else
        let
            rmap1 = IntMap.insert (uniqVal $ uniq s) ret rmap
            rmap2 = case signal s of
                Comb _ l -> V.foldl aux rmap1 l
                Sample' _ -> rmap1
                Sample @k x -> aux rmap1 x
                Reg @k _ x -> aux rmap1 x
            ret = case signal s of
                Comb g l -> map (makeSignal . Comb g) $ V.transposeVL $ V.map (rmap2 `get`) l
                Sample' x -> repeat x
                Sample @k x -> concatMap (replicate (valueOf @k)) (rmap2 `get` x)
                Reg @k i x -> i : lastN (valueOf @k) (rmap2 `get` x)
        in rmap2

    get :: forall clk'. IntMap [Signal 0] -> Signal clk' -> [Signal 0]
    get rmap s = rmap IntMap.! (uniqVal $ uniq s)

    everyN :: forall a'. Int -> [a'] -> [a']
    everyN _ [] = []
    everyN n (h:t) = h : (everyN n $ drop (n-1) t)

    lastN :: forall a'. Int -> [a'] -> [a']
    lastN n = everyN n . drop (n-1)

    limit :: forall a' b'. [a'] -> [b'] -> [b']
    limit [] _ = []
    limit (_:ta) (hb:tb) = hb : limit ta tb
    limit _ _ = error "bad size"
