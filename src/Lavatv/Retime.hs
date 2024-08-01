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

dynUnroll :: forall a b. (UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b, UHard (ReClock a 0), UHard (ReClock b 0)) => (a -> b) -> [ReClock a 0] -> [ReClock b 0]
dynUnroll f inp = limit inp $ map pack $ transpose $ map (rmapFinal `get`) (unpack out)
  where
    symb :: a = sigwise0 (valueOf @(ClockOf a)) (gate) ()
    out = f symb
    rmapInit = IntMap.fromList $ map (uniqVal . uniq) (unpack symb) `zip` transpose (map unpack inp)
    rmapFinal = foldl aux rmapInit (unpack out)
    
    aux :: IntMap [Signal] -> Signal -> IntMap [Signal]
    aux rmap s = if IntMap.member (uniqVal $ uniq s) rmap then rmap else
        let
            rmap1 = IntMap.insert (uniqVal $ uniq s) ret rmap
            rmap2 = case signal s of
                Comb _ l -> V.foldl aux rmap1 l
                Sample' _ _ -> rmap1
                Sample _ x -> aux rmap1 x
                Reg _ _ x -> aux rmap1 x
            ret = case signal s of
                Comb g l -> map (comb 0 g) $ V.transposeVL $ V.map (rmap2 `get`) l
                Sample' _ x -> repeat x
                Sample k x -> concatMap (replicate k) (rmap2 `get` x)
                Reg i k x -> i : lastN k (rmap2 `get` x)
        in rmap2

    get :: IntMap [Signal] -> Signal -> [Signal]
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
