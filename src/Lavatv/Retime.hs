{-|
Module      : Lavatv.Retime
Description : Time transformations
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Retime (
  Lavatv.Retime.dynUnroll
, Lavatv.Retime.unroll
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

memo :: (IntMap a -> Signal -> a) -> IntMap a -> Signal -> IntMap a
memo f rmap s = if IntMap.member (uniqVal $ uniq s) rmap then rmap else
    let ret = IntMap.insert (uniqVal $ uniq s) (f ret s) rmap in ret

mGet :: IntMap a -> Signal -> a
mGet rmap s = rmap IntMap.! (uniqVal $ uniq s)

everyN :: forall a'. Int -> [a'] -> [a']
everyN _ [] = []
everyN n (h:t) = h : (everyN n $ drop (n-1) t)

lastN :: forall a'. Int -> [a'] -> [a']
lastN n = everyN n . drop (n-1)

lazyList 0 _       = []
lazyList n ~(x:xs) = x : lazyList (n-1) xs

dynUnroll :: forall a b. (UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b, UHard (ReClock a 0), UHard (ReClock b 0)) => (a -> b) -> [ReClock a 0] -> [ReClock b 0]
dynUnroll f inp = limit inp $ map pack $ transpose $ map (rmapFinal `mGet`) (unpack out)
  where
    symb :: a = sigwise0 (valueOf @(ClockOf a)) (gate "symb") ()
    out = f symb
    rmapInit = IntMap.fromList $ map (uniqVal . uniq) (unpack symb) `zip` transpose (map unpack inp)
    rmapFinal = foldl aux rmapInit (unpack out)
    
    aux :: IntMap [Signal] -> Signal -> IntMap [Signal]
    aux = memo \rmap s -> let
            rmap2 = case signal s of
                Comb _ l -> V.foldl aux rmap l
                Sample' _ _ -> rmap
                Sample _ x -> aux rmap x
                Reg _ _ x -> aux rmap x
            ret = case signal s of
                Comb g l -> map (sig_comb 0 g) $ V.transposeVL $ V.map (rmap2 `mGet`) l
                Sample' _ x -> repeat x
                Sample k x -> concatMap (replicate k) (rmap2 `mGet` x)
                Reg i k x -> i : lastN k (rmap2 `mGet` x)
        in ret

    limit :: forall a' b'. [a'] -> [b'] -> [b']
    limit [] _ = []
    limit (_:ta) (hb:tb) = hb : limit ta tb
    limit _ _ = error "bad size"


unroll :: forall n a b. (KnownPos n, UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> (Vec n a -> Vec n b)
unroll f inp = V.map pack $ V.transposeLV $ map (V.fromList . (rmapFinal `mGet`)) (unpack out)
  where
    symb :: a = sigwise0 (valueOf @(ClockOf a)) (gate "symb") ()
    out = f symb
    rmapInit = IntMap.fromList $ map (uniqVal . uniq) (unpack symb) `zip` transpose (map unpack (V.toList inp))
    rmapFinal = foldl (aux (valueOf @(ClockOf a)) (valueOf @n)) rmapInit (unpack out)
    
    aux :: Int -> Int -> IntMap [Signal] -> Signal -> IntMap [Signal]
    aux clk len = memo \rmap s -> let
            rmap2 = case signal s of
                Comb _ l -> V.foldl (aux clk len) rmap l
                Sample' _ _ -> rmap
                Sample k x -> if (len `mod` k /= 0) then error ("cannot unroll with shifting phase "++show len++"/"++show k) else aux clk (len `div` k) rmap x
                Reg _ k x -> aux clk (len * k) rmap x
            ret = case signal s of
                Comb g l -> map (sig_comb clk g) $ V.transposeVL $ V.map (rmap2 `mGet`) l
                Sample' _ x -> replicate len (sig_sample' clk x)
                Sample k x -> concatMap (replicate k) (rmap2 `mGet` x)
                Reg i k x -> let prev = lastN k (rmap2 `mGet` x) in sig_delay i (last prev) : lazyList (len-1) (init prev)
        in ret
