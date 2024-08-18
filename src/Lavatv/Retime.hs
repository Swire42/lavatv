{-|
Module      : Lavatv.Retime
Description : Time transformations
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Retime (
  Lavatv.Retime.dynUnroll
, Lavatv.Retime.unroll
, Lavatv.Retime.unroll1
, Lavatv.Retime.slowdown
) where

import Prelude
import Data.List

import Lavatv.Nat
import Lavatv.Core
import qualified Lavatv.Vec as V

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap

type Vec = V.Vec

memo :: (IntMap a -> Signal -> a) -> IntMap a -> Signal -> IntMap a
memo f rmap s = if IntMap.member (sigId s) rmap then rmap else
    let ret = IntMap.insert (sigId s) (f ret s) rmap in ret

mGet :: IntMap a -> Signal -> a
mGet rmap s = rmap IntMap.! (sigId s)

everyN :: forall a'. Int -> [a'] -> [a']
everyN _ [] = []
everyN n (h:t) = h : (everyN n $ drop (n-1) t)

lastN :: forall a'. Int -> [a'] -> [a']
lastN n = everyN n . drop (n-1)

lazyList :: Int -> [a] -> [a]
lazyList 0 _       = []
lazyList n l = head l : lazyList (n-1) (tail l)

dynUnroll :: forall a b. (UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> [ReClock a 0] -> [ReClock b 0]
dynUnroll f inp = limit inp $ map pack $ transpose $ map (rmapFinal `mGet`) (unpack out)
  where
    symb = symbolic "dynUnroll"
    out = f symb
    rmapInit = IntMap.fromList $ map sigId (unpack symb) `zip` transpose (map unpack inp)
    rmapFinal = foldl aux rmapInit (unpack out)

    aux :: IntMap [Signal] -> Signal -> IntMap [Signal]
    aux = memo \rmap s -> let
            rmap2 = case sigDef s of
                Comb (GateOp _ l) -> V.foldl aux rmap l
                Comb DontCare -> rmap
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ _ -> rmap
                UpSample _ x -> aux rmap x
                Reg _ _ x -> aux rmap x
            ret = case sigDef s of
                Comb (GateOp g l) -> map (sig_comb ((sigInfo s) { sigClock=0 }) g) $ V.transposeVL $ V.map (rmap2 `mGet`) l
                Comb DontCare -> map (\() -> sig_dontcare ((sigInfo s) { sigClock=0 })) $ repeat ()
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ x -> repeat x
                UpSample k x -> concatMap (replicate k) (rmap2 `mGet` x)
                Reg i k x -> i : lastN k (rmap2 `mGet` x)
        in ret

    limit :: forall a' b'. [a'] -> [b'] -> [b']
    limit [] _ = []
    limit (_:ta) (hb:tb) = hb : limit ta tb
    limit _ _ = error "bad size"

unroll :: forall n a b. (KnownPos n, UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> (Vec n a -> Vec n b)
unroll f inp = V.map pack $ V.transposeLV $ map (V.fromList . (rmapFinal `mGet`)) (unpack out)
  where
    symb = symbolic "unroll"
    out = f symb
    rmapInit = IntMap.fromList $ map sigId (unpack symb) `zip` transpose (map unpack (V.toList inp))
    rmapFinal = foldl (aux (valueOf @(ClockOf a)) (valueOf @n)) rmapInit (unpack out)

    aux :: Int -> Int -> IntMap [Signal] -> Signal -> IntMap [Signal]
    aux clk len = memo \rmap s -> let
            rmap2 = case sigDef s of
                Comb (GateOp _ l) -> V.foldl (aux clk len) rmap l
                Comb DontCare -> rmap
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ _ -> rmap
                UpSample k x -> if (len `mod` k /= 0) then error ("cannot unroll with shifting phase ("++show len++"/"++show k++")") else aux clk (len `div` k) rmap x
                Reg _ k x -> aux clk (len * k) rmap x
            ret = case sigDef s of
                Comb (GateOp g l) -> map (sig_comb ((sigInfo s) { sigClock=clk }) g) $ V.transposeVL $ V.map (rmap2 `mGet`) l
                Comb DontCare -> map (\() -> sig_dontcare ((sigInfo s) { sigClock=clk })) $ replicate len ()
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ x -> replicate len (sig_cstsample clk x)
                UpSample k x -> concatMap (replicate k) (rmap2 `mGet` x)
                Reg i k x -> let prev = lastN k (rmap2 `mGet` x) in sig_delay clk i (last prev) : lazyList (len-1) (init prev)
        in ret

unroll1 :: forall a b. (UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> (a -> b)
unroll1 f = V.destruct1 . unroll f . V.construct1

slowdown :: forall a b. (UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => Int -> (a -> b) -> (a -> b)
slowdown count f inp = pack $ map (rmapFinal `mGet`) (unpack out)
  where
    clk = valueOf @(ClockOf a)
    symb = symbolic "slowdown"
    out = f symb
    rmapInit = IntMap.fromList $ map sigId (unpack symb) `zip` unpack inp
    rmapFinal = foldl aux rmapInit (unpack out)

    aux :: IntMap Signal -> Signal -> IntMap Signal
    aux = memo \rmap s -> let
            rmap2 = case sigDef s of
                Comb (GateOp _ l) -> V.foldl aux rmap l
                Comb DontCare -> rmap
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ _ -> rmap
                UpSample 1 x -> aux rmap x
                UpSample _ _ -> error "slowdown requires a unique clock"
                Reg _ 1 x -> aux rmap x
                Reg _ _ _ -> error "slowdown requires a unique clock"
            ret = case sigDef s of
                Comb (GateOp g l) -> sig_comb ((sigInfo s) { sigClock=clk }) g $ V.map (rmap2 `mGet`) l
                Comb DontCare -> s
                Comb (Symbolic _) -> error "unreachable"
                CstSample _ _ -> s
                UpSample 1 x -> rmap2 `mGet` x
                UpSample _ _ -> error "slowdown requires a unique clock"
                Reg i 1 x -> iterate (\nxt -> sig_delay clk i nxt) (rmap2 `mGet` x) !! count
                Reg _ _ _ -> error "slowdown requires a unique clock"
        in ret
