module Lavatv where

import Prelude

import Lavatv.Nat
import Lavatv.Vec(Vec)
import qualified Lavatv.Vec as V
import Lavatv.Batch(Batch)
import qualified Lavatv.Batch as B
import Control.Arrow((***))

import Lavatv.Core
import Lavatv.HBool
import Lavatv.HInteger
import Lavatv.BV
import Lavatv.Sim
import Lavatv.Verif

halfAdder :: forall clk. _ => Bit clk -> Bit clk -> (Bit clk, Bit clk)
halfAdder a b = (s, c)
  where
    s = a `bvXor` b
    c = a `bvAnd` b

fullAdder :: forall clk. _ => Bit clk -> Bit clk -> Bit clk -> (Bit clk, Bit clk)
fullAdder a b ci = (s, co)
  where
    (t, c1) = halfAdder a b
    (s, c2) = halfAdder ci t
    co = c1 `bvOr` c2

seqAdder :: forall clk. _ => Bit clk -> Bit clk -> Bit clk
seqAdder a b = s
  where
    (s, c) = fullAdder a b (delay bvZeros c)

-- MSB is the closest to Nil (/= BV)
rippleAdder :: forall clk n. _ => Vec n (Bit clk) -> Vec n (Bit clk) -> Vec (n+1) (Bit clk)
rippleAdder a b = s
  where
    sc = V.zipWith (\c' (a', b') -> fullAdder a' b' c') (bvZeros `V.Cons` V.init c) (V.zip a b)
    c = V.map snd sc
    s = V.map fst sc `V.append` V.singleton (V.last c)

batchAdder :: forall clk n. _ => Batch n (Bit clk) -> Batch n (Bit clk) -> Batch n (Bit clk)
batchAdder a b = s
  where
    s = B.scan' kernel (B.Batch bvZeros) (B.zip a b)
    kernel ci (a', b') = let (s', co) = fullAdder a' b' ci in (co, s')

mux (sel :: Bit _) (x0 :: Bit _, x1 :: Bit _) = (x :: Bit _)
  where
    x = (x0 `bvAnd` bvNot sel) `bvOr` (x1 `bvAnd` sel)

tmap2 (f :: forall a. Bit a -> Bit a) (x :: Bit clk, y :: Bit clk) = (fx :: Bit clk, fy :: Bit clk)
  where
    sx :: Bit (2*clk) = upsample x
    sy :: Bit (2*clk) = upsample y
    z = hite (pulse ()) (sx, sy)
    fz = f z
    fx = reg bvZeros $ delay bvZeros fz
    fy = reg bvZeros fz

tmap2b (f :: forall a. Bit a -> Bit a) (xs :: Vec 2 (Bit clk)) = (fxs :: Vec 2 (Bit clk))
  where
    fxs = B.collect (V.replicate bvZeros) $ B.map f $ B.sweep xs

sim0 :: forall clk. (KnownPos clk) => Sim Int clk -> Sim Int clk
sim0 _ = cstsample $ simLift0 42

sim1 :: forall clk. (KnownPos clk) => Sim Int clk -> Sim Int clk
sim1 y = x
  where
    x :: Sim Int clk = (simLift2 (+)) (delay (simLift0 0) x) y

sim3 :: forall clk. (KnownPos clk) => Sim Int clk -> Sim Int clk
sim3 y = reg @_ @3 (simLift0 0) x
  where
    x :: Sim Int (3*clk) = (simLift2 (+)) (delay (simLift0 0) x) (upsample @_ @3 y)

integ :: forall clk. KnownPos clk => HInteger clk -> HInteger clk
integ i = o
  where o = hadd i $ delay (hinteger 0) o

integ_space :: Vec 2 (HInteger 1) -> Vec 2 (HInteger 1)
integ_space = V.map integ

integ_time :: Vec 2 (HInteger 1) -> Vec 2 (HInteger 1)
integ_time = B.collect (V.replicate $ hinteger 0) . B.map integ . B.sweep


cvcell :: forall clk. KnownNat clk => (HInteger clk, HInteger clk) -> HInteger clk -> (HInteger clk, HInteger clk)
cvcell (x, acc) w = (x, (x `hmul` w) `hadd` acc)

cv1cell :: forall clk. KnownPos clk => (HInteger clk, HInteger clk) -> HInteger clk -> (HInteger clk, HInteger clk)
cv1cell (x, acc) w = (delay (hinteger 0) *** id) $ cvcell (x, acc) w

cv1 :: forall n. KnownPos n => HInteger 1 -> Vec n (HInteger 1) -> HInteger 1
cv1 xs ws = snd $ V.foldl cv1cell (xs, hinteger 0) ws

cv2 :: forall m k. (KnownPos m, KnownPos k) => HInteger 1 -> Vec (m*k) (HInteger 1) -> HInteger 1
cv2 xs ws = snd $ B.fold (V.foldl cv1cell) (dontcare ()) (xs, hinteger 0) (B.sweep @m $ V.unconcat ws)
