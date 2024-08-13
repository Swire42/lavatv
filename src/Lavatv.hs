module Lavatv where

import Prelude

import Lavatv.Nat
import Lavatv.Vec(Vec)
import qualified Lavatv.Vec as V
import Lavatv.Batch(Batch)
import qualified Lavatv.Batch as B

import Lavatv.Core
import Lavatv.HBool
import Lavatv.BV
import Lavatv.Sim
import Lavatv.Verif

halfAdder (a :: Bit _, b :: Bit _) = (s :: Bit _, c :: Bit _)
  where
    s = a `bvXor` b
    c = a `bvAnd` b

fullAdder (a :: Bit _, b :: Bit _, ci :: Bit _) = (s :: Bit _, co :: Bit _)
  where
    (t, c1) = halfAdder (a, b)
    (s, c2) = halfAdder (ci, t)
    co = c1 `bvOr` c2

seqAdder (a :: Bit _, b :: Bit _) = (s :: Bit _)
  where
    (s, c) = fullAdder (a, b, delay bvZeros c)

rippleAdder (a :: Vec n (Bit _)) (b :: Vec n (Bit _)) = (s :: Vec (n+1) (Bit _))
  where
    sc = V.zipWith (\c' (a', b') -> fullAdder (a', b', c')) (bvZeros `V.Cons` V.init c) (V.zip a b)
    c = V.map snd sc
    s = V.map fst sc `V.append` V.singleton (V.last c)

batchAdder (a :: Batch n (Bit _)) (b :: Batch n (Bit _)) = (s :: Batch n (Bit _))
  where
    s = B.scanReset kernel (B.Batch bvZeros) (B.zip a b)
    kernel ci (a', b') = let (s', co) = fullAdder (a', b', ci) in (co, s')

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
    fxs = B.collect (V.replicate bvZeros) $ B.lift f $ B.sweep xs

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
