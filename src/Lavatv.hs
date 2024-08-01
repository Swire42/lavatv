module Lavatv where

import Prelude

import Lavatv.Nat
import qualified Lavatv.Vec as V
import qualified Lavatv.Batch as B

import Lavatv.Core
import Lavatv.HBool
import Lavatv.BV
import Lavatv.Sim

type Vec = V.Vec

s0 :: Signal
s0 = comb 0 gate V.Nil

s1 :: Signal
s1 = sample' 1 s0

s6 :: Signal
s6 = sample 6 s1

s3 :: Signal
s3 = reg_ s0 2 s6

s42 :: Signal -> Signal
s42 x = sample 2 x

s2 :: Signal -> Signal
s2 x = sample 2 x



halfadd (a :: Bit _, b :: Bit _) = (s :: Bit _, c :: Bit _)
  where
    s = a `bvxor` b
    c = a `bvand` b

fulladd (a :: Bit _, b :: Bit _, ci :: Bit _) = (s :: Bit _, co :: Bit _)
  where
    (t, c1) = halfadd (a, b)
    (s, c2) = halfadd (ci, t)
    co = c1 `bvor` c2

mux (sel :: Bit _) (x0 :: Bit _, x1 :: Bit _) = (x :: Bit _)
  where
    x = (x0 `bvand` bvnot sel) `bvor` (x1 `bvand` sel)

tmap2 (f :: forall a. Bit a -> Bit a) (x :: Bit clk, y :: Bit clk) = (fx :: Bit clk, fy :: Bit clk)
  where
    sx :: Bit (2*clk) = upsample x
    sy :: Bit (2*clk) = upsample y
    z = ite (pulse ()) (sx, sy)
    fz = f z
    fx = reg zeros $ delay zeros fz
    fy = reg zeros fz

tmap2b (f :: forall a. Bit a -> Bit a) (xs :: Vec 2 (Bit clk)) = (fxs :: Vec 2 (Bit clk))
  where
    fxs = B.collect (V.replicate zeros) $ B.lift f $ B.sweep xs

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
