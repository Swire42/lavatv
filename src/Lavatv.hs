module Lavatv where

import Prelude

import Lavatv.Nat
import qualified Lavatv.Vec as V
import qualified Lavatv.Batch as B

import Lavatv.Core
import Lavatv.HBool
import Lavatv.BV
import Lavatv.Sim
import Lavatv.Verif

type Vec = V.Vec

halfadd (a :: Bit _, b :: Bit _) = (s :: Bit _, c :: Bit _)
  where
    s = a `bvXor` b
    c = a `bvAnd` b

fulladd (a :: Bit _, b :: Bit _, ci :: Bit _) = (s :: Bit _, co :: Bit _)
  where
    (t, c1) = halfadd (a, b)
    (s, c2) = halfadd (ci, t)
    co = c1 `bvOr` c2

serialAdd (a :: Bit _, b :: Bit _) = (s :: Bit _)
  where
    (s, c) = fulladd (a, b, delay bvZeros c)

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
