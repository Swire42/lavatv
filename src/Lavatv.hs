module Lavatv where

import Prelude

import Lavatv.Nat
import qualified Lavatv.Vec as V
import qualified Lavatv.HVec as HV

import Lavatv.Core
import Lavatv.HBool
import Lavatv.BV
import Lavatv.Retime
import Lavatv.Sim

someFunc :: IO ()
someFunc = putStrLn "someFunc"

s0 :: Signal 0
s0 = comb gate V.Nil

s1 :: Signal 1
s1 = sample' s0

s6 :: Signal 6
s6 = sample s1

s3 :: Signal 3
s3 = reg s0 s6

s42 :: Signal 2 -> Signal 4
s42 x = sample x

s2 :: (KnownNat a, 1 <= a) => Signal a -> Signal (2*a)
s2 x = sample x



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
    sx :: Bit (2*clk) = sample x
    sy :: Bit (2*clk) = sample y
    z = ite (pulse ()) (sx, sy)
    fz = f z
    fx = reg zeros $ delay zeros fz
    fy = reg zeros fz

