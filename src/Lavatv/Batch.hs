{-|
Module      : Lavatv.Batch
Description : Wrapper for values that can be manipulated as serial batches.
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Batch (
  Lavatv.Batch.Batch(..)
, Lavatv.Batch.unBatchLazy

, Lavatv.Batch.flatten
, Lavatv.Batch.unflatten
, Lavatv.Batch.pulse
, Lavatv.Batch.pulseMux
, Lavatv.Batch.sweepMux
, Lavatv.Batch.sweep
, Lavatv.Batch.collect
, Lavatv.Batch.updateRaw
, Lavatv.Batch.zip
, Lavatv.Batch.unzip
, Lavatv.Batch.mapRaw
, Lavatv.Batch.map
, Lavatv.Batch.zipWithRaw
, Lavatv.Batch.zipWith
, Lavatv.Batch.shiftRaw
, Lavatv.Batch.shift'
, Lavatv.Batch.shift
, Lavatv.Batch.fullDelay
, Lavatv.Batch.scanRaw
, Lavatv.Batch.scan'
, Lavatv.Batch.scan
, Lavatv.Batch.row
, Lavatv.Batch.fold
) where

import Prelude hiding (replicate, repeat, map, zip, unzip, zipWith, last)
import Control.Arrow ((***))
import Data.Kind

import Lavatv.Nat

import Lavatv.Core
import Lavatv.Retime
import qualified Lavatv.HBool as HB
import qualified Lavatv.Vec as V

type HBool = HB.HBool
type Vec = V.Vec

data Batch (n :: Nat) (h :: Type) = (1 <= n) => Batch { unBatch :: h }

type TVec n h = Batch n (SpedUp n h)

lazyShape ~(Batch { unBatch=x }) = Batch { unBatch=x }
unBatchLazy ~(Batch { unBatch=x }) = x

-- Identity
flatten :: forall n m h. (KnownPos n, KnownPos m, 1 <= n*m) => Batch n (Batch m h) -> Batch (n*m) h
flatten = Batch @(n*m) . unBatch . unBatch

-- Identity
unflatten :: forall n m h. (KnownPos n, KnownPos m) => Batch (n*m) h -> Batch n (Batch m h)
unflatten = Batch . Batch . unBatch

-- Pulse (1) every n fast ticks, with an offset of i.
pulse :: forall i n clk. (KnownNat i, KnownPos n, (i+1) <= n, KnownPos clk) => Batch n (HBool clk)
pulse = Batch $ V.select @i @n x
  where x = V.zipWith ($) (delay HB.htrue `V.Cons` V.replicate (delay HB.hfalse)) (V.rotateR x)

-- Use the value of rare instead of base every n ticks, with an offset of i
pulseMux :: forall i n h. (KnownNat i, KnownPos n, (i+1) <= n, UHard h, KnownPos (ClockOf h)) => Batch n h -> Batch n h -> Batch n h
pulseMux rare often = zipWithRaw (HB.hite) (pulse @i @n) (zip rare often)

-- Iterate through the values of a Vec over n base ticks
sweepMux :: forall n h. (KnownPos n, UHard h, KnownPos (ClockOf h)) => Vec n h -> Batch n h
sweepMux v = Batch $ V.foldr (\(active, x) next -> HB.hite active (x, next)) (dontcare ()) (hot `V.zip` v)
  where
    hot = V.zipWith ($) (delay HB.htrue `V.Cons` V.replicate (delay HB.hfalse)) (V.rotateR hot)

repeat :: forall n h. (KnownPos n, UHard h, UHard (SpedUp n h), KnownPos (ClockOf h), KnownPos (ClockOf (SpedUp n h))) => h -> TVec n h
repeat = Batch . upsample

-- Iterate through the values of a Vec in a single base tick
sweep :: forall n h. (KnownPos n, UHard h, UHard (SpedUp n h), KnownPos (ClockOf h), KnownPos (ClockOf (SpedUp n h))) => Vec n h -> TVec n h
sweep = sweepMux . upsample @(Vec n h) @n

-- Collect the values into a Vec, with a the result available once the base clock ticks
collect :: forall n h. (KnownPos n, UHard h, UHard (SpedUp n h), KnownPos (ClockOf h), KnownPos (ClockOf (SpedUp n h)), ReClock (SpedUp n h) 0 ~ ReClock h 0) => Vec n (ReClock h 0) -> Batch n (SpedUp n h) -> Vec n h
collect ini b = reg ini $ V.reverse $ V.map unBatch $ V.iterate @n (shiftRaw (dontcare () :: ReClock h 0)) b

-- Get the last value of the previous batch on every base clock tick
last :: forall n h. _ => ReClock h 0 -> TVec n h -> h
last ini tv = V.last $ collect (V.append (V.map dontcare (V.replicate @(n-1) ())) (V.singleton ini)) tv

-- Apply f every n fast ticks, with an offset of i
updateRaw :: forall i n h. (KnownNat i, KnownPos n, (i+1) <= n, UHard h, KnownPos (ClockOf h)) => (h -> h) -> Batch n h -> Batch n h
updateRaw f base = pulseMux @i @n (mapRaw f base) base

-- Wiring
zip :: forall n a b. (KnownPos n, UHard a, UHard b, ClockOf a ~ ClockOf b) => Batch n a -> Batch n b -> Batch n (a, b)
zip x y = Batch $ (unBatch x, unBatch y)

-- Wiring
unzip :: forall n a b. KnownPos n => Batch n (a, b) -> (Batch n a, Batch n b)
unzip = (Batch *** Batch) . unBatchLazy

-- Apply circuit without slowing it down
mapRaw :: forall n a b. KnownPos n => (a -> b) -> Batch n a -> Batch n b
mapRaw f = Batch . f . unBatchLazy

-- Apply slowed-down circuit
map :: forall n a b. (KnownPos n, UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> Batch n a -> Batch n b
map f x = Batch $ slowdown (valueOf @n) f $ unBatchLazy x

-- Merge using slowed-down circuit
zipWith :: (KnownPos n, UHard a, UHard b, UHard c, KnownPos (ClockOf a), ClockOf a ~ ClockOf b, ClockOf a ~ ClockOf c) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- Merge using circuit without slowing it down
zipWithRaw :: (KnownPos n, UHard a, UHard b, UHard c) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWithRaw f xs ys = mapRaw (uncurry f) $ zip xs ys

-- Short delay, "shifting" values one tick toward the future,
-- with a constant value for the first ever tick
shiftRaw :: forall n a. (KnownPos n, UHard a, KnownPos (ClockOf a)) => ReClock a 0 -> Batch n a -> Batch n a
shiftRaw ini = mapRaw $ delay ini

-- Short delay, "shifting" values one tick toward the future,
-- resetting to a dynamic value every n ticks.
-- ini[i] is used iff i%n == 0
-- Tip: ini can typically be `replicate cst`
shift' :: forall n a. (KnownPos n, UHard a, KnownPos (ClockOf a)) => Batch n a -> Batch n a -> Batch n a
shift' ini x = pulseMux @0 ini $ shiftRaw (dontcare ()) x

shift :: forall n a. _ => a -> TVec n a -> TVec n a
shift ini x = shift' (repeat ini) x

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a. (KnownPos n, UHard a, KnownPos (ClockOf a)) => ReClock a 0 -> Batch n a -> Batch n a
fullDelay ini x = Prelude.iterate (shiftRaw @n ini) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [fst (ini `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ...]
scanRaw :: forall n a b c. (KnownPos n, UHard a, UHard b, UHard c, KnownPos (ClockOf c)) => (b -> a -> (b, c)) -> ReClock b 0 -> Batch n a -> Batch n c
scanRaw f ini x = let (state, ret) = unzip $ zipWithRaw f (shiftRaw ini state) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- ini[i] is used iff i%n == 0
-- Output: [fst (ini[0] `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ..., fst (ini[n] `f` x[n]), ...]
scan' :: forall n a b c. _ => (b -> a -> (c, b)) -> Batch n b -> Batch n a -> Batch n c
scan' f e x = let (ret, acc) = unzip $ zipWith f (shift' e acc) x in ret

scan :: forall n a b c. _ => (SpedUp n b -> a -> (c, SpedUp n b)) -> b -> Batch n a -> TVec n c
scan f e x = let (ret, acc) = unzip $ zipWith f (shift e acc) x in ret

row :: forall n a b c. _ => (SpedUp n b -> a -> (c, SpedUp n b)) -> ReClock b 0 -> b -> Batch n a -> (TVec n c, b)
row f ini e x = let (ret, acc) = unzip $ zipWith f (shift e acc) x in (ret, last ini acc)

fold :: forall n a b. _ => (SpedUp n b -> a -> SpedUp n b) -> ReClock b 0 -> b -> Batch n a -> b
fold f ini e x = let acc = zipWith f (shift e acc) x in last ini acc
