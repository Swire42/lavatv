{-|
Module      : Lavatv.Batch
Description : Wrapper for values that can be manipulated as serial batches.
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Batch (
  Lavatv.Batch.Batch(..),
  Lavatv.Batch.wrap,
  Lavatv.Batch.lazyUnwrap,

  Lavatv.Batch.flatten,
  Lavatv.Batch.unflatten,
  Lavatv.Batch.pulse,
  Lavatv.Batch.pulseMux,
  Lavatv.Batch.sweepMux,
  Lavatv.Batch.sweep,
  Lavatv.Batch.collect,
  Lavatv.Batch.update,
  Lavatv.Batch.zip,
  Lavatv.Batch.unzip,
  Lavatv.Batch.map,
  Lavatv.Batch.lift,
  Lavatv.Batch.zipWith,
  Lavatv.Batch.shift,
  Lavatv.Batch.shiftReset,
  Lavatv.Batch.fullDelay,
  Lavatv.Batch.scan,
  Lavatv.Batch.scanReset,
) where

import Prelude hiding (replicate, map, zip, unzip, zipWith)
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

wrap :: forall n h. (1 <= n) => h -> Batch n h
wrap ~x = Batch { unBatch=x }

lazyShape ~(Batch { unBatch=x }) = Batch { unBatch=x }
lazyUnwrap ~(Batch { unBatch=x }) = x

-- Identity
flatten :: forall n m h. (KnownPos n, KnownPos m, 1 <= n*m) => Batch n (Batch m h) -> Batch (n*m) h
flatten = wrap @(n*m) . unBatch . unBatch

-- Identity
unflatten :: forall n m h. (KnownPos n, KnownPos m) => Batch (n*m) h -> Batch n (Batch m h)
unflatten = wrap . wrap . unBatch

-- Pulse (1) every n fast ticks, with an offset of i.
pulse :: forall i n clk. (KnownNat i, KnownPos n, (i+1) <= n, KnownPos clk) => Batch n (HBool clk)
pulse = Batch $ V.select @i @n x
  where x = V.zipWith ($) (delay HB.htrue `V.Cons` V.replicate (delay HB.hfalse)) (V.rotateR x)

-- Use the value of rare instead of base every n ticks, with an offset of i
pulseMux :: forall i n h. (KnownNat i, KnownPos n, (i+1) <= n, UHard h, KnownPos (ClockOf h)) => Batch n h -> Batch n h -> Batch n h
pulseMux rare often = zipWithRaw (HB.hite) (pulse @i @n) (zip rare often)

-- Iterate through the values of a Vec over n base ticks
sweepMux :: forall n h. (KnownPos n, UHard h, UHard (ReClock h 0), KnownNat (ClockOf (ReClock h 0)), KnownPos (ClockOf h)) => Vec n h -> Batch n h
sweepMux v = Batch $ V.select @0 $ unBatch shreg
  where
    shreg = shiftReset (Batch @n v) (lift V.rotateL shreg) -- note: inneficient

-- Iterate through the values of a Vec in a single base tick
sweep :: forall n h. (KnownPos n, UHard h, UHard (SpedUp h n), UHard (ReClock (SpedUp h n) 0), KnownNat (ClockOf (ReClock (SpedUp h n) 0)), KnownPos (ClockOf h), KnownPos (ClockOf (SpedUp h n))) => Vec n h -> Batch n (SpedUp h n)
sweep = sweepMux . upsample @(Vec n h) @n

-- Iterate through the values of a Vec in a single base tick
collect :: forall n h. (KnownPos n, UHard h, UHard (SpedUp h n), UHard (ReClock h 0), KnownPos (ClockOf h), KnownPos (ClockOf (SpedUp h n)), ReClock (SpedUp h n) 0 ~ ReClock h 0, ClockOf (ReClock h 0) ~ 0) => Vec n (ReClock h 0) -> Batch n (SpedUp h n) -> Vec n h
collect ini b = reg ini $ V.reverse $ V.map unBatch $ V.iterate @n (shift (dontCare () :: ReClock h 0)) b

-- Apply f every n fast ticks, with an offset of i
update :: forall i n h. (KnownNat i, KnownPos n, (i+1) <= n, UHard h, KnownPos (ClockOf h)) => (h -> h) -> Batch n h -> Batch n h
update f base = pulseMux @i @n (lift f base) base

-- Wiring
zip :: forall n a b. (KnownPos n, UHard a, UHard b, ClockOf a ~ ClockOf b) => Batch n a -> Batch n b -> Batch n (a, b)
zip x y = wrap $ (unBatch x, unBatch y)

-- Wiring
unzip :: forall n a b. KnownPos n => Batch n (a, b) -> (Batch n a, Batch n b)
unzip = (wrap *** wrap) . unBatch

-- Apply slowed-down circuit
map :: forall n a b. (KnownPos n, UHard a, UHard b, KnownPos (ClockOf a), ClockOf a ~ ClockOf b) => (a -> b) -> Batch n a -> Batch n b
map f x = Batch $ slowdown (valueOf @n) f $ unBatch x

-- Apply circuit without slowing it down
lift :: forall n a b. KnownPos n => (a -> b) -> Batch n a -> Batch n b
lift f = wrap . f . unBatch

-- Merge using slowed-down circuit
zipWith :: (KnownPos n, UHard a, UHard b, UHard c, KnownPos (ClockOf a), ClockOf a ~ ClockOf b, ClockOf a ~ ClockOf c) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

-- Merge using circuit without slowing it down
zipWithRaw :: (KnownPos n, UHard a, UHard b, UHard c) => (a -> b -> c) -> Batch n a -> Batch n b -> Batch n c
zipWithRaw f xs ys = lift (uncurry f) $ zip xs ys

-- Short delay, "shifting" values one tick toward the future,
-- with a constant value for the first ever tick
shift :: forall n a. (KnownPos n, UHard a, UHard (ReClock a 0), KnownPos (ClockOf a)) => ReClock a 0 -> Batch n a -> Batch n a
shift ini x = wrap $ delay ini $ lazyUnwrap x

-- Short delay, "shifting" values one tick toward the future,
-- resetting to a dynamic value every n ticks.
-- ini[i] is used iff i%n == 0
-- Tip: ini can typically be `replicate cst`
shiftReset :: forall n a. (KnownPos n, UHard a, UHard (ReClock a 0), KnownPos (ClockOf a), KnownNat (ClockOf (ReClock a 0))) => Batch n a -> Batch n a -> Batch n a
shiftReset ini x = pulseMux @0 ini $ shift (dontCare ()) x

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a. (KnownPos n, UHard a, UHard (ReClock a 0), KnownPos (ClockOf a)) => ReClock a 0 -> Batch n a -> Batch n a
fullDelay ini x = Prelude.iterate (shift @n ini) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [fst (ini `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ...]
scan :: forall n a b c. (KnownPos n, UHard a, UHard b, UHard (ReClock b 0), UHard c, KnownPos (ClockOf c)) => (b -> a -> (b, c)) -> ReClock b 0 -> Batch n a -> Batch n c
scan f ini x = let (state, ret) = unzip $ zipWithRaw f (shift ini state) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- ini[i] is used iff i%n == 0
-- Output: [fst (ini[0] `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ..., fst (ini[n] `f` x[n]), ...]
scanReset :: forall n a b c. (KnownPos n, UHard a, UHard b, UHard (ReClock b 0), KnownNat (ClockOf (ReClock b 0)), UHard c, KnownPos (ClockOf c)) => (b -> a -> (b, c)) -> Batch n b -> Batch n a -> Batch n c
scanReset f ini x = let (state, ret) = unzip $ zipWithRaw f (shiftReset ini state) x in ret
