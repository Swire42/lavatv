{-|
Module      : Lavatv.Batch
Description : Wrapper for values that can be manipulated as serial batches.
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Batch (
  Lavatv.Batch.Batch(unBatch),
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
import qualified Lavatv.HBool as HB
import qualified Lavatv.HVec as HV
import qualified Lavatv.HPair as HP
import qualified Lavatv.Vec as V

type HBool = HB.HBool
type HVec = HV.HVec
type HPair = HP.HPair

data Batch (n :: Nat) (h :: Nat -> Type) (clk :: Nat) = (1 <= n) => Batch { unBatch :: h clk }

wrap :: forall n h clk. (1 <= n) => h clk -> Batch n h clk
wrap ~x = Batch { unBatch=x }

lazyShape ~(Batch { unBatch=x }) = Batch { unBatch=x }
lazyUnwrap ~(Batch { unBatch=x }) = x

-- Identity
flatten :: forall n m h clk. (KnownNat n, KnownNat m, 1 <= n, 1 <= m, 1 <= n*m) => Batch n (Batch m h) clk -> Batch (n*m) h clk
flatten = wrap @(n*m) . unBatch . unBatch

-- Identity
unflatten :: forall n m h clk. (KnownNat n, KnownNat m, 1 <= n, 1 <= m) => Batch (n*m) h clk -> Batch n (Batch m h) clk
unflatten = wrap . wrap . unBatch

-- Pulse (1) every n fast ticks, with an offset of i.
pulse :: forall i n clk. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n, LiveClock clk) => Batch n (HBool) clk
pulse = Batch $ V.select @i @n x
  where x = V.zipWith ($) (delay @_ @clk HB.htrue `V.Cons` V.replicate (delay HB.hfalse)) (V.rotateR x)
--pulse = let ret = (\x -> L.iterate (delay hfalse) x !! (valueOf @i)) . (delay htrue) . (\x -> L.iterate (delay hfalse) x !! (valueOf @(n-(i+1)))) $ ret in wrap ret

-- Use the value of rare instead of base every n ticks, with an offset of i
pulseMux :: forall i n h clk. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n, Hard h, LiveClock clk) => Batch n h clk -> Batch n h clk -> Batch n h clk
pulseMux rare often = zipWithRaw (HB.ite') (pulse @i @n) (zip rare often)

-- Iterate through the values of a Vec over n base ticks
sweepMux :: forall n h clk. (KnownNat n, 1 <= n, Hard h, LiveClock clk) => HVec n h clk -> Batch n h clk
sweepMux v = Batch $ V.select @0 $ HV.unHVec $ unBatch shreg
  where
    shreg = shiftReset (Batch @n v) (lift (HV.HVec . V.rotateL . HV.unHVec) shreg) -- note: highly inneficient

-- Iterate through the values of a Vec in a single base tick
sweep :: forall n h clk. (KnownNat n, 1 <= n, Hard h, LiveClock clk, 1 <= (n * clk)) => HVec n h clk -> Batch n h (n*clk)
sweep = sweepMux . sample

-- Iterate through the values of a Vec in a single base tick
collect :: forall n h clk. (KnownNat n, 1 <= n, Hard h, LiveClock clk, 1 <= (n * clk)) => HVec n h 0 -> Batch n h (n*clk) -> HVec n h clk
collect ini b = reg @_ @n @clk ini $ HV.HVec $ V.reverse $ V.map unBatch $ V.iterate @n (shift (dontCare () :: h 0)) b

-- Apply f every n fast ticks, with an offset of i
update :: forall i n h clk. (KnownNat i, KnownNat n, (i+1) <= n, 1 <= n, Hard h, LiveClock clk) => (h clk -> h clk) -> Batch n h clk -> Batch n h clk
update f base = pulseMux @i @n (lift f base) base

-- Wiring
zip :: forall n a b clk. (KnownNat n, 1 <= n) => Batch n a clk -> Batch n b clk -> Batch n (HPair a b) clk
zip x y = wrap $ HP.HPair (unBatch x, unBatch y)

-- Wiring
unzip :: forall n a b clk. (KnownNat n, 1 <= n) => Batch n (HPair a b) clk -> (Batch n a clk, Batch n b clk)
unzip = (wrap *** wrap) . HP.unHPair . unBatch

-- Apply slowed-down circuit
map :: forall n a b clk. (KnownNat n, 1 <= n) => (a clk -> b clk) -> Batch n a clk -> Batch n b clk
map = undefined--slowdown

-- Apply circuit without slowing it down
lift :: forall n a b clk. (KnownNat n, 1 <= n) => (a clk -> b clk) -> Batch n a clk -> Batch n b clk
lift f = wrap . f . unBatch

-- Merge using slowed-down circuit
zipWith :: (KnownNat n, 1 <= n) => (a clk -> b clk -> c clk) -> Batch n a clk -> Batch n b clk -> Batch n c clk
zipWith f xs ys = map (HP.huncurry f) $ zip xs ys

-- Merge using circuit without slowing it down
zipWithRaw :: (KnownNat n, 1 <= n) => (a clk -> b clk -> c clk) -> Batch n a clk -> Batch n b clk -> Batch n c clk
zipWithRaw f xs ys = lift (HP.huncurry f) $ zip xs ys

-- Short delay, "shifting" values one tick toward the future,
-- with a constant value for the first ever tick
shift :: forall n a clk. (KnownNat n, 1 <= n, Hard a, LiveClock clk) => a 0 -> Batch n a clk -> Batch n a clk
shift ini x = wrap $ delay ini $ lazyUnwrap x

-- Short delay, "shifting" values one tick toward the future,
-- resetting to a dynamic value every n ticks.
-- ini[i] is used iff i%n == 0
-- Tip: ini can typically be `replicate cst`
shiftReset :: forall n a clk. (KnownNat n, 1 <= n, Hard a, LiveClock clk) => Batch n a clk -> Batch n a clk -> Batch n a clk
shiftReset ini x = pulseMux @0 ini $ shift (dontCare ()) x

-- Composed short delays, "shifting" values one whole base tick toward the future
fullDelay :: forall n a clk. (KnownNat n, 1 <= n, Hard a, LiveClock clk) => a 0 -> Batch n a clk -> Batch n a clk
fullDelay ini x = Prelude.iterate (shift @n ini) x !! (valueOf @n)

-- Compute iterations of a circuit without slowing it down
-- Output: [fst (ini `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ...]
scan :: forall n a b c clk. (KnownNat n, 1 <= n, Hard a, Hard b, Hard c, LiveClock clk) => (b clk -> a clk -> (b clk, c clk)) -> b 0 -> Batch n a clk -> Batch n c clk
scan f ini x = let (state, ret) = unzip $ zipWithRaw (\u v -> HP.HPair $ f u v) (shift ini state) x in ret

-- Compute iterations of a circuit without slowing it down,
-- Resetting loopback every n fast ticks
-- ini[i] is used iff i%n == 0
-- Output: [fst (ini[0] `f` x[0]), fst((snd (ini `f` x[0])) `f` x[1]), ..., fst (ini[n] `f` x[n]), ...]
scanReset :: forall n a b c clk. (KnownNat n, 1 <= n, Hard a, Hard b, Hard c, LiveClock clk) => (b clk -> a clk -> (b clk, c clk)) -> Batch n b clk -> Batch n a clk -> Batch n c clk
scanReset f ini x = let (state, ret) = unzip $ zipWithRaw (\u v -> HP.HPair $ f u v) (shiftReset ini state) x in ret
