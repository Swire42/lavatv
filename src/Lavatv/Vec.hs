{-|
Module      : Lavatv.Vec
Description : Sized lists
Copyright   : (c) Victor Miquel, 2024
License     : MIT

Lists with type-checked lengths
-}

module Lavatv.Vec (
  Lavatv.Vec.Vec(..),

  Lavatv.Vec.fromList,
  Lavatv.Vec.toList,

  Lavatv.Vec.lazyShape,
  Lavatv.Vec.forceCast,
  Lavatv.Vec.replicate,
  Lavatv.Vec.iterate,
  Lavatv.Vec.singleton,
  Lavatv.Vec.construct1,
  Lavatv.Vec.construct2,
  Lavatv.Vec.construct3,
  Lavatv.Vec.destruct1,
  Lavatv.Vec.destruct2,
  Lavatv.Vec.destruct3,
  Lavatv.Vec.append,
  Lavatv.Vec.concat,
  Lavatv.Vec.unconcat,
  Lavatv.Vec.select,
  Lavatv.Vec.split,
  Lavatv.Vec.update,
  Lavatv.Vec.head,
  Lavatv.Vec.last,
  Lavatv.Vec.tail,
  Lavatv.Vec.init,
  Lavatv.Vec.uncons,
  Lavatv.Vec.take,
  Lavatv.Vec.drop,
  Lavatv.Vec.rotateL,
  Lavatv.Vec.rotateR,
  Lavatv.Vec.reverse,
  Lavatv.Vec.zip,
  Lavatv.Vec.unzip,
  Lavatv.Vec.map,
  Lavatv.Vec.zipWith,
  Lavatv.Vec.foldr,
  Lavatv.Vec.foldl,
  Lavatv.Vec.foldr1,
  Lavatv.Vec.foldl1,
  Lavatv.Vec.scanr,
  Lavatv.Vec.scanl,
  Lavatv.Vec.transposeVV,
  Lavatv.Vec.transposeLV,
  Lavatv.Vec.transposeVL,
) where

import qualified Prelude
import Prelude (error, Maybe(..), ($), (.), (<*>), uncurry)
import qualified Data.List as L

import Lavatv.Nat

data Vec (n :: Nat) a where
  Nil :: (n ~ 0) => Vec n a
  Cons :: forall n a. (1 <= n) => a -> Vec (n-1) a -> Vec n a

assertEq :: forall a b v. (KnownNat a, KnownNat b) => (a ~ b => v) -> v
assertEq x = ifEq @a @b x (error "assert failed")

assertZero :: forall n v. KnownNat n => (n ~ 0 => v) -> v
assertZero = assertEq @n @0

fromList :: forall n a. KnownNat n => [a] -> Vec n a
fromList [] = ifZero @n Nil (error "list too small")
fromList (x:xs) = ifZero @n (error "list too large") (x `Cons` fromList @(n-1) xs)

toList :: forall n a. KnownNat n => Vec n a -> [a]
toList xs = ifZero @n [] (let y `Cons` ys = xs in y : toList @(n-1) ys)

instance (Prelude.Show [a], KnownNat n) => Prelude.Show (Vec n a) where
  show = Prelude.show . toList

instance KnownNat n => Prelude.Functor (Vec n) where
  fmap = map

instance KnownNat n => Prelude.Foldable (Vec n) where
  foldr = foldr

instance KnownNat n => Prelude.Traversable (Vec n) where
  traverse f xss = ifZero @n (Prelude.pure Nil) (let x `Cons` xs = xss in Prelude.pure Cons <*> f x <*> Prelude.traverse f xs)

lazyShape :: forall n a. KnownNat n => Vec n a -> Vec n a
lazyShape xss = ifZero @n Nil (let x `Cons` xs = xss in x `Cons` xs)

forceCast :: forall n m a. (KnownNat n, KnownNat m) => Vec m a -> Vec n a
forceCast xs = ifEq @n @m xs (error "sizes don't match")

replicate :: forall n a. KnownNat n => a -> Vec n a
replicate x = ifZero @n Nil (x `Cons` replicate @(n-1) x)

iterate :: forall n a. KnownNat n => (a -> a) -> a -> Vec n a
iterate f x = ifZero @n Nil (x `Cons` iterate @(n-1) f (f x))

singleton :: a -> Vec 1 a
singleton = construct1

construct1 :: a -> Vec 1 a
construct1 x0 = x0 `Cons` Nil

construct2 :: (a, a) -> Vec 2 a
construct2 (x0, x1) = x0 `Cons` (x1 `Cons` Nil)

construct3 :: (a, a, a) -> Vec 3 a
construct3 (x0, x1, x2) = x0 `Cons` (x1 `Cons` (x2 `Cons` Nil))

destruct1 :: Vec 1 a -> a
destruct1 (x0 `Cons` Nil) = x0

destruct2 :: Vec 2 a -> (a, a)
destruct2 (x0 `Cons` (x1 `Cons` Nil)) = (x0, x1)

destruct3 :: Vec 3 a -> (a, a, a)
destruct3 (x0 `Cons` (x1 `Cons` (x2 `Cons` Nil))) = (x0, x1, x2)

append :: forall n m a. KnownNat n => Vec n a -> Vec m a -> Vec (n+m) a
append xss ys = ifZero @n ys (let x `Cons` xs = xss in x `Cons` append xs ys)

concat :: forall n m a. (KnownNat n, KnownNat m) => Vec n (Vec m a) -> Vec (n*m) a
concat xss = ifZero @n Nil (let x `Cons` xs = xss in x `append` concat xs)

unconcat :: forall n m a. (KnownNat n, KnownNat m) => Vec (n*m) a -> Vec n (Vec m a)
unconcat xss = ifZero @n (Nil) (let (x, xs) = split @(n*m) @m xss in x `Cons` unconcat @(n-1) @m xs) 

select :: forall i n a. (KnownNat i, KnownNat n, (i+1) <= n) => Vec n a -> a
select xs = ifZero @n (error "Out-of-bounds") (let y `Cons` ys = xs in ifZero @i y (select @(i-1) ys))

split :: forall n n0 n1 a. (KnownNat n, KnownNat n0, KnownNat n1, n1 ~ (n-n0), n0 <= n) => Vec n a -> (Vec n0 a, Vec n1 a)
split xss = ifZero @n0 (Nil, xss) ((let x `Cons` xs = xss in let (as, bs) = split @(n-1) @(n0-1) @n1 xs in (x `Cons` as, bs)) :: (1 <= n) => (Vec n0 a, Vec n1 a))

update :: forall i n a. (KnownNat i, (i+1) <= n, 1 <= n) => (a -> a) -> Vec n a -> Vec n a
update f (x `Cons` xs) = ifZero @i (f x `Cons` xs) (x `Cons` update @(i-1) f xs)

head :: (1 <= n) => Vec n a -> a
head (x `Cons` _) = x

last :: forall n a. (KnownNat n, 1 <= n) => Vec n a -> a
last (x `Cons` xs) = ifZero @(n-1) x (last xs)

tail :: (1 <= n) => Vec n a -> Vec (n-1) a
tail (_ `Cons` xs) = xs

init :: forall n a. (KnownNat n, 1 <= n) => Vec n a -> Vec (n-1) a
init xs = ifZero @(n-1) Nil (let y `Cons` ys = xs in y `Cons` init ys)

uncons :: (1 <= n) => Vec n a -> (a, Vec (n-1) a)
uncons xs = (head xs, tail xs)

take :: forall i n a. (KnownNat i, i <= n) => Vec n a -> Vec i a
take xss = ifZero @i Nil ((let x `Cons` xs = xss in x `Cons` take @(i-1) xs) :: (1 <= n) => Vec i a)

drop :: forall n i a. (KnownNat n, KnownNat i, i <= n) => Vec n a -> Vec (n-i) a
drop xs = ifZero @(i) xs ((let _ `Cons` t = xs in (drop @(n-1) @(i-1) t :: (i-1 <= n-1) => Vec (n-i) a)) :: (1 <= n) => Vec (n-i) a)

rotateL :: forall n a. (KnownNat n, 1 <= n) => Vec n a -> Vec n a
rotateL xs = (tail xs) `append` singleton (head xs)

rotateR :: forall n a. (KnownNat n, 1 <= n) => Vec n a -> Vec n a
rotateR xs = last xs `Cons` init xs

reverse :: KnownNat n => Vec n a -> Vec n a
reverse = aux Nil
  where
    aux :: forall n0 n1 n a. (KnownNat n0, KnownNat n1, n0+n1 ~ n) => Vec n0 a -> Vec n1 a -> Vec n a
    aux acc xss = ifZero @n1 acc (let x `Cons` xs = xss in aux @(n0+1) (x `Cons` acc) xs)

zip :: forall n a b. KnownNat n => Vec n a -> Vec n b -> Vec n (a, b)
zip xss yss = ifZero @n Nil (let (x `Cons` xs, y `Cons` ys) = (xss, yss) in (x, y) `Cons` zip xs ys)

unzip :: forall n a b. KnownNat n => Vec n (a, b) -> (Vec n a, Vec n b)
unzip xyss = ifZero @n (Nil, Nil) (let (x, y) `Cons` xys = xyss in let (xs, ys) = unzip xys in (x `Cons` xs, y `Cons` ys))

map :: forall n a b. KnownNat n => (a -> b) -> Vec n a -> Vec n b
map f xss = ifZero @n Nil (let x `Cons` xs = xss in f x `Cons` map f xs)

zipWith :: KnownNat n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f xs ys = map (uncurry f) $ zip xs ys

foldr :: forall n a b. KnownNat n => (a -> b -> b) -> b -> Vec n a -> b
foldr f e xss = ifZero @n e (let x `Cons` xs = xss in x `f` foldr f e xs)

foldl :: forall n a b. KnownNat n => (b -> a -> b) -> b -> Vec n a -> b
foldl f e xss = ifZero @n e (let x `Cons` xs = xss in foldl f (e `f` x) xs)

foldr1 :: forall n a. (KnownNat n, 1 <= n) => (a -> a -> a) -> Vec n a -> a
foldr1 f xss = let x `Cons` xs = xss in ifZero @(n-1) x (x `f` foldr1 f xs)

foldl1 :: forall n a. (KnownNat n, 1 <= n) => (a -> a -> a) -> Vec n a -> a
foldl1 f xss = let x `Cons` xs = xss in foldl f x xs

scanr :: forall n a b. KnownNat n => (a -> b -> b) -> b -> Vec n a -> Vec n b
scanr f e = reverse . scanl (\b a -> f a b) e . reverse

scanl :: forall n a b. KnownNat n => (b -> a -> b) -> b -> Vec n a -> Vec n b
scanl f e xss = ifZero @n Nil (let x `Cons` xs = xss in let y = (e `f` x) in y `Cons` scanl f y xs)

transposeVV :: forall m n a. (KnownNat n, KnownNat m) => Vec m (Vec n a) -> Vec n (Vec m a)
transposeVV x = ifZero @n Nil (let (y, ys) = unzip . map (uncons) $ x in y `Cons` transposeVV ys)

transposeLV :: forall n a. KnownNat n => [Vec n a] -> Vec n [a]
transposeLV x = ifZero @n Nil (let (y, ys) = L.unzip . L.map (uncons) $ x in y `Cons` transposeLV ys)

transposeVL :: forall n a. KnownNat n => Vec n [a] -> [Vec n a]
transposeVL x = case Prelude.fmap unzip . Prelude.mapM (L.uncons) $ x of
  Just (y, ys) -> y : transposeVL ys
  Nothing -> []
