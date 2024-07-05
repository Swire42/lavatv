{-|
Module      : Lavatv.HBool
Description : Hardware booleans
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.HBool (
  Lavatv.HBool.HBool(unHBool)
, Lavatv.HBool.htrue
, Lavatv.HBool.hfalse
, Lavatv.HBool.hnot
, Lavatv.HBool.hand
, Lavatv.HBool.hor
, Lavatv.HBool.pulse
, Lavatv.HBool.ite
, Lavatv.HBool.ite'
) where

import Prelude
import Control.Arrow ((>>>))

import Lavatv.Nat
import qualified Lavatv.Vec as V
import qualified Lavatv.HPair as HP
import Lavatv.Core

data HBool (clk :: Nat) = HBool { unHBool :: Signal clk }
  deriving Show

instance Hard HBool where
    dontCare = HBool . dontCare
    lift1 f = HBool . f . unHBool
    lift2 f a b = HBool $ f (unHBool a) (unHBool b)

htrue :: forall clk. Clock clk => HBool clk
htrue = HBool $ comb (gate { smt2= \V.Nil -> "true" }) V.Nil

hfalse :: forall clk. Clock clk => HBool clk
hfalse = HBool $ comb (gate { smt2= \V.Nil -> "false" }) V.Nil

hnot :: forall clk. Clock clk => HBool clk -> HBool clk
hnot = lift1 $ comb gate { smt2=(\(x `V.Cons` V.Nil) -> "(not "++x++")") } . V.construct1

hand :: forall clk. Clock clk => HBool clk -> HBool clk -> HBool clk
hand = lift2 $ curry $ comb gate { smt2=(\(x `V.Cons` (y `V.Cons` V.Nil)) -> "(and "++x++" "++y++")") } . V.construct2

hor :: forall clk. Clock clk => HBool clk -> HBool clk -> HBool clk
hor = lift2 $ curry $ comb gate { smt2=(\(x `V.Cons` (y `V.Cons` V.Nil)) -> "(or "++x++" "++y++")") } . V.construct2

pulse :: forall clk. LiveClock clk => () -> HBool clk
pulse () = x
    where x = delay htrue $ hnot x

ite :: forall h clk. (Hard h, Clock clk) => HBool clk -> (h clk, h clk) -> h clk
ite cond = uncurry $ lift2 $ sigite (unHBool cond)
    where
        sigite :: Signal clk -> Signal clk -> Signal clk -> Signal clk
        sigite sigc sigt sigf = comb gate { smt2=(V.destruct3 >>> \(c, t, f) -> "(ite "++c++" "++t++" "++f++")") } $ V.construct3 (sigc, sigt, sigf)

ite' :: forall h clk. (Hard h, Clock clk) => HBool clk -> HP.HPair h h clk -> h clk
ite' cond pair = ite cond (HP.unHPair pair)
