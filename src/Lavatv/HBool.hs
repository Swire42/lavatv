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

instance Hard HBool where
    sigsCount = 1
    unpack x = [unHBool x]
    pack [x] = HBool x
    pack _ = error "bad size"

instance Show (HBool clk) where
    show = show . unHBool

htrue :: forall clk. Clock clk => HBool clk
htrue = sigwise0 (gate { smt2=Just (\V.Nil -> "true") }) ()

hfalse :: forall clk. Clock clk => HBool clk
hfalse = sigwise0 (gate { smt2=Just (\V.Nil -> "false") }) ()

hnot :: forall clk. Clock clk => HBool clk -> HBool clk
hnot = sigwise1 (gate { smt2=Just (\(x `V.Cons` V.Nil) -> "(not "++x++")") })

hand :: forall clk. Clock clk => HBool clk -> HBool clk -> HBool clk
hand = sigwise2 (gate { smt2=Just (\(x `V.Cons` (y `V.Cons` V.Nil)) -> "(and "++x++" "++y++")") })

hor :: forall clk. Clock clk => HBool clk -> HBool clk -> HBool clk
hor = sigwise2 (gate { smt2=Just (\(x `V.Cons` (y `V.Cons` V.Nil)) -> "(or "++x++" "++y++")") })

pulse :: forall clk. LiveClock clk => () -> HBool clk
pulse () = x
    where x = delay htrue $ hnot x

ite :: forall h clk. (Hard h, Clock clk) => HBool clk -> (h clk, h clk) -> h clk
ite cond (a, b) = pack $ map (sigite (unHBool cond)) $ (unpack a `zip` unpack b)
    where
        sigite :: Signal clk -> (Signal clk, Signal clk) -> Signal clk
        sigite sigc (sigt, sigf) = comb gate { smt2=Just (V.destruct3 >>> \(c, t, f) -> "(ite "++c++" "++t++" "++f++")") } $ V.construct3 (sigc, sigt, sigf)

ite' :: forall h clk. (Hard h, Clock clk) => HBool clk -> HP.HPair h h clk -> h clk
ite' cond pair = ite cond (HP.unHPair pair)
