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
) where

import Prelude
import Data.Dynamic

import Lavatv.Nat
import qualified Lavatv.Vec as V
import Lavatv.Core

data HBool (clk :: Nat) = HBool { unHBool :: Signal }

instance Hard (HBool clk) where
    sigsCount = 1
    unpack x = [unHBool x]
    pack [x] = HBool x
    pack _ = error "bad size"

instance UHard (HBool clk) where
    type ClockOf (HBool clk) = clk
    type ReClock (HBool clk) c = HBool c

instance Show (HBool clk) where
    show = show . unHBool

htrue :: forall clk. KnownNat clk => HBool clk
htrue = sigwise0 (valueOf @clk) ((gate "htrue") {
      smt2=(gateFun0 \() -> "true")
    , sim=(gateSim0 \() -> True)
    }) ()

hfalse :: forall clk. KnownNat clk => HBool clk
hfalse = sigwise0 (valueOf @clk) ((gate "hfalse") {
      smt2=(gateFun0 \() -> "false")
    , sim=(gateSim0 \() -> False)
    }) ()

hnot :: forall clk. KnownNat clk => HBool clk -> HBool clk
hnot = sigwise1 (valueOf @clk) ((gate "hnot") {
      smt2=(gateFun1 \x -> "(not "++x++")")
    , sim=gateSim1 not
    })

hand :: forall clk. KnownNat clk => HBool clk -> HBool clk -> HBool clk
hand = sigwise2 (valueOf @clk) ((gate "hand") {
      smt2=(gateFun2 \x y -> "(and "++x++" "++y++")")
    , sim=gateSim2 (&&)
    })

hor :: forall clk. KnownNat clk => HBool clk -> HBool clk -> HBool clk
hor = sigwise2 (valueOf @clk) ((gate "hor") {
      smt2=(gateFun2 \x y -> "(or "++x++" "++y++")")
    , sim=gateSim2 (||)
    })

pulse :: forall clk. KnownPos clk => () -> HBool clk
pulse () = x
    where x = delay htrue $ hnot x

ite :: forall h clk. (UHard h, ClockOf h ~ clk, KnownNat clk) => HBool clk -> (h, h) -> h
ite cond (a, b) = pack $ map (sigite (unHBool cond)) $ (unpack a `zip` unpack b)
    where
        sigite :: Signal -> (Signal, Signal) -> Signal
        sigite sigc (sigt, sigf) = sig_comb (valueOf @clk) (gate "ite") {
              smt2=(gateFun3 \c t f -> "(ite "++c++" "++t++" "++f++")")
            , sim=(gateFun3 \c t f -> if (fromDyn c (error "bad type")) then t else f)
            } $ V.construct3 (sigc, sigt, sigf)
