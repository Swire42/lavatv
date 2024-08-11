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
import Text.PrettyPrint

import Lavatv.Nat
import Lavatv.Core

data HBool (clk :: Nat) = HBool { unHBool :: Signal }

sigInfoHBool :: forall clk. KnownNat clk => SigInfo
sigInfoHBool = SigInfo { sigClock=valueOf @clk, sigSmt2Type="Bool" }

instance Hard (HBool clk) where
    sigsCount = 1
    unpack x = [unHBool x]
    pack [x] = HBool x
    pack _ = error "bad size"

instance UHard (HBool clk) where
    type ClockOf (HBool clk) = clk
    type ReClock (HBool clk) c = HBool c

    dontCare () = HBool $ sig_dontcare (sigInfoHBool @clk)
    symbolic = HBool . sig_symbolic (sigInfoHBool @clk)

htrue :: forall clk. KnownNat clk => HBool clk
htrue = HBool $ sig_comb0 (sigInfoHBool @clk) ((gate "htrue") {
      gateSmt2=(gateFun0 \() -> text "true")
    , gateSim=(gateSim0 \() -> True)
    }) ()

hfalse :: forall clk. KnownNat clk => HBool clk
hfalse = HBool $ sig_comb0 (sigInfoHBool @clk) ((gate "hfalse") {
      gateSmt2=(gateFun0 \() -> text "false")
    , gateSim=(gateSim0 \() -> False)
    }) ()

hnot :: forall clk. KnownNat clk => HBool clk -> HBool clk
hnot a = HBool $ sig_comb1 (sigInfoHBool @clk) ((gate "hnot") {
      gateSmt2=(gateFun1 \x -> parens $ text "not" <+> x)
    , gateSim=gateSim1 not
    }) (unHBool a)

hand :: forall clk. KnownNat clk => HBool clk -> HBool clk -> HBool clk
hand a b = HBool $ sig_comb2 (sigInfoHBool @clk) ((gate "hand") {
      gateSmt2=(gateFun2 \x y -> parens $ text "and" <+> x <+> y)
    , gateSim=gateSim2 (&&)
    }) (unHBool a, unHBool b)

hor :: forall clk. KnownNat clk => HBool clk -> HBool clk -> HBool clk
hor a b = HBool $ sig_comb2 (sigInfoHBool @clk) ((gate "hor") {
      gateSmt2=(gateFun2 \x y -> parens $ text "or" <+> x <+> y)
    , gateSim=gateSim2 (||)
    }) (unHBool a, unHBool b)

pulse :: forall clk. KnownPos clk => () -> HBool clk
pulse () = x
    where x = delay htrue $ hnot x

ite :: forall h clk. (UHard h, ClockOf h ~ clk, KnownNat clk) => HBool clk -> (h, h) -> h
ite cond (a, b) = pack $ map (sigite (unHBool cond)) $ (unpack a `zip` unpack b)
    where
        sigite :: Signal -> (Signal, Signal) -> Signal
        sigite sigc (sigt, sigf) = sig_comb3 (sigInfo sigt) (gate "ite") {
              gateSmt2=(gateFun3 \c t f -> parens $ text "ite" <+> c <+> t <+> f)
            , gateSim=(gateFun3 \c t f -> if (fromDyn c (error "bad type")) then t else f)
            } $ (sigc, sigt, sigf)
