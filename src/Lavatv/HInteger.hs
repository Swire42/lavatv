{-|
Module      : Lavatv.HInteger
Description : Hardware integers
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.HInteger (
  Lavatv.HInteger.HInteger(..)
, Lavatv.HInteger.sigInfoHInteger
, Lavatv.HInteger.hinteger
, Lavatv.HInteger.hadd
, Lavatv.HInteger.hmul
) where

import Prelude
import Data.Dynamic
import Text.PrettyPrint

import Lavatv.Nat
import Lavatv.Core
import Lavatv.Sim
import Lavatv.HBool
import Lavatv.Vec(Vec)
import qualified Lavatv.Vec as V

data HInteger (clk :: Nat) = HInteger { unHInteger :: Signal }

sigInfoHInteger :: forall clk. KnownNat clk => SigInfo
sigInfoHInteger = SigInfo { sigClock=valueOf @clk, sigSmt2Type="Int" }

instance Hard (HInteger clk) where
    sigsCount = 1
    unpack x = [unHInteger x]
    pack [x] = HInteger x
    pack _ = error "bad size"

instance UHard (HInteger clk) where
    type ClockOf (HInteger clk) = clk
    type ReClock (HInteger clk) c = HInteger c

    dontcare () = HInteger $ sig_dontcare (sigInfoHInteger @clk)
    symbolic = HInteger . sig_symbolic (sigInfoHInteger @clk)

instance KnownNat clk => SimAs (HInteger clk) Integer where
    fromSim = HInteger . sig_comb1 (sigInfoHInteger @clk) (gateSimId @Integer) . unSim
    toSim = Sim . sig_comb1 (sigInfoSim @clk) (gateSimId @Integer) . unHInteger

instance KnownNat clk => HEq (HInteger clk) where
    heq a b = HBool $ sig_comb2 (sigInfoHInteger @clk) ((gate "heq") {
          gateSmt2=(gateFun2 \x y -> parens $ text "=" <+> x <+> y)
        , gateSim=gateSim2 ((==) @Integer)
        }) (unHInteger a, unHInteger b)

hinteger :: forall clk. KnownNat clk => Integer -> HInteger clk
hinteger x = HInteger $ sig_comb0 (sigInfoHInteger @clk) ((gate "hinteger") {
      gateSmt2=(gateFun0 \() -> text $ show x)
    , gateSim=(gateSim0 \() -> x)
    }) ()

hadd :: forall clk. KnownNat clk => HInteger clk -> HInteger clk -> HInteger clk
hadd a b = HInteger $ sig_comb2 (sigInfoHInteger @clk) ((gate "hadd") {
      gateSmt2=(gateFun2 \x y -> parens $ text "+" <+> x <+> y)
    , gateSim=gateSim2 ((+) @Integer)
    }) (unHInteger a, unHInteger b)

hmul :: forall clk. KnownNat clk => HInteger clk -> HInteger clk -> HInteger clk
hmul a b = HInteger $ sig_comb2 (sigInfoHInteger @clk) ((gate "hmul") {
      gateSmt2=(gateFun2 \x y -> parens $ text "*" <+> x <+> y)
    , gateSim=gateSim2 ((*) @Integer)
    }) (unHInteger a, unHInteger b)
