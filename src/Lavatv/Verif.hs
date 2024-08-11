{-|
Module      : Lavatv.Verif
Description : SMT-based verification
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Verif (
  Lavatv.Verif.test
) where

import Prelude hiding ((<>))
import Data.Maybe

import Lavatv.Core
import Lavatv.Utils
import qualified Lavatv.Vec as V

import Text.PrettyPrint

type Vec = V.Vec

smtLet :: Doc -> Doc -> Doc -> Doc
smtLet var expr bod = parens $ text "let" <+> (parens $ parens $ var <+> expr) $+$ bod

smtEq :: Doc -> Doc -> Doc
smtEq a b = parens $ text "=" <+> a <+> b

smtAssert :: Doc -> Doc
smtAssert expr = parens $ text "assert" <+> expr

sigRef :: Doc -> Doc -> Signal -> Doc
sigRef prefix regPrefix s = case sigSignal s of
    Comb (GateOp _ _) -> prefix <> text "sig" <> int (sigId s)
    CstSample _ _ -> prefix <> text "sig" <> int (sigId s)
    UpSample _ _ -> prefix <> text "sig" <> int (sigId s)
    Comb DontCare -> prefix <> text "dontcare_sig" <> int (sigId s)
    Comb (Symbolic n) -> prefix <> text "input_sig" <> int (sigId s) <> text ("_" ++ n)
    Reg _ _ _ -> prefix <> regPrefix <> text "_sig" <> int (sigId s)

sigCombDef :: Doc -> Signal -> Maybe Doc
sigCombDef regPrefix s = case sigSignal s of
    Comb (GateOp g l) ->
        Just ((fromMaybe (error ("Gate `"++gateName g++"` has no smt2 semantic")) (gateSmt2 g)) (V.map (sigRef empty regPrefix) l))
    Comb DontCare -> Nothing
    Comb (Symbolic _) -> Nothing
    CstSample _ x -> Just (sigRef empty regPrefix x)
    UpSample 1 x -> Just (sigRef empty regPrefix x)
    UpSample _ _ -> error "unique clock required"
    Reg _ 1 _ -> Nothing
    Reg _ _ _ -> error "unique clock required"

defineConstants :: Netlist -> Doc
defineConstants net = vcat $ map def cstnet
  where
    cstnet = filter (\s -> sigClock s == 0) net
    def s = case sigCombDef undefined s of
        Just expr -> parens $ text "define-const" <+> sigRef empty undefined s <+> text (sigSmt2Type s) <+> expr
        Nothing -> parens $ text "declare-const" <+> sigRef empty undefined s <+> text (sigSmt2Type s)

defineTransition :: Netlist -> Signal -> Doc
defineTransition net prop = parens $ text "define-fun"
    <+> transitionName
    <+> parens ((parens $ text "prop" <+> text "Bool") <+> hsep args)
    <+> text "Bool"
    $+$ body
  where
    livenet = filter (\s -> sigClock s > 0) net
    transitionName = text "transition" <> int (sigId prop)
    args = map arg livenet
    arg s = case sigSignal s of
        Comb DontCare -> parens $ sigRef empty undefined s <+> (text $ sigSmt2Type s)
        Comb (Symbolic _) -> parens $ sigRef empty undefined s <+> (text $ sigSmt2Type s)
        Comb (GateOp _ _) -> empty
        CstSample _ _ -> empty
        UpSample _ _ -> empty
        Reg _ _ _ ->
            (parens $ sigRef empty (text "prev") s <+> (text $ sigSmt2Type s))
            <+> (parens $ sigRef empty (text "next") s <+> (text $ sigSmt2Type s))
    body = foldr letsig inner livenet
    letsig s = maybe id (smtLet (sigRef empty undefined s)) (sigCombDef (text "prev") s)
    inner = parens $ (text "and") <+> smtEq (text "prop") (sigRef empty undefined prop)
        <+> (hsep $ map (\s -> case sigSignal s of
            Reg _ _ x -> smtEq (sigRef empty (text "next") s) (sigRef empty (text "prev") x)
            _ -> empty
        ) livenet)

makeZ3Faster :: Doc
makeZ3Faster = text "(push)"

defineAll :: Netlist -> Signal -> Doc
defineAll net prop = defineConstants net $+$ defineTransition net prop $+$ makeZ3Faster

declareTick :: Doc -> Netlist -> Doc
declareTick prefix net = vcat $ map decl livenet
  where
    livenet = filter (\s -> sigClock s > 0) net
    decl s = case sigCombDef undefined s of
        Just _ -> empty
        Nothing -> parens $ text "declare-const" <+> sigRef prefix (text "reg") s <+> text (sigSmt2Type s)

quantifyTick :: Doc -> Netlist -> Doc -> Doc
quantifyTick prefix net body = foldr decl body livenet
  where
    livenet = filter (\s -> sigClock s > 0) net
    decl s = case sigCombDef undefined s of
        Just _ -> id
        Nothing -> \b -> parens $ text "forall" <+> (parens $ sigRef prefix (text "reg") s <+> text (sigSmt2Type s)) <+> b

transitionConstraint :: Doc -> Doc -> Doc -> Netlist -> Signal -> Doc
transitionConstraint prefixPrev prefixNext propExpr net propSig = transition
  where
    livenet = filter (\s -> sigClock s > 0) net
    transitionName = text "transition" <> int (sigId propSig)
    transition = parens $ transitionName
        <+> propExpr
        <+> args
    args = hsep $ map arg livenet
    arg s = case sigSignal s of
        Comb DontCare -> sigRef prefixPrev undefined s
        Comb (Symbolic _) -> sigRef prefixPrev undefined s
        Comb (GateOp _ _) -> empty
        CstSample _ _ -> empty
        UpSample _ _ -> empty
        Reg _ _ _ -> sigRef prefixPrev (text "reg") s <+> sigRef prefixNext (text "reg") s

bounded :: Int -> Netlist -> Signal -> Doc
bounded k net propSig = defineAll net propSig $+$ declarations $+$ assertions
  where
    tickPrefix i = text "bounded" <> int i <> text "_"
    declarations = vcat (map (\i -> declProp i $+$ declareTick (tickPrefix i) net) [0..k])
    propName i = tickPrefix i <> text "prop"
    declProp i = parens $ text "declare-const" <+> propName i <+> text "Bool"
    assertions = if k == 0 then text "(assert false)" else vcat $ map (\i -> parens $ text "assert" <+> transitionConstraint (tickPrefix i) (tickPrefix (i+1)) (propName i) net propSig) [0..k-1]

test :: Signal -> Doc
test s = bounded 1 (sortedNetlist s) s
