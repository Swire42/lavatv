{-|
Module      : Lavatv.SMT
Description : Low-level SMT-based verification
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.SMT (
  Lavatv.SMT.bounded
, Lavatv.SMT.safeNeighborhood
, Lavatv.SMT.checkSat
, Lavatv.SMT.checkBounded
, Lavatv.SMT.checkSafeNeighborhood
, Lavatv.SMT.withNetlist
) where

import Prelude hiding ((<>))
import Data.Maybe
import System.IO
import System.Process
import Text.PrettyPrint

import Lavatv.Core
import Lavatv.Utils
import qualified Lavatv.Vec as V


type Vec = V.Vec

smtLet :: Doc -> Doc -> Doc -> Doc
smtLet var expr bod = parens $ text "let" <+> (parens $ parens $ var <+> expr) $+$ bod

smtEq :: Doc -> Doc -> Doc
smtEq a b = parens $ text "=" <+> a <+> b

smtAssert :: Doc -> Doc
smtAssert expr = parens $ text "assert" <+> expr

sigRef :: Doc -> Doc -> Signal -> Doc
sigRef prefix regPrefix s = case sigDef s of
    Comb (GateOp _ _) -> prefix <> text "sig" <> int (sigId s)
    CstSample _ _ -> prefix <> text "sig" <> int (sigId s)
    UpSample _ _ -> prefix <> text "sig" <> int (sigId s)
    Comb DontCare -> prefix <> text "dontcare_sig" <> int (sigId s)
    Comb (Symbolic n) -> prefix <> text "input_sig" <> int (sigId s) <> text ("_" ++ n)
    Reg _ _ _ -> prefix <> regPrefix <> text "_sig" <> int (sigId s)

sigCombDef :: Doc -> Signal -> Maybe Doc
sigCombDef regPrefix s = case sigDef s of
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
    cstnet = filter (\s -> sigClock (sigInfo s) == 0) net
    def s = case sigCombDef undefined s of
        Just expr -> parens $ text "define-const" <+> sigRef empty undefined s <+> text (sigSmt2Type (sigInfo s)) <+> expr
        Nothing -> parens $ text "declare-const" <+> sigRef empty undefined s <+> text (sigSmt2Type (sigInfo s))

defineTransition :: Netlist -> Signal -> Doc
defineTransition net prop = parens $ text "define-fun"
    <+> transitionName
    <+> parens ((parens $ text "prop" <+> text "Bool") <+> hsep args)
    <+> text "Bool"
    $+$ body
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    transitionName = text "transition" <> int (sigId prop)
    args = map arg livenet
    arg s = case sigDef s of
        Comb DontCare -> parens $ sigRef empty undefined s <+> (text $ sigSmt2Type (sigInfo s))
        Comb (Symbolic _) -> parens $ sigRef empty undefined s <+> (text $ sigSmt2Type (sigInfo s))
        Comb (GateOp _ _) -> empty
        CstSample _ _ -> empty
        UpSample _ _ -> empty
        Reg _ _ _ ->
            (parens $ sigRef empty (text "prev") s <+> (text $ sigSmt2Type (sigInfo s)))
            <+> (parens $ sigRef empty (text "next") s <+> (text $ sigSmt2Type (sigInfo s)))
    body = foldr letsig inner livenet
    letsig s = maybe id (smtLet (sigRef empty undefined s)) (sigCombDef (text "prev") s)
    inner = parens $ (text "and") <+> smtEq (text "prop") (sigRef empty (text "prev") prop)
        <+> (hsep $ map (\s -> case sigDef s of
            Reg _ _ x -> smtEq (sigRef empty (text "next") s) (sigRef empty (text "prev") x)
            _ -> empty
        ) livenet)

makeZ3Faster :: Doc
makeZ3Faster = parens $ text "push"

defineAll :: Netlist -> Signal -> Doc
defineAll net prop = defineConstants net $+$ defineTransition net prop $+$ makeZ3Faster

declareTickInput :: Doc -> Netlist -> Doc
declareTickInput prefix net = vcat $ map decl livenet
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    decl s = case sigDef s of
        Comb DontCare -> parens $ text "declare-const" <+> sigRef prefix undefined s <+> text (sigSmt2Type (sigInfo s))
        Comb (Symbolic _) -> parens $ text "declare-const" <+> sigRef prefix undefined s <+> text (sigSmt2Type (sigInfo s))
        _ -> empty

declareTickState :: Doc -> Netlist -> Doc
declareTickState prefix net = vcat $ map decl livenet
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    decl s = case sigDef s of
        Reg _ _ _ -> parens $ text "declare-const" <+> sigRef prefix (text "reg") s <+> text (sigSmt2Type (sigInfo s))
        _ -> empty

quantifyTickInput :: Doc -> Netlist -> Doc -> Doc
quantifyTickInput prefix net body = if decls /= empty then parens $ text "forall" <+> parens decls <+> body else body
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    decls = hsep $ map decl livenet
    decl s = case sigDef s of
        Comb DontCare -> parens $ sigRef prefix undefined s <+> text (sigSmt2Type (sigInfo s))
        Comb (Symbolic _) -> parens $ sigRef prefix undefined s <+> text (sigSmt2Type (sigInfo s))
        _ -> empty

quantifyTickState :: Doc -> Netlist -> Doc -> Doc
quantifyTickState prefix net body = if decls /= empty then parens $ text "exists" <+> parens decls <+> body else body
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    decls = hsep $ map decl livenet
    decl s = case sigDef s of
        Reg _ _ _ -> parens $ sigRef prefix (text "reg") s <+> text (sigSmt2Type (sigInfo s))
        _ -> empty

initialConstraint :: Doc -> Netlist -> Doc
initialConstraint prefix net = vcat $ map cstr net
  where
    cstr s = case sigDef s of
        Reg i _ _ -> parens $ text "assert" <+> (parens $ text "=" <+> sigRef prefix (text "reg") s <+> sigRef empty undefined i)
        _ -> empty

transitionConstraint :: Doc -> Doc -> Doc -> Doc -> Netlist -> Signal -> Doc
transitionConstraint prefixPrev prefixInput prefixNext propExpr net propSig = transition
  where
    livenet = filter (\s -> sigClock (sigInfo s) > 0) net
    transitionName = text "transition" <> int (sigId propSig)
    transition = parens $ transitionName
        <+> propExpr
        <+> args
    args = hsep $ map arg livenet
    arg s = case sigDef s of
        Comb DontCare -> sigRef prefixInput undefined s
        Comb (Symbolic _) -> sigRef prefixInput undefined s
        Comb (GateOp _ _) -> empty
        CstSample _ _ -> empty
        UpSample _ _ -> empty
        Reg _ _ _ -> sigRef prefixPrev (text "reg") s <+> sigRef prefixNext (text "reg") s

bounded :: Int -> (Netlist, Signal) -> Doc
bounded depth (net, propSig) = defineAll net propSig $+$ declarations $+$ assertions $+$ check
  where
    tickPrefix i = text "bounded" <> int i <> text "_"
    declarations = vcat (map (\i -> declProp i $+$ declareTickInput (tickPrefix i) net $+$ declareTickState (tickPrefix i) net) [0..depth-1]) $+$ declareTickState (tickPrefix depth) net
    propName i = tickPrefix i <> text "prop"
    declProp i = parens $ text "declare-const" <+> propName i <+> text "Bool"
    assertions = initialConstraint (tickPrefix 0) net
        $+$ (vcat $ map (\i -> parens $ text "assert" <+> transitionConstraint (tickPrefix i) (tickPrefix i) (tickPrefix (i+1)) (propName i) net propSig) [0..depth-1])
        $+$ (parens $ text "assert" <+> (parens $ text "not" <+> (parens $ hsep $ text "and" : text "true" : map (\i -> propName i) [0..depth-1])))
    check = parens $ text "check-sat"

safeNeighborhood :: Int -> (Netlist, Signal) -> Doc
safeNeighborhood depth (net, propSig) = defineAll net propSig $+$ declarations $+$ assertions $+$ check
  where
    tickPrefix i = text "induction" <> int i <> text "_"
    safePrefix i = text "safe" <> int i <> text "_"
    declarations = vcat (map (\i -> declareTickInput (tickPrefix i) net $+$ declareTickState (tickPrefix i) net) [0..depth]) $+$ declareTickState (tickPrefix (depth+1)) net
    safe = foldr (\i x -> quantifyTickInput (safePrefix i) net $ quantifyTickState (safePrefix (i+1)) net $ parens $ text "and" <+> transitionConstraint (if i == 0 then tickPrefix i else safePrefix i) (safePrefix i) (safePrefix (i+1)) (text "true") net propSig <+> x) (text "true") [0..depth-1]
    assertions = (parens $ text "assert" <+> safe)
        $+$ (vcat $ map (\i -> parens $ text "assert" <+> transitionConstraint (tickPrefix i) (tickPrefix i) (tickPrefix (i+1)) (text "true") net propSig) [0..depth-1])
        $+$ (parens $ text "assert" <+> transitionConstraint (tickPrefix depth) (tickPrefix depth) (tickPrefix (depth+1)) (text "false") net propSig)
    check = parens $ text "check-sat"

checkSat :: Doc -> IO Bool
checkSat input = withCreateProcess solver \(Just hIn) (Just hOut) _ _ -> do
    hSetBuffering hIn LineBuffering
    hPutStrLn hIn $ renderStyle (Style OneLineMode 0 0) input
    ln <- hGetLine hOut
    case ln of
        "sat" -> return True
        "unsat" -> return False
        _ -> error $ "Unexpected SMT output: '" ++ ln ++ "'"
  where
    solver = (proc "z3" ["-in"]) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }

checkBounded :: Int -> (Netlist, Signal) -> IO Bool
checkBounded depth circ = fmap not $ checkSat $ bounded depth circ

checkSafeNeighborhood :: Int -> (Netlist, Signal) -> IO Bool
checkSafeNeighborhood depth circ = fmap not $ checkSat $ safeNeighborhood depth circ

withNetlist :: Signal -> (Netlist, Signal)
withNetlist s = (sortedNetlist s, s)
