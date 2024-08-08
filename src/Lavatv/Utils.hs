{-|
Module      : Lavatv.Utils
Description : Utility functions
Copyright   : (c) Victor Miquel, 2024
License     : MIT
-}

module Lavatv.Utils (
  Lavatv.Utils.sortedNetlist
, Lavatv.Utils.formatNetlist
) where

import Prelude hiding ((<>))
import Control.Exception

import Lavatv.Core
import Lavatv.Uniq
import qualified Lavatv.Vec as V

import Text.PrettyPrint

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

type Vec = V.Vec

-- topological sort with respect to combinational dependencies
-- note: vulnerable to combinational cycles
sortedNetlist :: Signal -> [Signal]
sortedNetlist = reverse . snd . snd . global (IntSet.empty, (IntSet.empty, []))
  where
    slInsert :: Signal -> (IntSet, [Signal]) -> (IntSet, [Signal])
    slInsert s (set, lis) = assert (not $ IntSet.member (uniqVal $ uniq s) set) (IntSet.insert (uniqVal $ uniq s) set, s : lis)

    local :: (IntSet, [Signal]) -> Signal -> (IntSet, [Signal])
    local (set, lis) s = if IntSet.member (uniqVal $ uniq s) set then (set, lis) else
        slInsert s $ case signal s of
            Comb (GateOp _ l) -> V.foldl local (set, lis) l
            Comb DontCare -> (set, lis)
            Comb (Symbolic _) -> (set, lis)
            CstSample _ x -> local (set, lis) x
            UpSample _ x -> local (set, lis) x
            Reg i _ _ -> local (set, lis) i

    global :: (IntSet, (IntSet, [Signal])) -> Signal -> (IntSet, (IntSet, [Signal]))
    global (set, sl) s = if IntSet.member (uniqVal $ uniq s) set then (set, sl) else
        let set2 = IntSet.insert (uniqVal $ uniq s) set in
        let sl2 = local sl s in
        let ss2 = (set2, sl2) in
        case signal s of
            Comb (GateOp _ l) -> V.foldl global ss2 l
            Comb DontCare -> ss2
            Comb (Symbolic _) -> ss2
            CstSample _ x -> global ss2 x
            UpSample _ x -> global ss2 x
            Reg i _ x -> global (global ss2 i) x

formatNetlist :: Signal -> Doc
formatNetlist = vcat . map line . sortedNetlist
  where
    sig :: Signal -> Doc
    sig s = text "#" <> (int $ uniqVal $ uniq s)

    line :: Signal -> Doc
    line s = sig s <+> text "=" <+> case signal s of
        Comb (GateOp g l) -> text (name g) <+> hsep (V.toList $ V.map sig l)
        Comb DontCare -> text "DontCare"
        Comb (Symbolic n) -> text ("\"" ++ n ++ "\"")
        CstSample clk x -> text "CstSample" <+> int clk <+> sig x
        UpSample k x -> text "UpSample" <+> int k <+> sig x
        Reg i k x -> text "Reg" <+> sig i <+> int k <+> sig x
