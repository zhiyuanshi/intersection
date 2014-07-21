{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Pretty where

import Data.Char        (chr, ord)
import Text.PrettyPrint

import Syntax

prettyPrint :: Pretty a => a -> String
prettyPrint = show . pretty

prettyPrintPSigma :: PSigma Int -> String
prettyPrintPSigma = prettyPrint

prettyPrintPExp :: PExp Int Int -> String
prettyPrintPExp = prettyPrint

parenPrec :: Int -> Int -> Doc -> Doc
parenPrec inheritedPrec currentPrec t
    | inheritedPrec <= 0          = t
    | inheritedPrec < currentPrec = parens t
    | otherwise                   = t

class Pretty a where
    pretty :: a -> Doc
    pretty = prettyPrec 0 (0, 0)

    prettyPrec :: Int -> (Int, Int) -> a -> Doc
    prettyPrec _ _ = pretty

uident :: Int -> String
uident n
    | n < 0     = error "`lident` called with n < 0"
    | n < 26    = [chr (ord 'A' + n)]
    | otherwise = "A" ++ show (n - 25)

lident :: Int -> String
lident n
    | n < 0     = error "`uident` called with n < 0"
    | n < 26    = [chr (ord 'a' + n)]
    | otherwise = "a" ++ show (n - 25)

instance Pretty (PTyp Int) where
    prettyPrec p l@(luident, llident) t =
        case t of
            Var a     -> text (uident a)
            Forall f  -> text ("forall " ++ uident luident ++ ".") <+> prettyPrec p (luident+1, llident) (f luident)
            Fun t1 t2 -> parenPrec p 3 $ prettyPrec 2 l t1 <+> text "->" <+> prettyPrec 3 l t2
            PInt      -> text "Int"

instance Pretty (PSigma Int) where
    prettyPrec p l o =
        case o of
            And o1 o2 -> parenPrec p 4 $ prettyPrec p l o1 <+> text "&" <+> prettyPrec 3 l o2
            Typ t     -> prettyPrec p l t

instance Pretty (PExp Int Int) where
    prettyPrec p l@(luident, llident) e =
        case e of
            EVar x     -> text (lident x)
            ETLam f    -> parenPrec p 3 $ text ("/\\" ++ uident luident ++ ".") <+> prettyPrec 0 (luident+1, llident) (f luident)
            ELam o f   -> parenPrec p 3 $
                            text ("\\(" ++ lident llident ++ " : " ++ show (prettyPrec p (luident, llident+1) o) ++ ").")
                            <+> prettyPrec 0 (luident, llident+1) (f llident)
            ETApp e1 t -> parenPrec p 2 $ prettyPrec 2 l e1 <+> prettyPrec 1 l t
            EApp e1 e2 -> parenPrec p 2 $ prettyPrec 2 l e1 <+> prettyPrec 1 l e2
            EAnd e1 e2 -> parenPrec p 3 $ prettyPrec 3 l e1 <+> text ",," <+> prettyPrec 3 l e2
