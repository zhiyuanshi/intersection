{-# LANGUAGE FlexibleInstances, RecordWildCards #-}
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

precApp :: Int
precApp = 1

precFun :: Int
precFun = 2

parenPrec :: Int -> Int -> Doc -> Doc
parenPrec inheritedPrec currentPrec t
    | inheritedPrec <= 0          = t
    | inheritedPrec < currentPrec = parens t
    | otherwise                   = t

data L = L
    { lx :: Int  -- fresh label for variables
    , la :: Int  -- fresh label for type variables
    } deriving (Eq, Show)

class Pretty a where
    pretty :: a -> Doc
    pretty = prettyPrec 0 L{ lx = 0, la = 0 }
  
    prettyPrec :: Int -> L -> a -> Doc
    prettyPrec _ _ = pretty

alpha :: Int -> String
alpha n
    | n < 0     = error "alpha called with n < 0"
    | n < 26    = [chr (ord 'a' + n)]
    | otherwise = "a" ++ show (n - 26)

instance Pretty (PTyp Int) where
    prettyPrec p L{..} (Var a)     = text (alpha a)
    prettyPrec p L{..} (Forall f)  = text ("forall " ++ alpha la ++ ".") <+> prettyPrec p L{ la = la + 1, .. } (f la)
    prettyPrec p L{..} (Fun t1 t2) = parenPrec p precFun $ prettyPrec (precFun - 1) L{..} t1 <+> text "->" <+> prettyPrec p L{..} t2
    prettyPrec p L{..} PInt        = text "Int"

instance Pretty (PSigma Int) where
    prettyPrec p L{..} (And s1 s2) = prettyPrec p L{..} s1 <+> text "&" <+> prettyPrec p L{..} s2
    prettyPrec p L{..} (Typ t)     = prettyPrec p L{..} t

instance Pretty (PExp Int Int) where
    prettyPrec p L{..} (EVar x)     = text (alpha x)
    prettyPrec p L{..} (ELam t f)   = char '\\' <> 
                                                parens (text (alpha lx) <+> colon <+> prettyPrec p L{ lx = lx + 1, .. } t) <> 
                                                char '.' <+> 
                                                prettyPrec p L{ lx = lx + 1, .. } (f lx)
    prettyPrec p L{..} (ETLam f)    = text "/\\" <> text (alpha la) <> char '.' <+> prettyPrec p L{ la = la + 1, .. } (f la)
    prettyPrec p L{..} (ETApp e t)  = prettyPrec p L{..} e <+> prettyPrec p L{..} t
    prettyPrec p L{..} (EApp e1 e2) = prettyPrec precApp L{..} e1 <+> prettyPrec precApp L{..} e2 
    prettyPrec p L{..} (EAnd e1 e2) = prettyPrec precApp L{..} e1 <+> text "&" <+> prettyPrec precApp L{..} e2 
