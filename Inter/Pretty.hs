{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
module Inter.Pretty
  ( showType
  , showExpr
  ) where

import Data.Char        (chr, ord)
import Text.PrettyPrint.Leijen

import Inter.Syntax

showType :: Type Int -> String
showType = show . pretty

showExpr :: Expr Int Int -> String
showExpr = show . pretty

name :: Char -> Int -> String
name c i
  | i < 0     = error "i < 0"
  | i < 26    = [chr (ord c + i)]
  | otherwise = c : show (i - 25)

tvar :: Int -> String
tvar = name 'A'

var :: Int -> String
var = name 'a'

instance Pretty (Type Int) where
  pretty = pretty' 0
    where
      pretty' a = go
        where
          go (TVar a')    = text (tvar a')
          go (Forall f)  = parens $ text "forall" <+> text (tvar a) <> char '.' <+> pretty' (a + 1) (f a)
          go (Fun t1 t2) = parens $ go t1 <+> text "->" <+> go t2
          go Int         = text "Int"
          go (And t1 t2) = parens $ go t1 <+> char '&' <+> go t2

instance Pretty (Expr Int Int) where
  pretty = pretty' (0,0)
    where
      pretty' (a,x) = go
        where
          go (Var x')      = text (var x')
          go (Lit n)       = integer n
          go (TLam f)      = parens $ text "/\\" <> text (tvar a) <> char '.' <+> pretty' (a + 1, x) (f a)
          go (Lam t f)     = parens $ char '\\' <> parens (text (var x) <+> char ':' <+> pretty t) <> char '.'
                                      <+> pretty' (a, x + 1) (f x)
          go (TApp e1 t)   = parens $ go e1 <+> pretty t
          go (App e1 e2)   = parens $ go e1 <+> go e2
          go (Merge e1 e2) = parens $ go e1 <+> text ",," <+> go e2
