{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
module Inter.TypeCheck where

import Inter.Syntax

{-
  Subtyping Relations:

    Sub-Int:                            =>      Int <: Int
    Sub-TVar:                           =>      a <: a
    Sub-Forall: t1 <: t2                =>      forall a. t1 <: forall a. t2
    Sub-Fun:    t3 <: t1   t2 <: t4     =>      t1 -> t2 <: t3 -> t4
    Sub-&1:     t <: t1   t <: t2       =>      t <: t1 & t2
    Sub-&2:     t1 <: t                 =>      t1 & t2 <: t
    Sub-&3:     t2 <: t                 =>      t1 & t2 <: t
-}

subtype :: Type Int -> Type Int -> Bool
subtype = go 0
  where
    go _  Int         Int        = True
    go _ (TVar a)    (TVar b)    = a == b
    go i (Forall f)  (Forall g)  = go (i + 1) (f i) (g i)
    go i (Fun t1 t2) (Fun t3 t4) = go i t3 t1 && go i t2 t4
    go i t           (And t1 t2) = go i t  t1 && go i t  t2
    go i (And t1 t2) t           = go i t1 t  || go i t2 t -- Sub-&2 and Sub-&3
    go _  _           _          = False

data TypeError t e
  = Mismatch { expr            :: Expr t e
             , expected_verbal :: String
             , actual          :: Type t
             }
  | NotASubtype { expr     :: Expr t e
                , expected :: Type t -- type(expr) should <: expected
                , actual   :: Type t
                }

equivalent :: Type Int -> Type Int -> Bool
equivalent t1 t2 = subtype t1 t2 && subtype t2 t1

-- Structural equality
instance Eq (Type Int) where
  (==) = go 0
    where
      go _  Int         Int        = True
      go _ (TVar a)    (TVar b)    = a == b
      go _ (Fun t1 t2) (Fun t3 t4) = t1 == t3 && t2 == t4
      go _ (And t1 t2) (And t3 t4) = t1 == t3 && t2 == t4
      go i (Forall f)  (Forall g)  = go (i + 1) (f i) (g i)
      go _  _           _          = False

infer :: Expr Int (Type Int) -> Either (TypeError Int (Type Int)) (Type Int)
infer = go 0
  where
    go _ (Var t)   = return t
    go _ (Lit _)   = return Int
    go i (Lam t f) = do tbody <- go i (f t)
                        return (Fun t tbody)
{-
  Consider the type of the expression:
    (\(x:Int). x + 1) (1,,\(x:Int). 1)
    Int -> Int        Int & (Int -> Int)

  It should reduce to:
    2
    Int
-}
    go i (App (Lam t f) e2) = do
      t2 <- go i e2
      if subtype t2 t
        then go i (f t) -- This should be t instead of t2. See the note above.
        else Left NotASubtype { expr     = e2
                              , expected = t
                              , actual   = t2
                              }
    go i (App e1 _) = do
      t1 <- go i e1
      Left Mismatch { expr   = e1
                    , actual = t1
                    , expected_verbal = "lambda"
                    }
    go i (TLam f) = do tbody <- go (i + 1) (f i)
                       return $ Forall (\a -> substType (i, TVar a) tbody)
    go i (TApp (TLam f) t) = do tbody <- go (i + 1) (f i)
                                return $ substType (i, t) tbody
    go i (TApp e1 _) = do
      t1 <- go i e1
      Left Mismatch { expr   = e1
                    , actual = t1
                    , expected_verbal = "type lambda"
                    }
    go i (Merge e1 e2) = do t1 <- go i e1
                            t2 <- go i e2
                            return (And t1 t2)

infer_exn :: Expr Int (Type Int) -> Type Int
infer_exn e =
  case infer e of
    Left Mismatch{}    -> error "Type mismatch"
    Left NotASubtype{} -> error "Subtype expected"
    Right t            -> t

normalize :: Type Int -> Type Int
normalize (TVar t)    = TVar t
normalize (Forall f)  = Forall (\a -> normalize (f a))
normalize Int         = Int
normalize (Fun t1 t2) = Fun (normalize t1) (normalize t2)
normalize (And t1 t2)
  | subtype t1 t2 = normalize t1
  | subtype t2 t1 = normalize t2
  | otherwise     = And (normalize t1) (normalize t2)

substType :: (Int, Type Int) -> Type Int -> Type Int
substType (i, t) = go
  where
    go (TVar a)
      | a == i     = t
      | otherwise  = TVar a
    go (Forall f)  = Forall (\a -> go (f a))
    go (Fun t1 t2) = Fun (go t1) (go t2)
    go Int         = Int
    go (And t1 t2) = And (go t1) (go t2)
