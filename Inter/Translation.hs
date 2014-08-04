-- A type directed translation of System F with intersection types to System F
module Translation where

translate :: Expr t e ->
translate = go 0
  where
    go _ (Var t)   = return t
    go _ (Lit _)   = return Int
    go i (Lam t f) = do tbody <- go i (f t)
                        return (Fun t tbody)
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
