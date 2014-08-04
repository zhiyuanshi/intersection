module Inter.Reduction where

import Unsafe.Coerce (unsafeCoerce)

import Inter.Syntax
import Inter.TypeCheck

import Data.Maybe       (fromMaybe)
import qualified Data.Map as Map

-- upcast Int (1 ,, \(x : Int). 1) = 1
-- upcast (Int -> Int) (1 ,, \(x : Int). 1) = \(x : Int). 1
-- upcast Int (3 ,, 4) = 3
upcast :: Type t -> Expr t e -> Maybe (Expr t e)
upcast t e
  | infer_exn e' == t'        = Just e
  | infer_exn e' `subtype` t' =
    case e of
      Merge e1 e2 ->
       case upcast t e1 of
         Nothing  -> upcast t e2
         Just e1' -> Just e1'
      _ -> Just e
  | otherwise = Nothing
  where
    e' = unsafeCoerce e
    t' = unsafeCoerce t

eliminateFreeTVars :: Map.Map Int (Type Int) -> Type Int -> Type Int
eliminateFreeTVars tenv = go
  where
    go (TVar a)    = fromMaybe (error "eliminateFreeTVars: lookup failed") (Map.lookup a tenv)
    go (Forall f)  = Forall (\a -> go (f a))
    go (Fun t1 t2) = Fun (go t1) (go t2)
    go Int         = Int
    go (And t1 t2) = And (go t1) (go t2)

evaluate :: Expr Int Int -> Maybe (Expr Int Int)
evaluate = evaluateWith (Map.empty, Map.empty) 0
  where
    evaluateWith (_,env) _ (Var x) = Map.lookup x env
    evaluateWith (tenv,env) i (App (Lam t f) arg) = do
      arg' <- upcast t arg -- TODO Remove tvars in t
      evaluateWith (tenv, Map.insert i arg' env) (i + 1) (f i)
    evaluateWith (tenv, env) i (TApp (TLam f) t) =
      evaluateWith (Map.insert i t tenv, env) (i + 1) (f i)
    evaluateWith _ _ e = Just e
