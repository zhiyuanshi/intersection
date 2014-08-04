module Inter.Syntax where

-- t ::= a | forall a. t | t1 -> t2 | Int | t1 & t2

data Type t
  = TVar t
  | Forall (t -> Type t)
  | Fun (Type t) (Type t)
  | Int
  | And (Type t) (Type t)

-- e ::= x | \(x : t). e | e1 e2 | /\a. e | e t | e1 ,, e2

data Expr t e
  = Var e
  | Lit Integer
  | Lam (Type t) (e -> Expr t e)
  | App (Expr t e) (Expr t e)
  | TLam (t -> Expr t e)
  | TApp (Expr t e) (Type t)
  | Merge (Expr t e) (Expr t e)
