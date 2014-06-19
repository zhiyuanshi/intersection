module IntersectionSubtyping where

-- Syntax:

-- t ::= a | forall a . o | o1 -> o2 | Int
-- o ::= o1 & o2 | t 

data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt 

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)

-- e ::= x | \(x : o) . e | e1 e2 | /\a . e | e t | e1 & e2

data PExp t e = 
    EVar e 
  | ELam (PSigma t) (e -> PExp t e) 
  | EApp (PExp t e) (PExp t e) 
  | ETLam (t -> PExp t e)
  | ETApp (PExp t e) (PSigma t)
  | EAnd (PExp t e) (PExp t e)  

-- Int & Int
t1 = And (Typ PInt) (Typ PInt)

-- Int
t2 = Typ PInt

-- Int & (Int -> Int)
t3 = And (Typ PInt) t4

-- (Int -> Int) & Int
t7 = And t4 (Typ PInt)

-- Int -> Int
t4 = Typ (Fun (Typ PInt) (Typ PInt))

-- forall a . a -> a 
t5 = Typ (Forall (\a -> Typ (Fun (Typ (Var a)) (Typ (Var a)))))

-- forall a . Int & a -> a
t6 = Typ (Forall (\a -> Typ (Fun (And (Typ PInt) (Typ (Var a))) (Typ (Var a)))))

{- Subtyping Relation:

----------
|t1 <: t2|
----------

a <: a                             Sub-Var

           o1 <: o2
------------------------------     Sub-Forall
forall a . o1 <: forall a . o2

o3 <: o1     o2 <: o4
---------------------              Sub-Arrow
o1 -> o2 <: o3 -> o4

----------
|o1 <: o2|
----------

o <: o1   o <: o2
-----------------                  Sub-&1
o <: o1 & o2

o <: t
------                             Sub-ot
o <: t

--------
|o <: t|
--------

o1 <: t
------------                       Sub-&2
o1 & o2 <: t

o2 <: t
------------                       Sub-&3
o1 & o2 <: t

t1 <: t2
--------                           Sub-tt
t1 <: t2
-}

subTyp :: PTyp Int -> PTyp Int -> Int -> Bool
subTyp PInt    PInt             _ = True
subTyp (Var x) (Var y)          _ = x == y
subTyp (Forall f) (Forall g)    i = subSigma (f i) (g i) (i+1)
subTyp (Fun o1 o2) (Fun o3 o4)  i = subSigma o3 o1 i && subSigma o2 o4 i 
subTyp _           _            _ = False

subSigma :: PSigma Int -> PSigma Int -> Int -> Bool
subSigma o (And o1 o2) i = subSigma o o1 i && subSigma o o2 i 
subSigma o (Typ t)     i = subSigma2 o t i

subSigma2 :: PSigma Int -> PTyp Int -> Int -> Bool
subSigma2 (And o1 o2) t  i = subSigma2 o1 t i || subSigma2 o2 t i
subSigma2 (Typ t1)    t2 i = subTyp t1 t2 i

sub o1 o2 = subSigma o1 o2 0

tcheck :: PExp Int (PSigma Int) -> Int -> Maybe (PSigma Int)
tcheck (EVar t)    _  = Just t 
tcheck (ELam s f)  i  = 
  do tbody <- tcheck (f s) i
     return (Typ (Fun s tbody))
tcheck (EApp e1 e2) i = 
  do t1 <- tcheck e1 i
     t2 <- tcheck e2 i
     case t1 of 
        Typ (Fun t3 t4) | subSigma t2 t3 i  -> Just t4 
        _                                   -> Nothing
tcheck (ETLam f) i =   
  do t <- tcheck (f i) (i+1)
     return (Typ (Forall (\x -> subst i (Typ (Var x)) t))) 
tcheck (ETApp e o) i = 
  do t <- tcheck e i
     case t of
        Typ (Forall f) -> Just (subst i o (f i)) 
        otherwise -> Nothing
tcheck (EAnd e1 e2) i = 
  do t1 <- tcheck e1 i
     t2 <- tcheck e2 i
     return (And t1 t2)

subst :: Int -> PSigma Int -> PSigma Int -> PSigma Int
subst = error "TODO!"
