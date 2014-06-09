(*
data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt 

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)
*)

Inductive PTyp A := 
  | Var : A -> PTyp A
  | PInt : PTyp A
  | Forall : (A -> PTyp A) -> PTyp A
  | Fun : PTyp A -> PTyp A -> PTyp A
  | And : PTyp A -> PTyp A -> PTyp A.

(*
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
*)

Require Import Arith.

Check eq_nat_dec.

Fixpoint subTyp (t1 : PTyp nat) (t2 : PTyp nat) (i : nat) : Prop := 
  match (t1, t2) with 
      | (PInt,PInt) => True
      | (Var x, Var y) => if (eq_nat_dec x y) then True else False
      | (Forall f, Forall g) => subTyp (f i) (g i) (i+1)
      | (And o1 o2, And o3 o4) => and (subTyp o1 o3 i) (subTyp o2 o4 i)
      (*| (Fun o1 o2, Fun o3 o4) => and (subTyp o3 o1 i) (subTyp o2 o4 i) *)
      | (_,_) => False
  end.

Lemma reflex : forall (t1 : PTyp nat) (n : nat), subTyp t1 t1 n.
Proof.
intro.
induction t1; intro.
(* case Var *)
simpl.
destruct (eq_nat_dec a a).
auto.
destruct n0.
reflexivity.
(* case PInt *)
simpl.
reflexivity.
(* case Forall *)
simpl.
apply H.
(* Case Fun *)
admit.
(* Case And *)
simpl.
split.
apply IHt1_1.
apply IHt1_2.
Qed.