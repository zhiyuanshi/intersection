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
Require Import Arith.MinMax.

Check eq_nat_dec.

Check max.

Fixpoint size (t : PTyp nat) (i : nat) : nat :=
  match t with
      | PInt => 1
      | Var x => 1
      | Forall f => 1 + size (f i) (i+1)
      | And o1 o2 => 1 + max (size o1 i) (size o2 i)
      | Fun o1 o2 => 1 + max (size o1 i) (size o2 i)
  end.

(* Subtyping relation *)

Inductive sub : nat -> PTyp nat -> PTyp nat -> Prop :=
  | SInt : forall i, sub i (PInt nat) (PInt nat)
  | SVar : forall i x y, x = y -> sub i (Var nat x) (Var nat y)
  | SForall : forall i f g, sub (i+1) (f i) (g i) -> sub i (Forall nat f) (Forall nat g)
  | SAnd : forall i o1 o2 o3 o4, sub i o1 o3 -> sub i o2 o4 -> sub i (And nat o1 o2) (And nat o3 o4)
  | SFun : forall i o1 o2 o3 o4, sub i o3 o1 -> sub i o2 o4 -> sub i (Fun nat o1 o2) (Fun nat o3 o4).

Lemma reflex : forall t1 i, sub i t1 t1.
Proof.
induction t1; intros.
(* Case Var *)
apply SVar.
reflexivity.
(* Case SInt *)
apply SInt.
(* case Forall *)
apply SForall.
apply H.
(* case Fun *)
apply SFun.
apply IHt1_1.
apply IHt1_2.
(* case And *)
apply SAnd.
apply IHt1_1.
apply IHt1_2.
Defined.

(* A functional definition : algorithm *)

Fixpoint subTyp (n : nat) (t1 : PTyp nat) (t2 : PTyp nat) (i : nat) : Prop  :=
  match n with 
      | 0 => False
      | S m =>
          match (t1,t2) with 
            | (PInt,PInt) => True
            | (Var x, Var y) => if (eq_nat_dec x y) then True else False
            | (Forall f, Forall g) => subTyp m (f i) (g i) (i+1)
            | (And o1 o2, And o3 o4) => and (subTyp m o1 o3 i) (subTyp m o2 o4 i)
            | (Fun o1 o2, Fun o3 o4) => and (subTyp m o3 o1 i) (subTyp m o2 o4 i)
            | (_,_) => False
          end
  end.
