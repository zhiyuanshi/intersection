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

----------
|t1 <: t2|
----------

a <: a                             Sub-Var

           t1 <: t2
------------------------------     Sub-Forall
forall a . t1 <: forall a . t2

t3 <: t1     t2 <: t4
---------------------              Sub-Arrow
t1 -> t2 <: t3 -> t4

t <: t1   t <: t2
-----------------                  Sub-&1
t <: t1 & t2

t1 <: t
------------                       Sub-&2
t1 & t2 <: t

t2 <: t
------------                       Sub-&3
t1 & t2 <: t

*)

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
Require Import Setoid.

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
  | SVar : forall i x, sub i (Var nat x) (Var nat x)
  | SForall : forall i f g, sub (i+1) (f i) (g i) -> sub i (Forall nat f) (Forall nat g)
  (* | SAnd : forall i o1 o2 o3 o4, sub i o1 o3 -> sub i o2 o4 -> sub i (And nat o1 o2) (And nat o3 o4) *)
  | SFun : forall i o1 o2 o3 o4, sub i o3 o1 -> sub i o2 o4 -> sub i (Fun nat o1 o2) (Fun nat o3 o4)
  | SAnd1 : forall i t t1 t2, sub i t t1 -> sub i t t2 -> sub i t (And nat t1 t2)
  | SAnd2 : forall i t t1 t2, sub i t1 t -> sub i (And nat t1 t2) t
  | SAnd3 : forall i t t1 t2, sub i t2 t -> sub i (And nat t1 t2) t.

Lemma reflex : forall t1 i, sub i t1 t1.
Proof.
induction t1; intros.
(* Case Var *)
apply SVar.
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
apply SAnd1.
apply SAnd2.
apply IHt1_1.
apply SAnd3.
apply IHt1_2.
Defined.

Lemma invAndS1 : forall t t1 t2 i, sub i t (And nat t1 t2) -> sub i t t1 /\ sub i t t2. 
Proof.
induction t; intros.
(* Case Var *)
inversion H.
split.
exact H4.
exact H5.
(* Case Int *)
inversion H.
split.
exact H4.
exact H5.
(* Case Forall *)
inversion H0.
split.
exact H5.
exact H6.
(* Case Fun *)
inversion H.
split.
exact H4.
exact H5.
(* Case And *)
inversion H.
split.
exact H4.
exact H5.
assert (sub i t1 t0 /\ sub i t1 t3).
apply IHt1.
exact H4.
destruct H5.
split.
apply SAnd2.
exact H5.
apply SAnd2.
exact H6.
assert (sub i t2 t0 /\ sub i t2 t3).
apply IHt2.
exact H4.
destruct H5.
split.
apply SAnd3.
exact H5.
apply SAnd3.
exact H6.
Defined.

Lemma invAndS2 : forall t i t1 t2, sub i (And nat t1 t2) t -> sub i t1 t \/ sub i t2 t.
(* Case Var *)
induction t; intros.
inversion H.
left.
exact H4.
right.
exact H4.
(* Case Int *)
inversion H.
left.
exact H4.
right.
exact H4.
(* Case Forall *)
inversion H0.
left.
exact H5.
right.
exact H5.
(* Case Fun *)
inversion H.
left.
exact H4.
right.
exact H4.
(* Case And *)
assert (sub i (And nat t0 t3) t1 /\ sub i (And nat t0 t3) t2).
apply invAndS1.
exact H.
destruct H0.
assert (sub i t0 t1 \/ sub i t3 t1).
apply IHt1.
exact H0.
assert (sub i t0 t2 \/ sub i t3 t2).
apply IHt2.
apply H1.
destruct H2.
destruct H3.
left.
apply SAnd1.
exact H2.
exact H3.
admit.
destruct H3.
admit.
right.
apply SAnd1.
exact H2.
exact H3.
Defined.

(*
left.
apply SAnd1.

inversion H.
assert (sub i t0 t1 \/ sub i t3 t1).
apply IHt1.
apply H4.
assert (sub i t0 t2 \/ sub i t3 t2).
apply IHt2.
apply H5.
admit.
left.
exact H4.
right.
exact H4.
Defined.
*)


Lemma trans : forall t1 t2 i (s : sub i t1 t2) t3, sub i t2 t3 -> sub i t1 t3.
intro. intro. intro. intro.
induction s; intros.
apply H.
apply H.
inversion H.
apply SForall.
apply IHs.
apply H2.
admit.
inversion H.
apply SFun.
admit.
apply IHs2.
exact H5.
apply SAnd1.

induction t1; intros.
(* Case Var *)
inversion H.
rewrite <- H2 in H0. 
rewrite <- H2 in H. 
inversion H0.
apply H.
rewrite <- H8 in H0.
apply H0.
rewrite <- H5 in H0.
rewrite <- H5 in H.

induction t2; intros.
(* Case Var *)
inversion H0.
exact H.
rewrite <- H5 in H0.
inversion H.
rewrite H9 in H7.
rewrite <- H7 in H. 
apply H0.
rewrite <- H8 in H.

(*

inversion H0.
apply SAnd2.
exact H1.
*)
(*
rewrite <- H9 in H0.
apply SAnd1.
apply SAnd2.
*)
admit.
rewrite <- H3 in H.
inversion H0. 
apply H.
admit.
(* Case Int *)
inversion H.
apply H0.
rewrite <- H3 in H.
inversion H0.
apply H.
admit.
rewrite <- H3 in H.
inversion H0.
apply H.
admit.
(* Case Forall *)
inversion H0.
rewrite <- H4 in H0.
inversion H1.
apply SForall.
apply (H i).
exact H5.
exact H8.
apply SAnd1.
admit.
admit.
admit.
admit.
(* Case Fun *)
inversion H.
rewrite <- H4 in H.
inversion H0.
rewrite <- H11 in H0.
apply SFun.
apply (IHt2_1 _ _ _ H10 H5).
apply (IHt2_2 _ _ _ H6 H12).
admit.
admit.
admit.
(* Case And *)
inversion H.
inversion H0.
apply SAnd1.
admit.
admit.
apply IHt2_1.
apply H5.
apply H11.
apply IHt2_2.
apply H6.
apply H11.
inversion H0.


(*
Inductive SubWF : nat -> PTyp nat -> PTyp nat -> Prop :=
  | SubWFBase : forall i t, SubWF i t t
  | SubWFStep : SubWF i t1 t2 -> SubWF SubWF i t1 (And nat t2 t3)

sub i t1 t2 -> t1 = t2 \/   
*)

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

Lemma implements : forall t1 t2 n i, subTyp (size t1 n) t1 t2 i -> sub i t1 t2.
Proof.
induction t1; intros.
simpl in H.
destruct t2; try destruct H.
destruct (eq_nat_dec a n0).
rewrite e.
apply SVar. reflexivity.
destruct H.
destruct t2; try destruct H.
