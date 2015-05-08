Require Import String.

(*
data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)
*)

Inductive PTyp A :=
  | Var : A -> PTyp A
  | PInt : PTyp A
  | Forall : (A -> PTyp A) -> PTyp A
  | Fun : PTyp A -> PTyp A -> PTyp A
  | And : PTyp A -> PTyp A -> PTyp A
  | Rcd : string -> PTyp A -> PTyp A.

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

Require Import Arith.
Require Import Setoid.

(* Subtyping relation *)

Inductive sub : nat -> PTyp nat -> PTyp nat -> Prop :=
  | SInt : forall i, sub i (PInt nat) (PInt nat)
  | SVar : forall i x, sub i (Var nat x) (Var nat x)
  | SForall : forall i f g, sub (i+1) (f i) (g i) -> sub i (Forall nat f) (Forall nat g)
  | SFun : forall i o1 o2 o3 o4, sub i o3 o1 -> sub i o2 o4 -> sub i (Fun nat o1 o2) (Fun nat o3 o4)
  | SAnd1 : forall i t t1 t2, sub i t t1 -> sub i t t2 -> sub i t (And nat t1 t2)
  | SAnd2 : forall i t t1 t2, sub i t1 t -> sub i (And nat t1 t2) t
  | SAnd3 : forall i t t1 t2, sub i t2 t -> sub i (And nat t1 t2) t
  | SRcd  : forall i s t1 t2, sub i t1 t2 -> sub i (Rcd nat s t1) (Rcd nat s t2).

Hint Resolve SVar SInt SForall SFun SAnd1 SAnd2 SAnd3 SRcd.

Lemma reflex : forall t1 i, sub i t1 t1.
Proof.
induction t1; intros; auto.
Defined.

Lemma invAndS1 : forall t t1 t2 i, sub i t (And nat t1 t2) -> sub i t t1 /\ sub i t t2.
Proof.
(*
induction t; intros; split; try (inversion H); auto.
*)
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
(* Case Rcd *)
inversion H.
split.
apply H4.
apply H5.
Defined.

Definition transitivity_sub S Q T := forall i, sub i S Q -> sub i Q T -> sub i S T.

Lemma trans : forall Q T S, transitivity_sub S Q T.
induction Q.
unfold transitivity_sub; intros.
induction T; try (inversion H0); auto.
rewrite H4 in H. auto.
unfold transitivity_sub; intros.
induction T; try (inversion H0); auto.
(* Case Forall *)
unfold transitivity_sub. intros.
generalize H1 H0. clear H0. clear H1.
generalize S. clear S.
induction T; intro; intro; try (inversion H1); auto.
induction S; intro; try (inversion H6); intros; auto.
apply SForall.
inversion H7.
apply (H i); auto.
(* Case Fun *)
unfold transitivity_sub; intros.
generalize H0 H. clear H0. clear H.
generalize S. clear S.
induction T; intro; intro; try (inversion H0); auto.
induction S; intro; try (inversion H7); auto.
inversion H8.
apply SFun.
apply IHQ1; auto.
apply IHQ2; auto.
(* Case And *)
unfold transitivity_sub; intros.
assert (sub i S Q1 /\ sub i S Q2).
apply invAndS1; auto.
destruct H1.
generalize H1 H2.
induction T; intros.
inversion H0.
apply IHQ1; auto.
apply IHQ2; auto.
inversion H0.
apply IHQ1; auto.
apply IHQ2; auto.
inversion H0.
apply IHQ1; auto.
apply IHQ2; auto.
inversion H0.
apply IHQ1; auto.
apply IHQ2; auto.
inversion H0.
apply SAnd1.
apply IHT1; auto.
apply IHT2; auto.
apply IHQ1; auto.
apply IHQ2; auto.
(* Case Rcd *)
unfold transitivity_sub; intros.
Defined.

Lemma p1 : forall (A B C : Prop), (A \/ B -> C) -> ((A -> C) /\ (B -> C)).
Proof.
intros.
split; intros.
apply H.
left.
exact H0.
apply H.
right.
exact H0.
Defined.

Definition equiv i t1 t2 := sub i t1 t2 /\ sub i t2 t1.

Definition contextEq i t1 t2 := (forall t, sub i t1 t -> sub i t2 t) /\ (forall t, sub i t t1 -> sub i t t2).

Definition narrowing_sub P Q X S T := forall i, sub i P Q -> (sub i X Q -> sub i S T) -> sub i X P -> sub i S T.

Lemma narrowing : forall X P Q S T, transitivity_sub X P Q -> narrowing_sub P Q X S T.
unfold narrowing_sub; intros.
apply H1.
apply H.
exact H2.
exact H0.
Defined.
