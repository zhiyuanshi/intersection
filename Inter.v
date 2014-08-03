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

Require Import Arith.
Require Import Setoid.

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

Hint Resolve SVar SInt SForall SFun SAnd1 SAnd2 SAnd3.

Lemma reflex : forall t1 i, sub i t1 t1.
Proof.
induction t1; intros; auto.
Defined.

Definition narrowing_sub P Q X S T := forall i, sub i P Q -> (sub i X Q -> sub i S T) -> sub i X P -> sub i S T.

Definition transitivity_sub S Q T := forall i, sub i S Q -> sub i Q T -> sub i S T.

Lemma narrowing : forall X P Q S T, transitivity_sub X P Q -> narrowing_sub P Q X S T.
unfold narrowing_sub; intros.
apply H1.
apply H.
exact H2.
exact H0.
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
admit.
Defined.

Lemma trans : forall Q S T, transitivity_sub S Q T.
induction Q.
unfold transitivity_sub; intros.
induction T; try (inversion H0); auto. 
rewrite H4 in H. auto.
unfold transitivity_sub; intros.
induction T; try (inversion H0); auto.
(* Case Forall *)
unfold transitivity_sub; intros.
induction T; try (inversion H1); auto.
induction S; try (inversion H0); auto.
apply SForall.
unfold transitivity_sub in H.
apply (H i); auto.
admit.
admit.
(* Case Fun *)
unfold transitivity_sub; intros.
generalize H0 H. clear H0. clear H.
generalize S. clear S.
induction T; induction S; intros. 
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H1.
inversion H0.
inversion H0.
inversion H.
inversion H.
inversion H1.
(* Case 1 *)
inversion H0.
inversion H.
apply SFun.
apply IHQ1; auto.
apply IHQ2; auto.
inversion H.
(* Case 2 *)
apply SAnd2.
apply IHS1.
exact H0.
exact H5.
apply SAnd3.
apply IHS2; auto.
inversion H.
inversion H.
inversion H1.
(* Case 3 *)
assert (sub i (Fun nat Q1 Q2) T1 /\ sub i (Fun nat Q1 Q2) T2).
apply invAndS1; auto.
destruct H1.
apply SAnd1.
apply IHT1; auto.
apply IHT2; auto.
assert (sub i (Fun nat Q1 Q2) T1 /\ sub i (Fun nat Q1 Q2) T2).
apply invAndS1; auto.
destruct H1.
assert (sub i S1 (Fun nat Q1 Q2) \/ sub i S2 (Fun nat Q1 Q2)).
apply invAndS2; auto.
destruct H3.
apply SAnd2.
apply IHS1.
exact H0.
exact H3.
apply SAnd3.
apply IHS2.
auto.
auto.
(* Case And *)
unfold transitivity_sub; intros.
assert (sub i S Q1 /\ sub i S Q2).
apply invAndS1; auto.
destruct H1.
assert (sub i Q1 T \/ sub i Q2 T).
apply invAndS2; auto.
destruct H3.
apply IHQ1; auto.
apply IHQ2; auto.
Defined.

Definition equiv i t1 t2 := sub i t1 t2 /\ sub i t2 t1.

Definition contextEq i t1 t2 := (forall t, sub i t1 t -> sub i t2 t) /\ (forall t, sub i t t1 -> sub i t t2).




Definition substitutability : 
  forall t1 t2 i, equiv i t2 t1 -> contextEq i t2 t1 /\ contextEq i t1 t2.
intro. intro. intro. intro.
destruct H.
induction H; split; try split; intros.
(* Case Int *)
exact H.
exact H.
exact H.
exact H.
(* Case Var *)
exact H.
exact H.
exact H.
exact H.
(* Case Forall *)
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd1.
apply IHt1.
apply H6.
apply IHt2.
apply H7.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd2.
apply IHt1.
apply H6.
apply SAnd3.
apply IHt2.
apply H6.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd1.
apply IHt1.
apply H6.
apply IHt2.
apply H7.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd2.
apply IHt1.
apply H6.
apply SAnd3.
apply IHt2.
apply H6.
(* Case Fun *)
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd1.
apply IHt1.
exact H7. 
apply IHt2.
exact H8.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd2.
apply IHt1.
exact H7. 
apply SAnd3.
apply IHt2.
exact H7.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd1.
apply IHt1.
exact H7. 
apply IHt2.
exact H8.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd2.
apply IHt1.
exact H7. 
apply SAnd3.
apply IHt2.
exact H7.
(* Case And1 *)
(*
generalize i, t1, t2, H, H1, H0, IHsub1, IHsub2, t0, H2.
clear H2. clear t0. clear IHsub2. clear IHsub1. clear H0. clear H1. clear H. clear t2. clear t1. clear i. *)
induction t; intros.
inversion H0.
apply SAnd2.
apply IHsub1.
exact H7.
exact H2.
apply SAnd3.
apply IHsub2.
exact H7.
exact H2.
inversion H0.
apply SAnd2.
apply IHsub1.
exact H7.
exact H2.
apply SAnd3.
apply IHsub2.
exact H7.
exact H2.
inversion H0. (*H2*)
apply SAnd2.
apply IHsub1.
exact H8.
exact H2. (*H3*)
apply SAnd3. 
apply IHsub2.
exact H8.
exact H2. (*H3*)
inversion H0.
apply SAnd2.
apply IHsub1.
exact H7.
exact H2.
apply SAnd3.
apply IHsub2.
exact H7.
exact H2.
admit.
admit. 
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
Defined.

Lemma ForallInv : forall t p g i, (forall t : PTyp nat, sub i (Forall nat p) t -> sub i (Forall nat g) t) -> 
                  sub (i + 1) (p i) t -> sub (i + 1) (g i) t.
intros.
assert (sub i (Forall nat g) (Forall nat (fun i => t))).
apply H.
apply SForall.
exact H0.
inversion H1.
exact H5.
Defined.

Lemma FunInv1 : forall o t t1 t2 t3 t4 i, (forall t : PTyp nat, sub i (Fun nat t1 t2) t -> sub i (Fun nat t3 t4) t) -> 
               sub i t1 t -> sub i o t.
intros.
(* assert (sub i (Fun nat t3 t4) (Fun )). *) 
admit.
Defined.

Lemma FunInv2 : forall t t1 t2 t3 t4 i, (forall t : PTyp nat, sub i (Fun nat t1 t2) t -> sub i (Fun nat t3 t4) t) -> 
               sub i t2 t -> sub i t4 t.
intros.
assert (exists t10, sub i (Fun nat t3 t4) (Fun nat t10 t)).
exists t1.
apply H.
apply SFun.
apply reflex.
exact H0.
destruct H1.
inversion H1.
exact H8.
Defined.

Lemma funnyLemma : forall t1 t3 i (s : sub i t1 t3) t2, (forall t, sub i t2 t -> sub i t3 t) -> sub i t1 t2.
intro. intro. intro. intro.
induction s; intros.
(* Case PInt *)
apply H.
apply reflex.
(* Case Var *)
apply H.
apply reflex.
(* Case Forall *)
assert (sub i (Forall nat g) t2).
apply H.
apply reflex.
induction t2; try (inversion H0). 
assert (sub (i+1) (f i) (p i)).
apply IHs. intro.
apply (ForallInv _ _ _ _ H).
apply SForall.
exact H6.
apply SAnd1.
apply IHt2_1.
intros.
apply H.
apply SAnd2.
exact H7.
exact H5.
apply IHt2_2.
intros.
apply H.
apply SAnd3.
exact H7.
exact H6.
(* Case Fun *)
(*
generalize i, o1, o2, o3, o4 , s1, s2, IHs1, IHs2, H.
clear H. clear IHs2. clear IHs1. clear s2. clear s1. clear o4. clear o3. clear o2. clear o1. clear i.
induction t2; intros.
assert (sub i (Fun nat o3 o4) (Var nat a)).
apply H. apply reflex.
inversion H0.
admit.
admit.
apply SFun.
*)

assert (sub i (Fun nat o3 o4) t2).
apply H.
apply reflex.
induction t2; try (inversion H0).
apply SFun.
assert (sub i o3 t2_1).
apply IHs1.
intros.
assert (sub i (Fun nat o3 o4) (Fun nat (Fun nat o1 o2) t2_1)). 
apply H.
apply SFun.
apply IHt2_1.
intros.
apply H.

(* Using H! *) 
apply (FunInv1 o1 _ t2_1 t2_2 o3 o4). 
apply H.
admit.
apply IHs2.
intro.
apply (FunInv2 _ t2_1 _ o3).
apply H.
apply SAnd1.
apply IHt2_1.
intros.
admit. 
admit.
admit.
admit.
admit.
admit.
Defined.

Lemma trans : forall t1 t2 i (s : sub i t1 t2) t3, sub i t2 t3 -> sub i t1 t3.
intro. intro. intro. intro.
induction s.
(* Case Var *)
intros.
apply H.
(* Case PInt *)
intros.
apply H.
(* Case Forall *)
induction t3; intros; try (inversion H).
apply SForall.
apply IHs.
inversion H0.
exact H4.
apply SAnd1.
apply IHt3_1.
exact H4.
apply IHt3_2.
exact H5.
(* Case Fun *)
induction t3; intros; try (inversion H).
inversion H0.
apply SFun.
apply (funnyLemma _ _ _ H4 _ IHs1). 
apply IHs2.
exact H6.
apply SAnd1.
apply IHt3_1.
exact H4.
apply IHt3_2.
exact H5.
(* Case SAnd *)
(* refactor out *)
intros; induction t3.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
inversion H.
apply IHs1.
exact H5.
apply IHs2.
exact H5.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
assert (sub i (And nat t1 t2) t3_1 /\ sub i (And nat t1 t2) t3_2).
apply invAndS1.
exact H.
destruct H0.
apply SAnd1.
apply IHt3_1.
exact H0.
apply IHt3_2.
exact H1.
intros.
apply SAnd2.
apply IHs.
exact H.
intros.
apply SAnd3.
apply IHs.
exact H.
Defined.

(* A functional definition : algorithm *)

Fixpoint size (t : PTyp nat) (i : nat) : nat :=
  match t with
      | PInt => 1
      | Var x => 1
      | Forall f => 1 + size (f i) (i+1)
      | And o1 o2 => 1 + max (size o1 i) (size o2 i)
      | Fun o1 o2 => 1 + max (size o1 i) (size o2 i)
  end.

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
