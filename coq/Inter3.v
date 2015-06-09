Require Import String.

(*
data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)
*)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp.

(* Atomic types *)

(*
Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).
*)

Require Import Arith.
Require Import Setoid.

(* Subtyping relation *)

Inductive sub : PTyp -> PTyp -> Prop :=
  | SInt : sub PInt PInt
  | SFun : forall o1 o2 o3 o4, sub o3 o1 -> sub o2 o4 -> sub (Fun o1 o2) (Fun  o3 o4)
  | SAnd1 : forall t t1 t2, sub t t1 -> sub t t2 -> sub t (And  t1 t2)
  | SAnd2 : forall t t1 t2, sub t1 t -> sub (And  t1 t2) t
  | SAnd3 : forall t t1 t2, sub t2 t -> sub (And  t1 t2) t.

(* Orthogonality: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt.

(*  | OLift : forall t1 t2, not (sub t1 t2) -> not (sub t2 t1) -> Atomic t1 -> Atomic t2 -> Ortho t1 t2. *)

(* Orthogonality: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, sub A C /\ sub B C).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> Ortho t1 t2 -> WFTyp (And t1 t2).


(* Reflexivity *)

Hint Resolve SInt SFun SAnd1 SAnd2 SAnd3.

Lemma reflex : forall (t1 : PTyp), sub t1 t1.
Proof.
induction t1; intros; auto.
Defined.


Lemma invWFSInt : forall t2, WFTyp t2 -> sub PInt t2 -> t2 = PInt. 
Proof. 
intro. intro. intro.
induction H; intros. reflexivity.
inversion H0.
inversion H0.
assert (t1 = PInt). apply  IHWFTyp1. auto. rewrite H8 in H2.
assert (t2 = PInt). apply  IHWFTyp2. auto. rewrite H9 in H2.
inversion H2. 
Defined.

(*
Lemma invWFSFun : forall t1 t2 t3, WFTyp t3 -> sub (Fun t1 t2) t3 -> exists t4 t5, sub t4 t1 /\ sub t2 t5 /\ t3 = Fun t4 t5. 
Proof.
intros.
induction H.
inversion H0.
exists t0. exists t3. split. inversion H0. auto. 
split. inversion H0. auto. reflexivity.
inversion H0.
assert (exists t4 t5 : PTyp, sub t4 t1 /\ sub t2 t5 /\ t0 = Fun t4 t5). apply IHWFTyp1. auto. 
destruct H8. destruct H8. destruct H8. destruct H9. rewrite H10 in H2.
assert (exists t4 t5 : PTyp, sub t4 t1 /\ sub t2 t5 /\ t3 = Fun t4 t5). apply IHWFTyp2. auto. 
destruct H11. destruct H11. destruct H11. destruct H12. rewrite H13 in H2.
exists x. exists x0. split. exact H8. split. exact H9.
inversion H2.
admit.*)

(* Orthogonality algorithm is complete *)

Lemma ortho_completness : forall (t1 t2 : PTyp), OrthoS t1 t2 -> Ortho t1 t2.
Proof.
induction t1; intros; unfold OrthoS in H.
(* Case PInt *)
induction t2.
destruct H. exists PInt. split; apply reflex.
apply OIntFun.
apply OAnd2. 
apply IHt2_1. unfold not. unfold not in H. intros; apply H.
destruct H0. destruct H0. 
exists x. split. exact H0. apply SAnd2. exact H1.
apply IHt2_2. unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0. exists x.
split. auto. apply SAnd3.
auto.
(* Case Fun t1 t2 *)
induction t2.
apply OFunInt. 
apply OFun.
apply IHt1_2. unfold OrthoS. unfold not. intros.
unfold not in H. apply H.
destruct H0. destruct H0.
exists (Fun (And t1_1 t2_1) x).
split.
apply SFun.
apply SAnd2.
apply reflex.
auto.
apply SFun.
apply SAnd3. apply reflex.
auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2.
apply IHt2_1.
unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0.
exists x. split. auto. apply SAnd2. exact H1.
apply IHt2_2.
unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0.
exists x. split. auto. apply SAnd3. exact H1.
(* Case (t11 & t12) _|_ t2 *) 
apply OAnd1.
apply IHt1_1.
unfold OrthoS.
unfold not. unfold not in H.
intro.
apply H.
clear H. destruct H0. destruct H.
exists x.
split.
apply SAnd2. exact H.
exact H0.
apply IHt1_2.
unfold OrthoS; unfold not; intro. unfold not in H.
apply H. clear H.
destruct H0.
destruct H.
exists x.
split.
apply SAnd3.
exact H.
exact H0.
Defined.

Lemma nosub : forall t1 t2, OrthoS t1 t2 -> not (sub t1 t2) /\ not (sub t2 t1).
Proof.
intros; split; unfold not.
unfold OrthoS in H. unfold not in H. intros.
apply H.
exists t2.
split. auto. apply reflex.
unfold OrthoS in H. unfold not in H. intros.
apply H.
exists t1. split. apply reflex. auto.
Defined.


Lemma invAndS1 : forall t t1 t2, sub t (And t1 t2) -> sub t t1 /\ sub t t2.
Proof.
induction t; intros.
(* Case Int *)
inversion H.
split; auto.
(* Case Fun *)
inversion H.
split; auto.
(* Case And *)
inversion H.
split; auto.
assert (sub t1 t0 /\ sub t1 t3).
apply IHt1.
auto.
destruct H4.
split.
apply SAnd2.
auto.
apply SAnd2.
auto.
assert (sub t2 t0 /\ sub t2 t3).
apply IHt2.
auto.
destruct H4.
split.
apply SAnd3.
auto.
apply SAnd3.
auto.
Defined.

Lemma uniquesub : forall A B C, 
  OrthoS A B -> sub (And A B) C -> not (sub A C /\ sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. apply H. exists C. auto.
Defined.

(* Lemmas needed to prove soundness of the orthogonality algorithm *)

Lemma ortho_sym : forall A B, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS. unfold not.
intros. apply H.
destruct H0. destruct H0.
exists x.
split; auto.
Defined.

Lemma ortho_and : forall A B C, OrthoS A C -> OrthoS B C -> OrthoS (And A B) C.
Proof.
intros. unfold OrthoS.
unfold not. intros.
destruct H1. destruct H1.
induction x. 
inversion H1. unfold OrthoS in H. apply H. exists (PInt). split; auto.
unfold OrthoS in H0. apply H0. exists (PInt). split; auto.
inversion H1. unfold OrthoS in H. apply H. exists (Fun x1 x2). split; auto.
unfold OrthoS in H0. apply H0. exists (Fun x1 x2). split; auto.
assert (sub C x1 /\ sub C x2). apply invAndS1. auto. destruct H3.
inversion H1. apply IHx1; auto.
unfold OrthoS in H. apply H. exists (And x1 x2). split; auto.
unfold OrthoS in H0. apply H0. exists (And x1 x2). split; auto.
Defined.

Lemma ortho_soundness : forall (t1 t2 : PTyp), Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(* Hard case *)
assert (OrthoS t1 t3). apply IHOrtho1; auto.
assert (OrthoS t2 t3). apply IHOrtho2; auto.
apply ortho_and; auto.
assert (OrthoS t2 t1). apply ortho_sym. apply IHOrtho1; auto.
assert (OrthoS t3 t1). apply ortho_sym. apply IHOrtho2; auto.
apply ortho_sym.
apply ortho_and; auto.
(* Case FunFun *)
unfold OrthoS. unfold not. intros.
unfold OrthoS in IHOrtho. apply IHOrtho.
destruct H0. destruct H0. generalize H0. generalize H1. clear H0. clear H1.
induction x; intros. inversion H1. exists x2.
split. inversion H0. auto. inversion H1. auto.
apply IHx1.
inversion H1. auto.
inversion H0. auto.
(* Case IntFun *)
unfold OrthoS. unfold not. intros.
destruct H. destruct H. induction x. inversion H0. inversion H.
apply IHx1.
inversion H. auto.
inversion H0. auto. 
(* Case FunInt *)
unfold OrthoS. unfold not. intros.
destruct H. destruct H. induction x. inversion H. inversion H0.
apply IHx1. inversion H. auto.
inversion H0. auto.
Defined.

(* Old theorems *)

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
Defined.

Definition Ortho A B := forall n, not (exists C, sub n A C /\ sub n B C).



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
