Require Import String.

(*
data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)
*)

Inductive S := Base | Inter.

Inductive PTyp : S -> Type :=
  | PInt : PTyp Base
  | Fun : PTyp Inter -> PTyp Inter -> PTyp Base
  | And : PTyp Inter -> PTyp Inter -> PTyp Inter
  | Lift : PTyp Base -> PTyp Inter.

Check PTyp_ind.

Definition PTyp_ind2 : forall (s : S) (p : PTyp s)  (P : forall s : S, PTyp s -> Prop),
       P Base PInt ->
       (forall p : PTyp Inter,
        P Inter p -> forall p0 : PTyp Inter, P Inter p0 -> P Base (Fun p p0)) ->
       (forall p : PTyp Inter,
        P Inter p -> forall p0 : PTyp Inter, P Inter p0 -> P Inter (And p p0)) ->
       (forall p : PTyp Base, P Base p -> P Inter (Lift p)) ->
       P s p.
Proof.
intros.
apply PTyp_ind. auto. auto. auto. auto.
Defined.

Definition T (P : PTyp Inter -> Prop) : forall s, PTyp s -> Prop.
intros.
destruct s.
exact True.
exact (P H).
Defined.

Check (PTyp_ind2 Inter _ (T _)).

Definition PTyp_ind3 (p : PTyp Inter) (P : PTyp Inter -> Prop) := PTyp_ind2 Inter p (T P).

Check PTyp_ind3.

Definition PTyp_ind4 : 
       forall (p : PTyp Inter) (P : PTyp Inter -> Prop),
       (forall p0 : PTyp Inter,
        P p0 ->
        forall p1 : PTyp Inter, P p1 -> P (And p0 p1)) ->
       (forall p0 : PTyp Base, P (Lift p0)) ->
       P p.
Proof.
intros.
apply (PTyp_ind3 p). 
unfold T. auto.
intros. unfold T. auto.
auto.
unfold T.
intros.
apply H0.
Defined.

(*
Inductive PTyp A :=
  | Var : A -> PTyp A
  | PInt : PTyp A
  | Forall : (A -> PTyp A) -> PTyp A
  | Fun : PTyp A -> PTyp A -> PTyp A
  | And : PTyp A -> PTyp A -> PTyp A.
*)

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

Inductive sub : forall (s : S), PTyp s -> PTyp s -> Prop :=
  | SInt : sub Base (PInt) (PInt)
  | SFun : forall o1 o2 o3 o4, sub Inter o3 o1 -> sub Inter o2 o4 -> sub Base (Fun  o1 o2) (Fun  o3 o4)
  | SAnd1 : forall t t1 t2, sub Inter t t1 -> sub Inter t t2 -> sub Inter t (And  t1 t2)
  | SAnd2 : forall t t1 t2, sub Inter t1 t -> sub Inter (And  t1 t2) t
  | SAnd3 : forall t t1 t2, sub Inter t2 t -> sub Inter (And  t1 t2) t
  | SLift : forall t1 t2, sub Base t1 t2 -> sub Inter (Lift  t1) (Lift  t2).

(*
Definition prog s t1 t2 (s1 : sub s t1 t2) : Prop.
destruct t1.
exact True.
exact True.
exact ((*(exists u1 u2, s1 = SAnd1 (And t1_1 t1_2) _ _ u1 u2) \/*) (exists u, s1 = SAnd2 _ _ _ u) \/ (exists u, s1 = SAnd3 _ _ _ u)).
exact True.
Defined.

Lemma invAnd : forall s t x (u : sub s t x), prog s t x u.
Proof.
intros.
unfold prog.
destruct t.
auto.auto.
inversion u.

assert (t = And t1 t2).
admit.
rewrite H.
*)
(* Orthogonality: Implementation *)


Inductive Ortho : forall s, PTyp s -> PTyp s -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho Inter t1 t3 -> Ortho Inter t2 t3 -> Ortho Inter (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho Inter t1 t2 -> Ortho Inter t1 t3 -> Ortho Inter t1 (And t2 t3)
  | OLift : forall t1 t2, not (sub Base t1 t2) -> not (sub Base t2 t1) -> Ortho Inter (Lift t1) (Lift t2).

(* Orthogonality: Specification *)


Hint Resolve SInt SFun SAnd1 SAnd2 SAnd3 SLift.

Lemma reflex : forall s (t1 : PTyp s) , sub s t1 t1.
Proof.
induction t1; intros; auto.
Defined.

Definition OrthoS (s:S) (A B : PTyp s) := not (exists C, sub s A C /\ sub s B C).


Definition prog s (t2 : PTyp s) : Prop.
intros.
destruct s.
exact True.
exact ((exists t3, t2 = Lift t3) \/ (exists t3 t4, t2 = And t3 t4)).
Defined.

Print prog.

Lemma inv : 
  forall s (t2 : PTyp s), prog s t2.
intros; unfold prog.
destruct t2.
auto.
auto.
right.
exists t2_1.
exists t2_2.
reflexivity.
left.
exists t2.
reflexivity.
Defined.

Lemma invInter (t2 : PTyp Inter) : (exists t3 : PTyp Base, t2 = Lift t3) \/ (exists t3 t4 : PTyp Inter, t2 = And t3 t4).
unfold prog.
apply (inv Inter).
Defined.

Lemma ortho_completness : forall s (t1 t2 : PTyp s), (s = Inter) -> OrthoS s t1 t2 -> Ortho s t1 t2.
Proof.
induction t1; intros; unfold OrthoS in H.
(* Dummy cases *)
discriminate H.
discriminate H.
(* Case (t11 & t12) _|_ t2 *) 
apply OAnd1.
apply IHt1_1.
exact H.
unfold OrthoS in H0.
unfold OrthoS.
unfold not.
intro.
apply H0.
clear H0.
destruct H1. destruct H0.
exists x.
split.
apply SAnd2. exact H0.
exact H1.
apply IHt1_2.
exact H.
unfold OrthoS; unfold not; intro.
apply H0. clear H0.
destruct H1.
destruct H0.
exists x.
split.
apply SAnd3.
exact H0.
exact H1.
clear H.
clear IHt1.
(* Make a separate Lemma ? *)
generalize H0. clear H0.
apply (PTyp_ind4 t2).
intros.
apply OAnd2.
apply H.
unfold OrthoS. unfold not. intro.
apply H1.
destruct H2. destruct H2.
exists x.
split.
exact H2.
apply SAnd2.
exact H3.
apply H0.
unfold OrthoS. unfold not. intro.
apply H1.
destruct H2. destruct H2.
exists x.
split.
exact H2.
apply SAnd3.
exact H3.
(* Last case *)
intros.
apply OLift.
unfold not. intros.
apply H0.
exists (Lift p0).
split.
apply SLift.
apply H.
(*case 2*)
apply SLift.
apply reflex.
(*case 3*)
unfold not. intros.
apply H0.
exists (Lift t1).
split.
apply reflex.
apply SLift.
exact H.
Defined.

Definition SubEither s t1 t2 := sub s t1 t2 \/ sub s t2 t1.

Lemma ortho_aux : forall s (t1 t2 : PTyp s), (s = Base) -> not (sub s t1 t2 /\ sub s t2 t1) -> OrthoS s t1 t2.
intros.
unfold not in H0.
unfold OrthoS. unfold not.
intros.
apply H0. clear H0.
induction t1; split; try (discriminate H); intros.
destruct H1.
destruct H0.
inversion H0.
assert (PInt = x). admit. rewrite <- H3 in H0. rewrite <- H3 in H1. clear H2.
inversion H1.
assert (PInt = t2). admit. rewrite <- H4 in H1. rewrite <- H4. apply reflex.
admit. (* Similar to previous one *)
clear IHt1_1. clear IHt1_2.
destruct H1. destruct H0.
inversion H0.
assert (Fun o3 o4 = x). admit. rewrite <- H7 in H0. rewrite <- H7 in H1. clear H4. clear H7.
inversion H1.
assert (Fun o0 o5 = t2). admit. rewrite <- H7 in H0. rewrite <- H7 in H1. clear H4. clear H7.

Lemma ortho_soundness : forall s (t1 t2 : PTyp s), (s = Inter) -> Ortho s t1 t2 -> OrthoS s t1 t2.
induction t1; intros. discriminate H. discriminate H. admit.
clear IHt1. generalize H0. clear H0. intros. unfold OrthoS. unfold not. intros.

 apply (PTyp_ind4 t2); intros. 
unfold OrthoS. unfold not. intros.
destruct H3. destruct H3.
unfold OrthoS in H0. unfold not in H1.
unfold OrthoS in H1. unfold not in H1.
admit.
unfold OrthoS. unfold not. intros.
destruct H1.
destruct H1.
inversion H0.
inversion H1.


Lemma ortho_soundness : forall s (t1 t2 : PTyp s), (s = Inter) -> OrthoS s t1 t2 -> Ortho s t1 t2.
Proof.
induction t1; intros; unfold OrthoS in H.
(* Dummy cases *)
discriminate H.
discriminate H.
(* Case (t11 & t12) _|_ t2 *) 
apply OAnd1.
apply IHt1_1.
exact H.
unfold OrthoS in H0.
unfold OrthoS.
unfold not.
intro.
apply H0.
clear H0.
destruct H1. destruct H0.
exists x.
split.
apply SAnd2. exact H0.
exact H1.
apply IHt1_2.
exact H.
unfold OrthoS; unfold not; intro.
apply H0. clear H0.
destruct H1.
destruct H0.
exists x.
split.
apply SAnd3.
exact H0.
exact H1.
clear H.
clear IHt1.
(* Make a separate Lemma ? *)
unfold OrthoS in H0. unfold not in H0.
assert ((exists t3 : PTyp Base, t2 = Lift t3) \/ (exists t3 t4 : PTyp Inter, t2 = And t3 t4)).
apply invInter.
destruct H. destruct H.
rewrite H.
apply OLift.
unfold not; intros.
apply H0.
exists (Lift x).
rewrite H.
split.
apply SLift.
apply H1.
apply reflex.
(*case 2*)
unfold not; intros.
apply H0.
exists (Lift t1).
rewrite H.
split.
apply reflex.
apply SLift.
exact H1.
(* Part 2 *)
destruct H. destruct H.
rewrite H.
apply OAnd2.
rewrite H in H0.
admit.
admit.
Defined.


Lemma ortho_soundness : forall s (t1 t2 : PTyp s), (s = Inter) -> OrthoS s t1 t2 -> Ortho s t1 t2.
Proof.
induction t1; intros; unfold OrthoS in H.
(* Dummy cases *)
discriminate H.
discriminate H.
(* Case (t11 & t12) _|_ t2 *) 
apply OAnd1.
apply IHt1_1.
exact H.
unfold OrthoS in H0.
unfold OrthoS.
unfold not.
intro.
apply H0.
clear H0.
destruct H1. destruct H0.
exists x.
split.
apply SAnd2. exact H0.
exact H1.
apply IHt1_2.
exact H.
unfold OrthoS; unfold not; intro.
apply H0. clear H0.
destruct H1.
destruct H0.
exists x.
split.
apply SAnd3.
exact H0.
exact H1.
clear H.
clear IHt1.
(* Make a separate Lemma ? *)
unfold OrthoS in H0. unfold not in H0.
(*
assert ((exists t3 : PTyp Base, t2 = Lift t3) \/ (exists t3 t4 : PTyp Inter, t2 = And t3 t4)).
apply invInter.*)
assert (exists t3, t2 = Lift t3).
admit. (* How to do this? *)
destruct H.
rewrite H.
apply OLift.
unfold not; intros.
apply H0.
exists (Lift x).
rewrite H.
split.
apply SLift.
apply H1.
apply reflex.
(*case 2*)
unfold not; intros.
apply H0.
exists (Lift t1).
rewrite H.
split.
apply reflex.
apply SLift.
exact H1.
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
