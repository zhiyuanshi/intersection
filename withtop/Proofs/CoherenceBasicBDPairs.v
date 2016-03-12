Require Import String.
Require Import STLC.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.

Module CoherenceBasicBDPairs
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  
Module ST := TLC(VarTyp)(set).
Import ST.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the correnposing lemmas/theorems in the paper. 
The reader can just look for:

Lemma 5

for example, to look for the proof of lemma 5 in the paper.

All lemmas and theorems are complete: there are no uses of admit or Admitted. 

*)

(* Our calculus: *)

(* Types *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | Pair : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp.

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | Pair t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
  end.

(* Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2)
  | APair : forall t1 t2, Atomic (Pair t1 t2).

Inductive sub : PTyp -> PTyp -> Exp -> Prop :=
  | SInt : sub PInt PInt (fun A => STLam' _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun o3 o4) (fun A => STLam' _ (STLam' _ (STApp _ (c2 A) (STApp _ (STBVar _ 1) (STApp _ (c1 A) (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (fun A => STLam' _
       (STPair _ (STApp _ (c1 A) (STBVar _ 0)) (STApp _ (c2 A) (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam' _ 
       ((STApp _ (c A) (STProj1 _ (STBVar _ 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam' _ 
       ((STApp _ (c A) (STProj2 _ (STBVar _ 0)))))
  | SPair : forall t11 t12 t21 t22 c1 c2,
               sub t11 t21 c1 ->
               sub t12 t22 c2 ->
               sub (Pair t11 t12) (Pair t21 t22)
                   (fun A => STLam' _ (STPair _
                                             (STApp _ (c1 A) (STProj1 _ (STBVar _ 0)))
                                             (STApp _ (c2 A) (STProj2 _ (STBVar _ 0))))).

Hint Constructors sub.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:Exp), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (fun A => STLam' _ (STBVar _ 0)). 
exact SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (fun A => STLam' _ ( 
       STLam' _ (STApp _ (x0 A) (STApp _ (STBVar _ 1) (STApp _ (x A) (STBVar _ 0)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (fun A => STLam' _ (
       STPair _ (STApp _ (x A) (STBVar _ 0)) (STApp _ (x0 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros t t1 t2 H H0. destruct t. destruct H.
exists (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto. destruct H.
exists (fun A => STLam' _ (
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto. destruct H.
exists (fun A => STLam' _ (
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))).
apply SAnd2; auto.
inversion H0.
Defined.

(* The No loss of Expressivity Lemmas *)

(* Theorem 3 *)

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
intro t.
induction t; intros.
(* Case PInt *)
apply sand2_atomic. auto. exact AInt.
(* Case Fun *)
apply sand2_atomic. auto. apply AFun.
(* Case Pair *)
apply sand2_atomic. auto. apply APair.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
exists (fun A => STLam' _ (
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And t1 t2) t.
unfold Sub. intros t t1 t2 H H0. destruct t. destruct H.
exists (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto. destruct H.
exists (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto. destruct H.
exists (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto.
inversion H0.
Defined.

(* Theorem 4 *)

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
intros t; induction t; intros.
(* Case PInt *)
apply sand3_atomic. auto. exact AInt.
(* Case Fun *)
apply sand3_atomic. auto. apply AFun.
(* Case Pair *)
apply sand3_atomic. auto. apply APair.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
exists (fun A => STLam' _ (
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
Defined.

Definition spair : forall t11 t12 t21 t22, Sub t11 t21 -> Sub t12 t22 -> Sub (Pair t11 t12) (Pair t21 t22).
  unfold Sub; intros; destruct H; destruct H0.
exists (fun A => STLam' _ (STPair _
                                             (STApp _ (x A) (STProj1 _ (STBVar _ 0)))
                                             (STApp _ (x0 A) (STProj2 _ (STBVar _ 0))))).
apply SPair; assumption.
Defined.

(* Disjointness: Implementation *)

(* TODO add hd connective *)

Definition head : PTyp -> nat :=
  fun t =>
    match t with
      | PInt => 0
      | Fun t1 t2 => 1 
      | Pair t1 t2 => 2
      | And t1 t2 => 3
    end.

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OPair1 : forall t1 t2 t3 t4, Ortho t1 t2 -> Ortho (Pair t1 t3) (Pair t2 t4)
  | OPair2 : forall t1 t2 t3 t4, Ortho t3 t4 -> Ortho (Pair t1 t3) (Pair t2 t4)           
  | OHd : forall t1 t2, not (head t1 = head t2) -> not (head t1 = 3) -> not (head t2 = 3) -> Ortho t1 t2.

Hint Constructors Ortho.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFPair : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Pair t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2).

Hint Constructors WFTyp.

(* Reflexivity *)
Hint Resolve sint sfun sand1 sand2 sand3 spair.

Lemma reflex : forall (t1 : PTyp), Sub t1 t1.
Proof.
induction t1; intros; auto.
Defined.

(* Disjointness algorithm is complete: Theorem 7 *)

Lemma ortho_completness : forall (t1 t2 : PTyp), OrthoS t1 t2 -> Ortho t1 t2.
Proof.
induction t1; intros; unfold OrthoS in H.
(* Case PInt *)
induction t2; auto.
destruct H. exists PInt. split; apply reflex.
apply OHd; unfold not; intros HInv; inversion HInv.
apply OHd; unfold not; intros HInv; inversion HInv.
apply OAnd2. 
apply IHt2_1. unfold not. unfold not in H. intros; apply H.
destruct H0. destruct H0. 
exists x. split. exact H0. apply sand2. exact H1.
apply IHt2_2. unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0. exists x.
split. auto. apply sand3.
auto.
(* Case Fun t1 t2 *)
induction t2.
apply OHd; unfold not; intros HInv; inversion HInv.
apply OFun.
apply IHt1_2. unfold OrthoS. unfold not. intros.
unfold not in H. apply H.
destruct H0. destruct H0.
exists (Fun (And t1_1 t2_1) x).
split.
apply sfun.
apply sand2.
apply reflex.
auto.
apply sfun.
apply sand3. apply reflex.
auto.
apply OHd; unfold not; intros HInv; inversion HInv.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2.
apply IHt2_1.
unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0.
exists x. split. auto. apply sand2. exact H1.
apply IHt2_2.
unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0.
exists x. split. auto. apply sand3. exact H1.
(* Case (t11 x t12) _|_ t2 *)
induction t2; try now (apply OHd; unfold not; intros HInv; inversion HInv).
assert (Ha : not (exists C : PTyp, Sub (Pair t1_1 t1_2) C /\ Sub (Pair t2_1 t2_2) C) ->
             not (exists C : PTyp, Sub t1_1 C /\ Sub t2_1 C) \/
             not (exists C : PTyp, Sub t1_2 C /\ Sub t2_2 C)). 
intros HNot.
apply Classical_Prop.not_and_or.
unfold not; intros HH; apply HNot.
inversion HH.
inversion H0.
inversion H1.
exists (Pair x x0).
unfold Sub.
split.
inversion H2.
inversion H3.
inversion H4.
inversion H6.
eexists.
apply SPair.
apply H8.
apply H9.
inversion H2.
inversion H3.
inversion H5.
inversion H7.
eexists.
apply SPair.
apply H8.
apply H9.
apply Ha in H.
inversion H.
apply OPair1.
apply IHt1_1.
unfold OrthoS; unfold not; intros.
apply H0; assumption.
apply OPair2.
apply IHt1_2.
unfold OrthoS; unfold not; intros.
apply H0; assumption.
apply OAnd2.
apply IHt2_1.
unfold not; unfold not in H; intros; apply H.
destruct H0; destruct H0.
exists x. split. auto. apply sand2. exact H1.
apply IHt2_2.
unfold not; unfold not in H; intros; apply H.
destruct H0; destruct H0.
exists x. split. auto. apply sand3. exact H1.
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
apply sand2. exact H.
exact H0.
apply IHt1_2.
unfold OrthoS; unfold not; intro. unfold not in H.
apply H. clear H.
destruct H0.
destruct H.
exists x.
split.
apply sand3.
exact H.
exact H0.
Defined.

Lemma nosub : forall t1 t2, OrthoS t1 t2 -> not (Sub t1 t2) /\ not (Sub t2 t1).
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


Lemma invAndS1 : forall t t1 t2, Sub t (And t1 t2) -> Sub t t1 /\ Sub t t2.
Proof.
intro t; induction t; intros.
(* Case Int *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
(* Case Fun *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
(* Case Pair *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
(* Case And *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
assert (Sub t1 t0 /\ Sub t1 t3).
apply IHt1.
auto. unfold Sub. exists c. auto.
destruct H7.
split.
apply sand2.
auto.
apply sand2.
auto.
assert (Sub t2 t0 /\ Sub t2 t3).
apply IHt2.
unfold Sub. exists c. auto.
destruct H7.
split.
apply sand3.
auto.
apply sand3.
auto.
Defined.

(* Unique subtype contributor: Lemma 4 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> Sub (And A B) C -> not (Sub A C /\ Sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. apply H. exists C. auto.
Defined.

(* Lemmas needed to prove soundness of the disjointness algorithm *)

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
- inversion H1. inversion H3. unfold OrthoS in H. apply H. exists (PInt). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (PInt). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
- inversion H1. inversion H3. unfold OrthoS in H. apply H. exists (Fun x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (Fun x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
- inversion H1. inversion H3. unfold OrthoS in H. apply H. exists (Pair x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (Pair x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
- assert (Sub C x1 /\ Sub C x2). apply invAndS1. auto. destruct H3.
inversion H1. inversion H5. apply IHx1. 
unfold Sub. exists c1. auto. unfold Sub.  unfold Sub in H3. destruct H3. exists x0. auto.
unfold OrthoS in H. apply H. exists (And x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (And x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
Defined.

Lemma orthosIntFun : forall t1 t2, OrthoS PInt (Fun t1 t2).
Proof.
  unfold OrthoS; unfold not; intros t1 t2 H.
  destruct H as [x [[c1 s1] [c2 s2]]].
  generalize dependent c1.
  generalize dependent c2.
  induction x; intros.
  inversion s2.
  inversion s1.
  inversion s1.
  inversion s2; subst.
  inversion s1; subst.
  eapply IHx1.
  apply H2.
  apply H3.
Qed.

Lemma orthosIntPair : forall t1 t2, OrthoS PInt (Pair t1 t2).
Proof.
  unfold OrthoS; unfold not; intros t1 t2 H.
  destruct H as [x [[c1 s1] [c2 s2]]].
  generalize dependent c1.
  generalize dependent c2.
  induction x; intros.
  inversion s2.
  inversion s1.
  inversion s1.
  inversion s2; subst.
  inversion s1; subst.
  eapply IHx1.
  apply H2.
  apply H3.
Qed.

Lemma orthosFunPair : forall t1 t2 t3 t4, OrthoS (Fun t1 t2) (Pair t3 t4).
Proof.
  unfold OrthoS; unfold not; intros t1 t2 t3 t4 H.
  destruct H as [x [[c1 s1] [c2 s2]]].
  generalize dependent c1.
  generalize dependent c2.
  induction x; intros.
  inversion s2.
  inversion s2.
  inversion s1.
  inversion s1; subst.
  inversion s2; subst.
  eapply IHx1.
  apply H3.
  apply H2.
Qed.
  
(* Soundness of the disjointness algorithm: Theorem 6 *)

Lemma ortho_soundness : forall (t1 t2 : PTyp), Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(* Hard case *)
- apply ortho_and; auto.
- assert (OrthoS t2 t1). apply ortho_sym. apply IHOrtho1; auto.
assert (OrthoS t3 t1). apply ortho_sym. apply IHOrtho2; auto.
apply ortho_sym.
apply ortho_and; auto.
(* Case FunFun *)
- unfold OrthoS. unfold not. intros.
unfold OrthoS in IHOrtho. apply IHOrtho.
destruct H0. destruct H0. generalize H0. generalize H1. clear H0. clear H1.
induction x; intros. inversion H1. inversion H2. exists x2.
split. inversion H0. inversion H2. unfold Sub. exists c2. auto. unfold Sub. inversion H1. inversion H2. exists c2. auto.
inversion H1; inversion H2.
apply IHx1.
inversion H1. inversion H2. unfold Sub. exists c1. auto. 
inversion H0. inversion H2. exists c1. auto.
- unfold OrthoS in *; unfold not; intros.
  inversion H0; inversion H1; clear H1.
  induction x; try (now inversion H2; inversion H1).
  inversion H2; inversion H3.
  inversion H1; inversion H4.
  subst.
  apply IHOrtho; exists x1.
  unfold Sub; split; intros.
  exists c1; assumption.
  exists c0; assumption.
  inversion H2; inversion H1.
  inversion H3; inversion H10.
  apply IHx1; unfold Sub.
  exists c1; auto.
  exists c0; auto.
- unfold OrthoS in *; unfold not; intros.
  inversion H0; inversion H1; clear H1.
  induction x; try (now inversion H2; inversion H1).
  inversion H2; inversion H3.
  inversion H1; inversion H4.
  subst.
  apply IHOrtho; exists x2.
  unfold Sub; split; intros.
  exists c2; assumption.
  exists c3; assumption.
  inversion H2; inversion H1.
  inversion H3; inversion H10.
  apply IHx1; unfold Sub.
  exists c1; auto.
  exists c0; auto.
- destruct t1; intros.
  destruct t2.
  exfalso; apply H; auto.
  apply orthosIntFun.
  apply orthosIntPair.
  exfalso; apply H1; auto.
  destruct t2.
  pose (orthosIntFun t1_1 t1_2) as HH; now apply ortho_sym in HH.
  exfalso; apply H; auto.
  apply orthosFunPair.
  exfalso; apply H1; auto.
  destruct t2.
  pose (orthosIntPair t1_1 t1_2) as HH; now apply ortho_sym in HH.
  pose (orthosFunPair t2_1 t2_2 t1_1 t1_2) as HH; now apply ortho_sym in HH.
  exfalso; apply H; auto.
  exfalso; apply H1; auto.
  exfalso; apply H0; auto.
Qed.

(* Coercive subtyping is coeherent: Lemma 5 *)

Lemma sub_coherent : forall {A}, WFTyp A -> forall {B}, WFTyp B -> forall {C1}, sub A B C1 -> forall {C2}, sub A B C2 -> C1 = C2.
Proof.
intro. intro. intro. intro. intro. intro.
induction H1; intros.
(* Case: Int <: Int *)
- inversion H1; reflexivity.
(* Case: Fun t1 t2 <: Fun t3 t4 *)
- inversion H1; inversion H; inversion H0.
  assert (c2 = c3). apply IHsub2; auto.
  assert (c1 = c0). apply IHsub1; auto.
  rewrite H17. rewrite H18.
  reflexivity.
(* Case: t <: And t1 t2 *) 
- inversion H1; inversion H0.
  assert (c1 = c0). apply IHsub1; auto.
  assert (c2 = c3). apply IHsub2; auto.
  rewrite H13. rewrite H14.
  reflexivity.
  (* different coercion case*)
  inversion H3.
  (* different coercion case*)
  inversion H3.
(* Case: And t1 t2 <: t (first) *)
- inversion H3; inversion H.
  (* different coercion *)
  rewrite <- H7 in H2. inversion H2.
  (* same coercion *)
  assert (c = c0). apply IHsub; auto. rewrite H15.
  reflexivity.
  (* contradiction: not orthogonal! *)
  destruct H14. exists t0. unfold Sub.
  split. exists c; auto. exists c0. auto.
(* Case: And t1 t2 <: t (second) *)
- inversion H3; inversion H.
  rewrite <- H7 in H2. inversion H2.
  (* contradiction: not orthogonal! *)
  destruct H14. exists t0. unfold Sub.
  split. exists c0; auto. exists c. auto.
  (* same coercion; no contradiction *)
  assert (c = c0). apply IHsub; auto. rewrite H15.
  reflexivity.
(* Case: Pair t1 t2 <: Pair t3 t4 *)
- inversion H1; subst.
  rewrite IHsub1 with (C2 := c0); auto.
  rewrite IHsub2 with (C2 := c3); auto.
  now inversion H.
  now inversion H0.
  now inversion H.
  now inversion H0.
Defined.


(* typing rules of lambda i *)

Module EqFacts := BoolEqualityFacts(VarTyp).

(* Definitions borrowed from STLC_Tutorial *)

(* Our source language *)
Inductive PExp :=
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp                   
  | PLit   : nat -> PExp
  | PLam   : PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp
  | PPair  : PExp -> PExp -> PExp
  | PAnn   : PExp -> PTyp -> PExp. (* only for the algorithmic version *) 

(* Free variables *)

(** Source language **)
Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
    | PFVar v => singleton v
    | PBVar _ => empty
    | PLit _ => empty
    | PLam t => fv_source t
    | PApp t1 t2 => union (fv_source t1) (fv_source t2)
    | PMerge t1 t2 => union (fv_source t1) (fv_source t2)
    | PPair t1 t2 => union (fv_source t1) (fv_source t2)
    | PAnn t1 A => fv_source t1
  end.


(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  let C := gather_vars_with (fun (x : context PTyp) => dom x) in
  let D := gather_vars_with (fun (x : context STyp) => dom x) in
  let E := gather_vars_with (fun x : PExp => fv_source x) in
  let F := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union C (union D (union E F))))).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i      => if Nat.eqb k i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x                     
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PPair t1 t2  => PPair (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  end.

Definition open_source t u := open_rec_source 0 u t.


(* Functions on contexts *)

Definition conv_context (env : context PTyp) : context STyp :=
  mapctx ptyp2styp env.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).

Lemma ok_map : forall Gamma, ok Gamma -> ok (∥ Gamma ∥).
Proof.
  intros.
  induction H.
  simpl; auto.
  unfold conv_context, mapctx in *.
  unfold extend.
  rewrite map_app.
  simpl.
  apply Ok_push.
  assumption.
  simpl.
  change (map (fun p : var * PTyp => (fst p, | snd p |)) E) with (mapctx ptyp2styp E).
  erewrite <- dom_map_id.
  assumption.
Defined.

Lemma fv_source_distr :
  forall t1 t2 x n, In x (fv_source (open_rec_source n t2 t1)) ->
               In x (union (fv_source t1) (fv_source t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; rewrite union_spec in *; auto.
  - destruct (Nat.eqb n0 n); auto. 
  - rewrite <- union_spec.
    eapply IHt1.
    apply H.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite union_spec.
    inversion H.
    rewrite or_comm at 1.
    rewrite <- or_assoc.
    left; rewrite or_comm; rewrite <- union_spec.
    eapply IHt1_1; apply H0.
    rewrite or_assoc.
    right; rewrite <- union_spec.
    eapply IHt1_2; apply H0.
  - rewrite <- union_spec.
    eapply IHt1; apply H.
Defined.
  
(* Typing rules of source language: Figure 2 
Note that we generate an Annotated expression, which serves as evidence for bi-directional
type-checking completness proof.
 *)

(* Declarative type system *)

Inductive has_type_source : context PTyp -> PExp -> PTyp -> PExp -> Prop :=
  | TyVar : forall Gamma x ty,
            ok Gamma -> 
            List.In (x,ty) Gamma ->
            WFTyp ty ->
            has_type_source Gamma (PFVar x) ty (PFVar x)
  | TyLit : forall Gamma x, ok Gamma -> has_type_source Gamma (PLit x) PInt (PLit x)
  | TyLam : forall L Gamma t t1 A B, (forall x, not (In x L) -> 
                                  has_type_source (extend x A Gamma) (open_source t (PFVar x)) B (open_source t1 (PFVar x))) ->
                           WFTyp A ->  
                           has_type_source Gamma (PLam t) (Fun A B) (PAnn (PLam t1) (Fun A B)) 
  | TyApp : forall Gamma A B t1 t1' t2 t2' ,
              has_type_source Gamma t1 (Fun A B) t1' ->
              has_type_source Gamma t2 A t2' ->
              has_type_source Gamma (PApp t1 t2) B (PApp t1' t2')
  | TyMerge : forall Gamma A B t1 t1' t2 t2' ,
                has_type_source Gamma t1 A t1' ->
                has_type_source Gamma t2 B t2' ->
                OrthoS A B ->
                has_type_source Gamma (PMerge t1 t2) (And A B) (PMerge t1' t2')
  | TyPair : forall Gamma A B t1 t1' t2 t2',
               has_type_source Gamma t1 A t1' ->
               has_type_source Gamma t2 B t2' ->
               has_type_source Gamma (PPair t1 t2) (Pair A B) (PPair t1' t2')
  | TySub : forall Gamma t t' A B,
              has_type_source Gamma t A t' ->
              Sub A B ->
              WFTyp B ->
              has_type_source Gamma t B (PAnn t' B).

Hint Constructors has_type_source.

Inductive PTerm : PExp -> Prop :=
  | PTerm_Var : forall x,
      PTerm (PFVar x)
  | PTerm_Lit : forall n,
      PTerm (PLit n)
  | PTerm_Lam : forall L t1,
      (forall x, not (In x L) -> PTerm (open_source t1 (PFVar x))) ->
      PTerm (PLam t1)
  | PTerm_App : forall t1 t2,
      PTerm t1 -> 
      PTerm t2 -> 
      PTerm (PApp t1 t2)
  | PTerm_Merge : forall t1 t2,
      PTerm t1 ->
      PTerm t2 ->
      PTerm (PMerge t1 t2)
  | PTerm_Pair : forall t1 t2,
      PTerm t1 ->
      PTerm t2 ->
      PTerm (PPair t1 t2)
  | PTerm_Ann : forall e t,
      PTerm e ->
      PTerm (PAnn e t).  

Hint Constructors PTerm.
  
Lemma open_rec_term_source_core :forall t j v i u, i <> j ->
  open_rec_source j v t = open_rec_source i u (open_rec_source j v t) ->
  t = open_rec_source i u t.
Proof.
  intro t; induction t; intros; simpl.
  - reflexivity.
  - simpl in *.
    case_eq (Nat.eqb i n); intros.
    case_eq (Nat.eqb j n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    rewrite H2 in H0.
    unfold open_rec_source in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
  - reflexivity.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2. 
Qed.

Lemma open_rec_source_term : forall t u,
  PTerm t -> forall k, t =  open_rec_source k u t.
Proof.
  induction 1; intros; simpl; auto.
  pick_fresh x.
  rewrite <- open_rec_term_source_core with (j := 0) (v := PFVar x).
  reflexivity.
  auto.
  simpl.
  unfold open_source in *.
  rewrite <- H0.
  reflexivity.
  not_in_L x.
  rewrite <- IHPTerm1.
  rewrite <- IHPTerm2.
  reflexivity.
  rewrite <- IHPTerm1.
  rewrite <- IHPTerm2.
  reflexivity.
  rewrite <- IHPTerm1.
  rewrite <- IHPTerm2.
  reflexivity.
  rewrite <- IHPTerm.
  reflexivity.
Qed.


Fixpoint subst_source (z : var) (u : PExp) (t : PExp) {struct t} : PExp :=
  match t with 
    | PBVar i      => PBVar i
    | PFVar x      => if VarTyp.eqb x z then u else (PFVar x)
    | PLit i       => PLit i
    | PLam t1      => PLam (subst_source z u t1)
    | PApp t1 t2   => PApp (subst_source z u t1) (subst_source z u t2)
    | PMerge t1 t2 => PMerge (subst_source z u t1) (subst_source z u t2)
    | PPair t1 t2  => PPair (subst_source z u t1) (subst_source z u t2)
    | PAnn t1 t2   => PAnn (subst_source z u t1) t2 
  end.


Lemma subst_source_fresh : forall t x u, 
  not (In x (fv_source t)) -> subst_source x u t = t.
Proof.
  intro t.
  induction t; intros; auto.
  (* Case PFVar *)
  simpl.
  remember (v =? x) as H1.
  destruct H1.
  exfalso.
  apply H.
  simpl.
  apply singleton_spec.
  symmetry in HeqH1.
  apply eqb_eq in HeqH1; symmetry; assumption.
  reflexivity.
  (* Case PLam *)
  simpl in *.
  rewrite IHt; auto.
  (* Case PApp *)
  simpl in *; rewrite IHt1, IHt2; auto; unfold not in *; intros;
  apply H; apply union_spec; [ right | left ]; auto.
  (* Case PMerge *)
  simpl in *; rewrite IHt1, IHt2; auto; unfold not in *; intros;
  apply H; apply union_spec; [ right | left ]; auto.
  (* Case PPair *)
  simpl in *; rewrite IHt1, IHt2; auto; unfold not in *; intros;
  apply H; apply union_spec; [ right | left ]; auto.  
  (* Case PAnn *)
  simpl in *; rewrite IHt; auto.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_source_open : forall x u t1 t2, PTerm u -> 
  subst_source x u (open_source t1 t2) = open_source (subst_source x u t1) (subst_source x u t2).
Proof.
  intros. unfold open_source. generalize 0.
  induction t1; intros; simpl.
  - case_eq (eqb v x); intros.
    rewrite <- open_rec_source_term; auto.
    simpl; reflexivity.
  - case_eq (Nat.eqb n0 n); intros; auto.
  - reflexivity.
  - rewrite IHt1; reflexivity.
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  - rewrite IHt1; reflexivity.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_source_open_var : forall (x y : var) u t, not (x == y) -> PTerm u ->
  open_source (subst_source x u t) (PFVar y) = subst_source x u (open_source t (PFVar y)).
Proof.
  intros. rewrite subst_source_open. simpl.
  case_eq (eqb y x); intros.
  apply eqb_eq in H1.
  exfalso; apply H; symmetry. assumption.
  reflexivity.
  assumption.
Qed.
  
(** Opening up an abstraction of body [t] with a term [u] is the same as opening
  up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)

Lemma subst_source_intro : forall x t u, 
  not (In x (fv_source t)) -> PTerm u ->
  open_source t u = subst_source x u (open_source t (PFVar x)).
Proof.
  intros.
  rewrite subst_source_open; [ | assumption ].
  rewrite subst_source_fresh; [ | assumption ].
  simpl.
  case_eq (eqb x x); intros.
  reflexivity.
  rewrite EqFacts.eqb_neq in H1.
  exfalso.
  apply H1.
  reflexivity.
Qed.

Lemma subst_fresh_var :
  forall x z t, not (In x (fv_source t)) ->
           subst_source x (PFVar z) (open_source t (PFVar x)) = open_source t (PFVar z).
Proof.
  intros x z t H1.
  rewrite subst_source_open.
  simpl.
  case_eq (x =? x); intros HEq.
  rewrite subst_source_fresh.
  reflexivity.
  auto.
  exfalso; apply EqFacts.eqb_neq in HEq; apply HEq; reflexivity.
  apply PTerm_Var.
Qed.
  
(* ********************************************************************** *)
(** ** Preservation of local closure *)

(** The goal of this section is to set up the appropriate lemmas 
    for proving goals of the form [term t]. First, we defined a
    predicate capturing that a term [t] is the body of a locally
    closed abstraction. *)

Definition body_source t :=
  exists L, forall x, not (In x L) -> PTerm (open_source t (PFVar x)).

(** We then show how to introduce and eliminate [body t]. *)

Lemma term_abs_to_body_source : forall t1, 
  PTerm (PLam t1) -> body_source t1.
Proof.
  intros; unfold body_source; inversion H; subst; exists L; assumption.
Qed.

Lemma body_source_to_term_abs : forall t1, 
  body_source t1 -> PTerm (PLam t1).
Proof. intros. inversion H. apply_fresh PTerm_Lam as x. apply H0.
       unfold not in *. intros; apply Fry; apply union_spec; auto.
Qed.

(* Hint Resolve term_abs_to_body body_to_term_abs. *)

(** We prove that terms are stable by substitution *)

Lemma subst_source_term : forall t z u,
  PTerm u -> PTerm t -> PTerm (subst_source z u t).
Proof.
  induction 2; simpl; auto.
  destruct (eqb x z).
  assumption.
  (* Var *)
  - apply PTerm_Var.
  (* Lam *)
  - apply_fresh PTerm_Lam as x.
    rewrite subst_source_open_var.
    apply H1. unfold not in *.
    intros; apply Frx.
    apply union_spec; left.
    apply union_spec; left.
    apply union_spec; left.
    assumption.
    unfold not in *; intros; apply Frx.
    apply union_spec; left.
    apply union_spec; left.
    apply union_spec; right.
    apply singleton_spec.
    symmetry; assumption.
    assumption.
Qed.

Hint Resolve subst_source_term.
 

Lemma type_correct_source_terms : forall Gamma E ty e, has_type_source Gamma E ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Qed.

Lemma type_correct_source_terms' : forall Gamma E ty e, has_type_source Gamma e ty E -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply PTerm_Ann.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Qed.

Lemma typing_wf_source :
  forall Gamma t T E, has_type_source Gamma t T E -> WFTyp T.
Proof.
  intros Gamma t  T E H.
  induction H; auto.
  pick_fresh x.
  assert (Ha : not (M.In x L)) by (not_in_L x).
  apply WFFun.
  apply H in Ha.
  assumption.
  apply H0 with (x := x); assumption.
  inversion IHhas_type_source1; assumption.
Qed.

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import MSetProperties.
Module MSetProperties := WPropertiesOn(VarTyp)(M).

Lemma typing_weaken_source : forall G E F t T d,
   has_type_source (E ++ G) t T d -> 
   ok (E ++ F ++ G) ->
   has_type_source (E ++ F ++ G) t T d.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply TyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
    assumption.
  (* STTyLam *)
  - unfold extend in *.
    apply_fresh TyLam as x.
    unfold open in *; simpl in *.
    unfold extend.
    rewrite app_assoc.
    apply H0.
    not_in_L x.
    rewrite HeqH'.
    rewrite <- app_assoc.
    reflexivity.
    rewrite <- app_assoc.
    apply Ok_push.
    assumption.
    repeat (rewrite dom_union; rewrite union_spec).
    repeat rewrite union_spec in Frx.
    repeat rewrite or_assoc in *.
    unfold not; intro HInv; destruct HInv as [HInv | [HInv | HInv]]; apply Frx; auto 8.
    assumption.
Defined.

Lemma typing_strengthen_source : forall z U E F t T d,
  not (In z (fv_source t)) ->
  has_type_source (E ++ ((z,U) :: nil) ++ F) t T d ->
  has_type_source (E ++ F) t T d.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - subst; apply TyVar.
    now apply ok_remove in H0.
    apply in_or_app.
    repeat apply in_app_or in H1.
    inversion H1.
    auto.
    apply in_app_or in H3.
    inversion H3.
    inversion H4.
    inversion H5.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H5.
    auto.
    assumption.
  - apply TyLit.
    subst.
    now apply ok_remove in H0.

  - subst.
    apply_fresh TyLam as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_source_distr in H3.
    rewrite union_spec in H3.
    inversion H3.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H4.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H4.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
    assumption.
  - eapply TyApp.
    subst.
    apply IHhas_type_source1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHhas_type_source2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply TyMerge.
    apply IHhas_type_source1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_source2; simpl in *; not_in_L z; reflexivity.
    assumption.
  - subst.
    apply TyPair.
    apply IHhas_type_source1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_source2; simpl in *; not_in_L z; reflexivity.
  - subst.
    eapply TySub.
    apply IHhas_type_source.
    assumption.
    reflexivity.
    apply H1.
    assumption.
Qed.    

Lemma typing_source_ok_env : forall Gamma E ty e, has_type_source Gamma E ty e -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Qed.
  
  
Definition has_type Gamma e t := exists s, has_type_source Gamma e t s.

Definition tvar :
  forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma -> WFTyp ty -> has_type Gamma (PFVar x) ty.
intros.  unfold has_type. exists (PFVar x). auto.
Defined.

Definition tlit : forall Gamma x, ok Gamma -> has_type Gamma (PLit x) PInt.
intros. unfold has_type. exists (PLit x); auto.
Defined.

Fixpoint subst (z : var) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
  match t with
    | STBVar _ i     => STBVar _ i
    | STFVar _ x     => if VarTyp.eqb x z then u else (STFVar _ x)
    | STLit _ i      => STLit _ i
    | STLam _ A t1   => STLam _ A (subst z u t1)
    | STLam' _ t1    => STLam' _ (subst z u t1)
    | STApp _ t1 t2  => STApp _ (subst z u t1) (subst z u t2)
    | STPair _ t1 t2 => STPair _ (subst z u t1) (subst z u t2)
    | STProj1 _ t    => STProj1 _ (subst z u t)
    | STProj2 _ t    => STProj2 _ (subst z u t)
    | STUnit _       => STUnit _
  end.


Lemma fv_source_distr_open_l :
  forall t1 t2 x n, In x (fv_source t1) ->
               In x (fv_source t2) ->
               In x (fv_source (open_rec_source n t2 t1)).
Proof.
  induction t1; intros; simpl in *; auto.
  - unfold open_source; simpl; destruct (Nat.eqb n0 n); auto.
  - apply MSetProperties.Dec.F.union_1 in H.
    inversion H.
    apply MSetProperties.Dec.F.union_2.
    now apply IHt1_1.
    apply MSetProperties.Dec.F.union_3.
    now apply IHt1_2.
  - apply MSetProperties.Dec.F.union_1 in H.
    inversion H.
    apply MSetProperties.Dec.F.union_2.
    now apply IHt1_1.
    apply MSetProperties.Dec.F.union_3.
    now apply IHt1_2.
  - apply MSetProperties.Dec.F.union_1 in H.
    inversion H.
    apply MSetProperties.Dec.F.union_2.
    now apply IHt1_1.
    apply MSetProperties.Dec.F.union_3.
    now apply IHt1_2.
Qed.

(*
not (In y (dom Gamma)) =>  
(x,A)::Gamma :- t1 ^ x : B (-> t2 ^ x) => 
(y,A)::Gamma :- [x -> y] (t1 ^ x) : B (-> [x -> y] (t2 ^ x))
*)
Lemma tsubst :
  forall E F t1 t2 x y A B,
    not (In y (dom (E ++ F))) ->
    has_type_source (E ++ (extend x A F)) (open_source t1 (PFVar x)) B (open_source t2 (PFVar x)) ->
    has_type_source (E ++ (extend y A F)) (subst_source x (PFVar y) (open_source t1 (PFVar x))) B (subst_source x (PFVar y) (open_source t2 (PFVar x))).
Proof.
  intros.
  remember (E ++ extend x A F) as G.
  generalize dependent HeqG.
  generalize dependent E.
  generalize dependent F.
  induction H0; intros; simpl in *; subst; eauto.
  - case_eq (x0 =? x); intro HEq.
    apply TyVar.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    rewrite <- app_nil_l in H.
    unfold extend in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    auto.
    assert (Ha : ty = A).
    apply eqb_eq in HEq.
    unfold extend in H; rewrite <- app_nil_l in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; subst.
    apply in_app_or in H0.
    inversion H0.
    exfalso; apply H7; rewrite dom_union; rewrite union_spec; left.
    apply list_impl_m in H3; now rewrite HEq in H3.
    unfold extend in H3; apply in_app_or in H3. 
    inversion H3.
    inversion H4; now inversion H6.
    exfalso; apply H7; rewrite dom_union; rewrite union_spec; right.
    apply list_impl_m in H4; now rewrite HEq in H4.
    rewrite Ha.
    apply in_or_app.
    right; apply in_or_app; left.
    left; reflexivity.
    auto.
    apply typing_weaken_source.
    apply TyVar.
    rewrite <- app_nil_l in H.
    unfold extend in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; auto.
    unfold extend in H3.
    apply in_app_or in H3.
    inversion H3.
    inversion H4.
    inversion H5; subst.
    apply EqFacts.eqb_neq in HEq.
    exfalso; apply HEq; reflexivity.
    inversion H5.
    apply in_or_app; auto.
    auto.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    unfold extend in H; now apply ok_remove in H.
    auto.
  - apply TyLit.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    unfold extend in H.
    rewrite <- app_nil_l in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    auto.
  - apply_fresh TyLam as z. 
    rewrite subst_source_open_var.
    rewrite subst_source_open_var.
    unfold extend in *.
    rewrite app_assoc.
    apply H0.
    not_in_L z.
    unfold not; intros.
    simpl.
    rewrite dom_union in H3; apply MSetProperties.Dec.F.union_1 in H3.
    inversion H3.
    rewrite dom_union in H4; apply MSetProperties.Dec.F.union_1 in H4.
    inversion H4.
    simpl in H5.
    apply MSetProperties.Dec.F.add_iff in H5.
    inversion H5.
    apply Frz.
    not_in_L z.
    inversion H6.
    apply H2; not_in_L y.
    apply H2; not_in_L y.
    rewrite app_assoc; reflexivity.
    not_in_L z.
    not_in_L x.
    apply PTerm_Var.
    not_in_L z.
    not_in_L x.
    apply PTerm_Var.
    auto.
Qed.

Lemma fv_source_in_open :
  forall x z t0 n, not (VarTyp.eq x z) ->
              In x (fv_source t0) ->
              In x (fv_source (open_rec_source n (PFVar z) t0)). 
Proof.
  intros.
  generalize dependent n.
  induction t0; simpl in *; auto.
  - inversion H0.
  - intros.
    rewrite union_spec in *.
    inversion H0.
    left; now apply IHt0_1.
    right; now apply IHt0_2.
  - intros.
    rewrite union_spec in *.
    inversion H0.
    left; now apply IHt0_1.
    right; now apply IHt0_2.
  - intros.
    rewrite union_spec in *.
    inversion H0.
    left; now apply IHt0_1.
    right; now apply IHt0_2.
Qed.
  
Lemma env_impl_fv_source :
  forall Gamma x t A E, has_type_source Gamma t A E -> In x (fv_source t) -> In x (dom Gamma).
Proof.
  intros.
  induction H.
  - simpl in *.
    apply MSetProperties.Dec.F.singleton_1 in H0.
    apply list_impl_m in H1.
    now rewrite H0 in H1.
  - inversion H0.
  - simpl in *.
    pick_fresh z.
    assert (Ha : not (In z L)) by not_in_L z.
    apply H1 in Ha.
    apply MSetProperties.Dec.F.add_iff in Ha.
    inversion Ha.
    assert (HNot : not (VarTyp.eq z x)) by not_in_L z.
    contradiction.
    assumption.
    apply fv_source_in_open.
    assert (HNot : not (VarTyp.eq z x)) by not_in_L z.
    unfold not; intros; apply HNot; now symmetry.
    assumption.
  - simpl in H0; rewrite union_spec in H0.
    inversion H0.
    now apply IHhas_type_source1.
    now apply IHhas_type_source2.
  - simpl in H0; rewrite union_spec in H0.
    inversion H0.
    now apply IHhas_type_source1.
    now apply IHhas_type_source2.
  - simpl in H0; rewrite union_spec in H0.
    inversion H0.
    now apply IHhas_type_source1.
    now apply IHhas_type_source2.
  - auto.
Qed.
    
Lemma not_env_impl_not_fv_source :
  forall Gamma x t A E, has_type_source Gamma t A E ->
               not (In x (dom Gamma)) ->
               not (In x (fv_source t)).
Proof.
  intros Gamma x t A E H HNot.
  induction H.
  - apply list_impl_m in H0.
    pose (@VarTyp.eq_dec x x0) as s.
    inversion s.
    rewrite H2 in HNot.
    contradiction.
    simpl.
    unfold not; intros; apply H2.
    apply MSetProperties.FM.singleton_1 in H3.
    now symmetry.
  - simpl; unfold not; intros HInv; now apply MSetProperties.Dec.F.empty_iff in HInv.
  - simpl in *.
    pick_fresh z.
    assert (not (In z L)) by not_in_L z.
    assert (not (VarTyp.eq z x)) by not_in_L z.
    apply H in H2.
    assert (not (In z L)) by not_in_L z.
    apply H0 in H4.
    unfold not; intros; apply H4.
    apply fv_source_in_open.
    unfold not; intros; apply H3; now symmetry.
    auto.
    unfold not; intros.
    apply MSetProperties.Dec.F.add_iff in H5.
    inversion H5.
    apply H3; now symmetry.
    contradiction.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; unfold not; intros HInv; apply IHhas_type_source; auto.
Qed.

Lemma not_env_impl_not_fv_source_E :
  forall Gamma x t A E, has_type_source Gamma t A E ->
               not (In x (dom Gamma)) ->
               not (In x (fv_source E)).
Proof.
  intros Gamma x t A E H HNot.
  induction H.
  - apply list_impl_m in H0.
    pose (@VarTyp.eq_dec x x0) as s.
    inversion s.
    rewrite H2 in HNot.
    contradiction.
    simpl.
    unfold not; intros; apply H2.
    apply MSetProperties.FM.singleton_1 in H3.
    now symmetry.
  - simpl; unfold not; intros HInv; now apply MSetProperties.Dec.F.empty_iff in HInv.
  - simpl in *.
    pick_fresh z.
    assert (not (In z L)) by not_in_L z.
    assert (not (VarTyp.eq z x)) by not_in_L z.
    apply H in H2.
    assert (not (In z L)) by not_in_L z.
    apply H0 in H4.
    unfold not; intros; apply H4.
    apply fv_source_in_open.
    unfold not; intros; apply H3; now symmetry.
    auto.
    unfold not; intros.
    apply MSetProperties.Dec.F.add_iff in H5.
    inversion H5.
    apply H3; now symmetry.
    contradiction.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; rewrite union_spec.
    unfold not; intros HInv.
    inversion HInv.
    apply IHhas_type_source1; auto.
    apply IHhas_type_source2; auto.
  - simpl; unfold not; intros HInv; apply IHhas_type_source; auto.
Qed.

  
Lemma tsubst'' :
  forall E F t1 x y A B,
    not (In y (dom (E ++ F))) ->
    has_type (E ++ (extend x A F)) (open_source t1 (PFVar x)) B ->
    has_type (E ++ (extend y A F)) (subst_source x (PFVar y) (open_source t1 (PFVar x))) B.
Proof.
  unfold has_type.
  intros.  
  remember (E ++ extend x A F) as G.
  generalize dependent HeqG.
  generalize dependent E.
  generalize dependent F.
  inversion H0.
  induction H; intros; simpl in *; subst; eauto.
  - case_eq (x0 =? x); intro HEq.
    exists (PFVar y).
    apply TyVar.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    rewrite <- app_nil_l in H.
    unfold extend in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    auto.
    assert (Ha : ty = A).
    apply eqb_eq in HEq.
    unfold extend in H; rewrite <- app_nil_l in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; subst.
    apply in_app_or in H1.
    inversion H1.
    exfalso; apply H8; rewrite dom_union; rewrite union_spec; left.
    apply list_impl_m in H4; now rewrite HEq in H4.
    unfold extend in H4; apply in_app_or in H4. 
    inversion H4.
    inversion H5; now inversion H7.
    exfalso; apply H8; rewrite dom_union; rewrite union_spec; right.
    apply list_impl_m in H5; now rewrite HEq in H5.
    rewrite Ha.
    apply in_or_app.
    right; apply in_or_app; left.
    left; reflexivity.
    auto.
    exists (PFVar x0).
    apply typing_weaken_source.
    apply TyVar.
    rewrite <- app_nil_l in H.
    unfold extend in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    apply in_app_or in H1.
    inversion H1.
    apply in_or_app; auto.
    unfold extend in H4.
    apply in_app_or in H4.
    inversion H4.
    inversion H5.
    inversion H6; subst.
    apply EqFacts.eqb_neq in HEq.
    exfalso; apply HEq; reflexivity.
    inversion H6.
    apply in_or_app; auto.
    auto.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    unfold extend in H; now apply ok_remove in H.
    auto.
  - exists (PLit x0).
    apply TyLit.
    rewrite <- app_nil_l; apply ok_middle_comm; rewrite app_nil_l.
    apply Ok_push.
    unfold extend in H.
    rewrite <- app_nil_l in H; apply ok_middle_comm in H; rewrite app_nil_l in H.
    inversion H; auto.
    auto.
  - eexists.
    apply_fresh TyLam as z. 
    rewrite subst_source_open_var.
    unfold open_source at 2.
    rewrite <- open_rec_source_term.
    unfold extend in *.
    rewrite app_assoc.
    assert (Ha : (not (In z L))) by not_in_L z.
    eapply (H1 z) in Ha.
    inversion Ha.
    Admitted.
(*
apply H4.
    not_in_L z.
    unfold not; intros.
    simpl.
    rewrite dom_union in H3; apply MSetProperties.Dec.F.union_1 in H3.
    inversion H3.
    rewrite dom_union in H4; apply MSetProperties.Dec.F.union_1 in H4.
    inversion H4.
    simpl in H5.
    apply MSetProperties.Dec.F.add_iff in H5.
    inversion H5.
    apply Frz.
    not_in_L z.
    inversion H6.
    apply H2; not_in_L y.
    apply H2; not_in_L y.
    rewrite app_assoc; reflexivity.
    not_in_L z.
    not_in_L x.
    apply PTerm_Var.
    not_in_L z.
    not_in_L x.
    apply PTerm_Var.
    auto.
Qed.*)

Lemma typing_open_rec_source :
  forall y A Gamma t B E n,
    has_type_source (extend y A Gamma) (open_rec_source n (PFVar y) t) B E ->
    (exists E', E = open_rec_source n (PFVar y) E').
Proof.
  intros.
  remember (extend y A Gamma).
  remember (open_source t0 (PFVar y)).
  generalize dependent Heqc.
  generalize dependent Heqp.
  inversion H; intros; subst.
  eexists. apply H0.
  eexists. apply H0.
  exists (PAnn (PLam t2) (Fun A0 B0)).
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H. 
  exists (PApp t1' t2').
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H.   
  exists (PMerge t1' t2').
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H.
  exists (PPair t1' t2').
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H.
  exists (PAnn t' B).
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H.   
Qed.


Lemma test :
  forall z A B Gamma y t0 x0,
    has_type_source (extend z A Gamma)
                    (subst_source y (PFVar z) (open_source t0 (PFVar y))) B
                    (subst_source y (PFVar z) (open_source x0 (PFVar y))) ->
    not (In y (dom Gamma)) ->
    not (z = y) ->
    has_type_source (extend z A Gamma)
                    (open_source t0 (PFVar z)) B (open_source x0 (PFVar z)).
Proof.
  intros.
  remember (extend z A Gamma).
  dependent induction H; subst.
  simpl in *.
  Focus 5.
Admitted.
  
Definition tlam : forall L Gamma t A B, (forall x, not (In x L) -> 
                                     has_type (extend x A Gamma) (open_source t (PFVar x)) B) ->
                               WFTyp A ->
                               has_type Gamma (PLam t) (Fun A B).
  intros.
  unfold has_type.
  unfold has_type in H.
  pick_fresh y.
  (* at this point we should have not (In y (fv_source x0)), see admit below *)
  assert (HNot : not (In y L)) by not_in_L y.
  pose (H y HNot).
  destruct e.
(*
  assert (not (In y (match H y HNot with
                       | ex_intro _ s _ => (fv_source s) end))).
*)  
  assert (Ha : has_type_source (extend y A Gamma) (open_source t0 (PFVar y)) B x) by apply H1.
  apply typing_open_rec_source in H1.
  destruct H1 as [x0 H1].
  subst.
  assert (Ha2 : has_type_source (extend y A Gamma) (open_source t0 (PFVar y)) B
         (open_rec_source 0 (PFVar y) x0)) by apply Ha.
  exists (PAnn (PLam x0) (Fun A B)).  
  apply_fresh TyLam as z. 
  rewrite <- app_nil_l with (l := extend y A Gamma) in Ha.

(*
  rewrite <- app_nil_l with (l := extend z A Gamma).
  eapply tsubst' with (y := y).
  simpl. not_in_L y.
  rewrite subst_fresh_var.
  rewrite subst_fresh_var.
  apply Ha.
  not_in_L y0.
  not_in_L y0.
  apply H0.
  *)

  apply tsubst with (y := z) in Ha.
  rewrite app_nil_l in Ha.
  rewrite subst_fresh_var in Ha.
  rewrite subst_fresh_var in Ha.
  apply Ha.
  apply not_env_impl_not_fv_source_E with (x := y) in Ha.
  
  admit.
  simpl; admit.
  not_in_L y.
  not_in_L y.
  not_in_L z.
  auto.
  
  (*
  assert (E : PExp) by admit.
  assert (x = (open_source E (PFVar y))) by admit.
  assert (Ha : not (In y (fv_source E))) by admit.
  subst.
  exists (PAnn (PLam E) (Fun A B)).  
  apply_fresh TyLam as x0.
  
  rewrite <- app_nil_l with (l := extend y A Gamma) in H1.
  eapply tsubst with (y := x0) in H1.
  rewrite app_nil_l in H1.
  rewrite subst_fresh_var in H1.
  rewrite subst_fresh_var in H1.
  apply H1.
  not_in_L x0.
  apply Ha.
  not_in_L x0.
  not_in_L y.
  not_in_L x0.
  auto.
*)
  
(*  
  assert (forall {y z}, not (In y L) -> not (In z L ) -> has_type_source (extend y A Gamma) (open_source t0 (PFVar y)) B x = has_type_source (extend z A Gamma) (open_source t0 (PFVar z)) B x).
  (* so, if y0 and z are both fresh *)
  admit.
  assert (HNotZ : not (In x0 L)) by not_in_L x0.
  pose (H2 _ _ HNotZ HNot). rewrite <- e in H0. clear e. clear H2.
  assert (open_rec_source 0 (PFVar x0) x = x). (* should be true if x0 not in the fv(x) *)
  admit.
  unfold open_source at 2.
  rewrite H2.
  assumption.
  admit. *)
Admitted.

Definition tapp : forall Gamma A B t1 t2,
              has_type Gamma t1 (Fun A B)  ->
              has_type Gamma t2 A  ->
              has_type Gamma (PApp t1 t2) B.
unfold has_type. intros. destruct H, H0.
exists (PApp x x0). apply (TyApp _ A); auto.
Defined.

Definition tmerge : forall Gamma A B t1 t2,
                has_type Gamma t1 A ->
                has_type Gamma t2 B ->
                OrthoS A B ->
                has_type Gamma (PMerge t1 t2) (And A B).
unfold has_type. intros. destruct H, H0.
exists (PMerge x x0). apply (TyMerge); auto.
Defined.

Definition tpair : forall Gamma A B t1 t2,
                has_type Gamma t1 A ->
                has_type Gamma t2 B ->
                has_type Gamma (PPair t1 t2) (Pair A B).
unfold has_type. intros. destruct H, H0.
exists (PPair x x0). apply (TyPair); auto.
Defined.

Definition tsub : forall Gamma t A B, has_type Gamma t A -> Sub A B -> WFTyp B -> has_type Gamma t B.
unfold has_type. intros. destruct H. exists (PAnn x B). apply (TySub _ _ _ A); auto.
Defined.  

Inductive Dir := Inf | Chk.

(* bidirection type-system (algorithmic): 

T |- e => t ~> E     (inference mode: infers the type of e producing target E) (use Inf)
T |- e <= t ~> E     (checking mode: checks the type of e producing target E) (use Chk)

Inspiration for the rules:

https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

*)

Inductive has_type_source_alg : context PTyp -> PExp -> Dir -> PTyp -> (SExp var) -> Prop :=
  (* Inference rules *)
  | ATyVar : forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma -> WFTyp ty ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x) 
  | ATyLit : forall Gamma x, ok Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp _ E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                OrthoS A B ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair _ E1 E2)
  | ATyPair : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                has_type_source_alg Gamma (PPair t1 t2) Inf (Pair A B) (STPair _ E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E -> has_type_source_alg Gamma (PAnn t1 A) Inf A E
  (* Checking rules *)
  | ATyLam : forall L Gamma t A B E, (forall x, not (In x L) -> 
                                 has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) -> WFTyp A ->
                           has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam' _ E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp B ->
               has_type_source_alg Gamma t Chk B (STApp _ (C var) E).

Hint Constructors has_type_source_alg.

Lemma decidability_types :
  forall (A B : PTyp), sumbool (A = B) (not (A = B)).
Proof.
  intros A.
  induction A.
  destruct B; auto; apply right; unfold not; intros H; inversion H.

  destruct B.
  right; unfold not; intros HInv; inversion HInv.
  assert (HA1: sumbool (A1 = B1) (A1 <> B1)) by (apply IHA1).
  assert (HA2: sumbool (A2 = B2) (A2 <> B2)) by (apply IHA2).  
  inversion HA1; subst; inversion HA2; subst.
  apply left; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv.

  destruct B.
  right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  assert (HA1: sumbool (A1 = B1) (A1 <> B1)) by (apply IHA1).
  assert (HA2: sumbool (A2 = B2) (A2 <> B2)) by (apply IHA2).  
  inversion HA1; subst; inversion HA2; subst.
  apply left; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv.
  contradiction. 
  apply right; unfold not; intros HInv; inversion HInv; subst.
  
  destruct B.
  right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  assert (HA1: sumbool (A1 = B1) (A1 <> B1)) by (apply IHA1).
  assert (HA2: sumbool (A2 = B2) (A2 <> B2)) by (apply IHA2).  
  inversion HA1; subst; inversion HA2; subst.
  apply left; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv; subst.
  apply H; reflexivity.
  apply right; unfold not; intros HInv; inversion HInv.
  contradiction.
Qed.

Module PTypDecidable <: DecidableType.

  Definition t := PTyp.

  Definition eq (x : PTyp) y := (x = y).
      
  Definition eq_refl : forall x : t, eq x x.
    Proof. destruct x; reflexivity. Defined.
    
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. destruct x; destruct y; intros; auto; symmetry; assumption. Defined.
  
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros; rewrite H; assumption. Defined.

  Definition eq_equiv : Equivalence eq :=
    Build_Equivalence _ eq_refl eq_sym eq_trans.
    
  Definition eq_dec : forall x y, sumbool (eq x y) (not (eq x y)).
    Proof. apply decidability_types. Defined.
  
End PTypDecidable.

Import PTypDecidable.
Require Import Coq.Structures.DecidableTypeEx.

Module VarTypDecidable <: DecidableType.

  Definition t := VarTyp.t.

  Definition eq (x : VarTyp.t) y := (VarTyp.eq x y).

  Definition eq_equiv : Equivalence eq.
    Proof. apply VarTyp.eq_equiv. Defined.
    
  Definition eq_refl : forall x : t, eq x x.
    Proof. apply reflexivity. Defined.
    
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. intros; symmetry; assumption. Defined.
  
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros; rewrite H; assumption. Defined.

  Definition eq_dec : forall x y, sumbool (eq x y) (not (eq x y)).
    Proof. apply VarTyp.eq_dec. Defined.
  
End VarTypDecidable.

Module MDec := PairDecidableType(VarTypDecidable)(PTypDecidable).

Lemma ok_unique_type : forall (Gamma: context PTyp) x A B,
  ok Gamma ->
  List.In (x, A) Gamma /\ List.In (x, B) Gamma ->
  A = B.
Proof.
  intros.
  
  induction H.
  inversion H0.
  inversion H.
  
  assert (HaA : sumbool (MDec.eq (x,A) (v, ty)) (not (MDec.eq (x,A) (v, ty)))).
  apply MDec.eq_dec.

  assert (HaB : sumbool (MDec.eq (x,B) (v, ty)) (not (MDec.eq (x,B) (v, ty)))).
  apply MDec.eq_dec.

  inversion HaA; inversion HaB.
  inversion H2; inversion H3; simpl in *.
  subst.
  reflexivity.
  
  inversion H2.
  simpl in *; subst.
  inversion H0.
  inversion H5; inversion H6.
  inversion H8; subst; reflexivity.
  inversion H7; subst.
  apply list_impl_m in H8; contradiction.
  inversion H8; subst; reflexivity.
  now apply IHok.

  inversion H3.
  simpl in *; subst.
  inversion H0.
  inversion H5; inversion H6.
  inversion H7; inversion H8; subst; reflexivity.
  inversion H7; subst; reflexivity.
  inversion H8; subst.
  apply list_impl_m in H7; contradiction.
  now apply IHok.

    
  apply IHok.
  inversion H0; clear H0.
  split; [ (apply in_app_or in H4; inversion H4) | (apply in_app_or in H5; inversion H5) ]; try assumption; inversion H0; inversion H6; simpl in *; subst;
  exfalso; [ apply H2 | apply H3 ]; reflexivity.
Qed.  

Lemma typing_wf_source_alg:
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp T.
Proof.
  intros Gamma t dir T E H.
  induction H; auto.
  inversion IHhas_type_source_alg1; assumption.
  pick_fresh x.
  assert (Ha : not (M.In x L)) by (not_in_L x).
  apply WFFun.
  apply H in Ha.
  assumption.
  apply H0 with (x := x); assumption.
Qed.
    
Lemma typing_weaken_alg : forall G E F t T d dir,
   has_type_source_alg (E ++ G) t dir T d -> 
   ok (E ++ F ++ G) ->
   has_type_source_alg (E ++ F ++ G) t dir T d.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply ATyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
    assumption.
  (* STTyLam *)
  - unfold extend in *.
    apply_fresh ATyLam as x.
    unfold open in *; simpl in *.
    unfold extend.
    rewrite app_assoc.
    apply H0.
    not_in_L x.
    rewrite HeqH'.
    rewrite <- app_assoc.
    reflexivity.
    rewrite <- app_assoc.
    apply Ok_push.
    assumption.
    repeat (rewrite dom_union; rewrite M.union_spec).
    repeat rewrite M.union_spec in Frx.
    repeat rewrite or_assoc in *.
    unfold not; intro HInv; destruct HInv as [HInv | [HInv | HInv]]; apply Frx; auto 8.
    assumption.
Qed.
    
Lemma typing_strengthen_alg : forall z U E F t dir T d,
  not (In z (fv_source t)) ->
  has_type_source_alg (E ++ ((z,U) :: nil) ++ F) t dir T d ->
  has_type_source_alg (E ++ F) t dir T d.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - subst; apply ATyVar.
    now apply ok_remove in H0.
    apply in_or_app.
    repeat apply in_app_or in H1.
    inversion H1.
    auto.
    apply in_app_or in H3.
    inversion H3.
    inversion H4.
    inversion H5.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H5.
    auto.
    assumption.
  - apply ATyLit.
    subst.
    now apply ok_remove in H0.
  - eapply ATyApp.
    subst.
    apply IHhas_type_source_alg1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHhas_type_source_alg2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply ATyMerge.
    apply IHhas_type_source_alg1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_source_alg2; simpl in *; not_in_L z; reflexivity.
    assumption.
  - subst.
    apply ATyPair.
    apply IHhas_type_source_alg1; simpl in *; not_in_L z; reflexivity.
    apply IHhas_type_source_alg2; simpl in *; not_in_L z; reflexivity.
  - subst.
    apply_fresh ATyLam as x.
    unfold extend in *; simpl in *.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    not_in_L z.
    apply fv_source_distr in H3.
    rewrite union_spec in H3.
    inversion H3.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H4.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H4.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
    assumption.
  - subst.
    eapply ATySub.
    apply IHhas_type_source_alg.
    assumption.
    reflexivity.
    apply H1.
    assumption.
Qed.    

Lemma type_correct_alg_terms : forall Gamma E ty e dir, has_type_source_alg Gamma E dir ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Qed.


Lemma typing_alg_ok_env : forall Gamma E dir ty e, has_type_source_alg Gamma E dir ty e -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Qed.


Definition body_typ t A B Gamma E :=
  exists L, forall x, not (In x L) -> has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x)).

(** We then show how to introduce and eliminate [body t]. *)

Lemma term_abs_to_body_typ : forall t1 A B Gamma E, 
  has_type_source_alg Gamma (PLam t1) Chk (Fun A B) (STLam' _ E) -> body_typ t1 A B Gamma E.
Proof. intros. unfold body_typ. inversion H. subst. exists L. unfold open_rec. apply H5. Qed.

Lemma body_typ_to_term_abs : forall t1 A B Gamma E, 
  body_typ t1 A B Gamma E -> has_type_source_alg Gamma (PLam t1) Chk (Fun A B) (STLam' _ E).
Proof. intros. inversion H. apply_fresh ATyLam as x.
       assert (not (In y x)) by (not_in_L y). now apply H0 in H1. admit. Admitted.

Definition alpha :forall t0 x y A Gamma B E,
  not (In x (union (dom Gamma) (fv_source t0))) ->
  not (In y (union (dom Gamma) (fv_source t0))) ->               
  has_type_source_alg (extend y A Gamma) (open_source t0 (PFVar y)) Chk B (open E (STFVar _ y)) ->
  has_type_source_alg (extend x A Gamma) (open_source t0 (PFVar x)) Chk B (open E (STFVar _ x)).        
Proof.
  (*
  induction t0; intros; subst.
  - unfold open_source in *.
    simpl in H1; simpl.
    rewrite <- app_nil_l with (l := (extend y A Gamma)) in H1.
    unfold extend in H1.
    rewrite union_spec in H0; apply not_or_and in H0; inversion H0.
    apply (typing_strengthen_alg _ _ _ _ _ _ _ _ H3) in H1.
    rewrite <- app_nil_l with (l := extend x A Gamma).
    unfold extend.
    apply typing_weaken_alg.
    assumption.
    rewrite app_nil_l.
    apply Ok_push.
    rewrite app_nil_l in H1.
    now apply typing_alg_ok_env in H1.
    rewrite union_spec in H; apply not_or_and in H; inversion H.
    assumption.
  - admit.
  - unfold open_source in *; simpl in *.
    inversion H1; subst.
    admit.
  - inversion H1; subst.
    unfold open_source in *; simpl in *.
    apply_fresh ATyLam as x.
    inversion H1; subst.
   *)
Admitted.

  
(* Ignoring the generated expressions + smart constructors *)

Definition has_ty Gamma e d t := exists E, has_type_source_alg Gamma e d t E.


Definition body_ty t A B Gamma :=
  exists L, forall x, not (In x L) -> has_ty (extend x A Gamma) (open_source t (PFVar x)) Chk B.

Lemma term_abs_to_body_ty : forall t1 A B Gamma, 
  has_ty Gamma (PLam t1) Chk (Fun A B) -> body_ty t1 A B Gamma.
Proof. intros. unfold body_ty. inversion H. inversion H0. subst. exists L.
       refine (fun x NHL => ex_intro _ (open E (STFVar _ x)) (H5 x NHL)).
       subst. inversion H1.
Qed.

Lemma foo' : forall L Gamma A B t1,
  (forall x : elt,
       ~ In x L ->
       exists E : SExp var,
         has_type_source_alg (extend x A Gamma) (open_source t1 (PFVar x))
                             Chk B E) ->
  (forall x : elt,
       ~ In x L ->
       exists E : SExp var,
         has_type_source_alg (extend x A Gamma) (open_source t1 (PFVar x))
           Chk B (open E (STFVar _ x))).
Admitted.
  
Lemma body_ty_to_term_abs : forall t1 A B Gamma, 
  body_ty t1 A B Gamma -> has_ty Gamma (PLam t1) Chk (Fun A B).
Proof. intros. unfold body_ty in H. unfold has_ty in *. inversion H as [L H1].
       eexists (STLam' _ _).
       unfold has_ty in H1.
       eapply (foo' L Gamma A B t1) in H1.
       eapply (ATyLam _ _ _ _ _ _ _ _).
       pick_fresh x.
       not_in_L x.
       (* apply H3. *)
       
Admitted.

Lemma free_var : forall t Gamma A B E x y,
  not (In y (union (dom Gamma) (union (fv_source t) (fv E)))) ->
  has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (E ^ x) ->
  has_type_source_alg (extend y A Gamma) (open_source t (PFVar y)) Chk B (E ^ y).
Proof.
  intros t Gamma A B E x y HNot H.
  remember (extend x A Gamma).
  induction H.
  - unfold open_source in *.
    unfold open in *.
    simpl in *; subst.
Admitted.
  
Lemma tylam : forall {Gamma t A B} L,
  (exists E, forall x, not (In x L) -> has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) ->
  WFTyp A ->
  has_ty Gamma (PLam t) Chk (Fun A B).
Proof.
  intros.
  unfold has_ty in *.
  inversion H.
  exists (STLam' _ x).
  eapply (ATyLam _ _ _ _ _ _ H1 H0).
Defined.

Lemma tylam'' : forall {Gamma t A B} L,
  (forall x, not (In x L) -> 
        sig (fun E => has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x)))) ->
  sig (fun E => has_type_source_alg Gamma (PLam t) Chk (Fun A B) E).
Proof.
  intros.
  pick_fresh x.
  assert (not (In x L)) by (not_in_L x).

  
  refine (let f :=
              fun x xNotInL => match (X x xNotInL) with
                                | exist _ E PE => exist _ (STLam' _ E) ((fun EE => ATyLam _ _ _ A B EE _ _) E)
                              end
           in f x H).  
  admit.

  (*
  refine (let f : forall x, ~ In x L -> SExp var :=
              fun x xNotInL => match (X x xNotInL) with
                                | exist _ E PE => E
                              end
           in exist _ (f x H) ((fun E => ATyLam _ _ _ _ _ (STLam' var E) _ _) (f x H))). *)  
Admitted.
  
Lemma tylam' : forall {Gamma t A B} L,
  (forall x, not (In x L) -> 
        has_ty (extend x A Gamma) (open_source t (PFVar x)) Chk B) ->
  has_ty Gamma (PLam t) Chk (Fun A B).
Proof.
  intros.
  unfold has_ty in *.  
  apply body_ty_to_term_abs.
  pick_fresh y.
  assert (Ha : not (In y L)) by (not_in_L y).
  apply H in Ha.
  inversion Ha. 
  unfold body_ty.
  unfold has_ty.
  exists L.
  apply H.
Defined.

Definition tyvar : forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma -> WFTyp ty ->
                                      has_ty Gamma (PFVar x) Inf ty.
intros.
unfold has_ty. exists (STFVar _ x). apply ATyVar; auto.
Defined.

Definition tylit : forall Gamma x, ok Gamma -> has_ty Gamma (PLit x) Inf PInt.
intros. unfold has_ty.
exists (STLit _ x); auto.
Defined.

Definition tyapp : forall Gamma A B t1 t2,
              has_ty Gamma t1 Inf (Fun A B) ->
              has_ty Gamma t2 Chk A ->
              has_ty Gamma (PApp t1 t2) Inf B.
intros. unfold has_ty.
inversion H. inversion H0.
exists (STApp _ x x0).
apply (ATyApp _ A). auto. auto.
Defined.

Definition tymerge : forall Gamma A B t1 t2,
                has_ty Gamma t1 Inf A ->
                has_ty Gamma t2 Inf B ->
                OrthoS A B ->
                has_ty Gamma (PMerge t1 t2) Inf (And A B).
intros.
inversion H. inversion H0.
unfold has_ty. exists (STPair _ x x0). apply ATyMerge; auto.
Defined.

Definition typair : forall Gamma A B t1 t2,
                has_ty Gamma t1 Inf A ->
                has_ty Gamma t2 Inf B ->
                has_ty Gamma (PPair t1 t2) Inf (Pair A B).
intros.
inversion H. inversion H0.
unfold has_ty. exists (STPair _ x x0). apply ATyPair; auto.
Defined.

Definition tyann : forall Gamma t1 A, has_ty Gamma t1 Chk A -> has_ty Gamma (PAnn t1 A) Inf A.
intros. inversion H. unfold has_ty. exists x. apply ATyAnn. auto.
Defined.

Lemma tysub : forall Gamma t A B, has_ty Gamma t Inf A -> Sub A B -> WFTyp B -> has_ty Gamma t Chk B.
intros.
unfold has_ty.
inversion H. inversion H0.
exists ((STApp _ (x0 var) x)).
apply  (ATySub _ _ A); auto.
Defined.

Fixpoint erase (e : PExp) : PExp :=
  match e with
    | PFVar x => PFVar x
    | PBVar x => PBVar x
    | PLit x => PLit x
    | PLam e => PLam (erase e)
    | PApp e1 e2 => PApp (erase e1) (erase e2)
    | PMerge e1 e2 => PMerge (erase e1) (erase e2)
    | PPair e1 e2 => PPair (erase e1) (erase e2)
    | PAnn e t => erase e
  end.

(* Uniqueness *)

Definition almost_unique (A B : PTyp) (d : Dir) : Prop := 
  match d with
    | Inf => A = B
    | Chk => True (* Is this result useful for checking: exists C, Sub C A /\ Sub C B*)
  end.

(*
Lemma typ_unique : forall Gamma e t1 E1, has_type_source_alg Gamma e Inf t1 E1 -> forall t2 E2, has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros Gamma e t1 E1 H.
induction H; intros; unfold almost_unique.
(* case Var *)
inversion H0. 
admit. (* TODO *)
(* Case Lit *)
inversion H. auto.
(* case App *)
inversion H1.
apply IHhas_type_source_alg1 in H5. simpl in H5.
apply IHhas_type_source_alg2 in H6.
injection H5. intros. auto.
(* Case Merge *)
inversion H1.
apply IHhas_type_source_alg1 in H5.
apply IHhas_type_source_alg2 in H6.
rewrite H5. rewrite H6. auto.
(* Case Ann *)
inversion H0. auto.
(* Case Lam *)
inversion H1.
auto. auto.
*)


Lemma typ_unique : forall Gamma e d t1 E1, has_type_source_alg Gamma e d t1 E1 -> forall t2 E2, has_type_source_alg Gamma e d t2 E2 -> almost_unique t1 t2 d.
intros Gamma e d t1 E1 H.
induction H; intros; unfold almost_unique.
(* case Var *)
- inversion H2; subst.
  rewrite (ok_unique_type _ _ _ _ H (conj H0 H5)).
  reflexivity.
(* case Lit *)
- inversion H0. auto.
(* case App *)
- inversion H1.
  apply IHhas_type_source_alg1 in H5. simpl in H5.
  apply IHhas_type_source_alg2 in H6.
  injection H5. intros. auto.
(* Case Merge *)
- inversion H2.
  apply IHhas_type_source_alg1 in H5.
  apply IHhas_type_source_alg2 in H7.
  rewrite H5. rewrite H7. auto.
(* Case Pair *)
- inversion H1.
  apply IHhas_type_source_alg1 in H5.
  apply IHhas_type_source_alg2 in H6.
  rewrite H5; rewrite H6; auto.
(* Case Ann *)
- inversion H0. auto.
(* Case Lam *)
- auto.
(* case Sub *)
- auto.
Qed.

(* type inference always gives unique types *)

Lemma typ_inf_unique : forall {Gamma e t1 E1}, has_type_source_alg Gamma e Inf t1 E1 -> forall {t2 E2}, has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros.
pose (@typ_unique _ _ _ _ _ H _ _ H0). simpl in a. auto.
Qed.

Lemma typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.
intros Gamma e d t E1 H.
induction H; intros.
(* case PFVar *)
- inversion H2; reflexivity. 
(* case STLit *)
- inversion H0; reflexivity.
(* Case App *)
- inversion H1.
  assert (Fun A B = Fun A0 B).
  apply (typ_inf_unique H H5). injection H9. intros.
  rewrite <- H9 in H5. rewrite <- H10 in H6.
  apply IHhas_type_source_alg1 in H5. 
  apply IHhas_type_source_alg2 in H6.
  rewrite H5. rewrite H6. auto.
(* Case Merge *)
- inversion H2.
  apply IHhas_type_source_alg1 in H8.
  apply IHhas_type_source_alg2 in H9.
  rewrite H8. rewrite H9. auto.
(* Case Pair *)
- inversion H1.
  apply IHhas_type_source_alg1 in H7.
  apply IHhas_type_source_alg2 in H9.
  rewrite H7; rewrite H9; auto.
(* Case Ann *)
- inversion H0.
  apply IHhas_type_source_alg in H3. auto.
(* Case Lam *)
- inversion H2; subst.
  apply f_equal.
  pick_fresh x.
  assert (Ha1: not (M.In x L0)) by (not_in_L x).
  apply H7 in Ha1.
  apply H0 in Ha1.
  assert (HNotE : not (In x (fv E))) by (not_in_L x).
  assert (HNotF : not (In x (fv E0))) by (not_in_L x).
  apply (open_app_eq _ _ _ _ HNotE HNotF Ha1).
  not_in_L x.
  inversion H3. 
(* ATySub *)
- inversion H2.
  subst.
  inversion H.
  assert (A = A0).
  apply (typ_inf_unique H H3).
  subst.
  apply IHhas_type_source_alg in H3.
  subst.
  assert (WFTyp A0). now apply typing_wf_source_alg in H.
  assert (WFTyp B). assumption.
  assert (C = C0).
  apply (sub_coherent H3 H6 H0 H4).
  subst; reflexivity. 
Qed.

(*
Lemma has_type_completeness : forall Gamma e t, has_type_source Gamma e t -> has_type_source_alg Gamma (PAnn e t) Inf t.
Proof.
intros.
induction H.
(* Var *)
apply ATyAnn. apply (ATySub _ _ ty _). apply ATyVar. auto. apply reflex.
(* Lit *)
apply ATyAnn. apply (ATySub _ _ PInt _). apply ATyLit. apply reflex.
(* Lam *)
apply ATyAnn. apply (ATyLam _ _ _ _ L). intros. 
pose (H0 x H1). inversion h. auto.
(* App *)
apply ATyAnn. apply (ATySub _ _ B _). 
apply (ATyApp _ A). inversion IHhas_type_source1.
inversion H1. rewrite <- H5 in H.
auto.
*)


(* TODO move this and merge with CoherenceBasic *)
Lemma in_persists : forall x ty Gamma, List.In (x, ty) Gamma -> List.In (x, |ty|) (∥ Gamma ∥).
Proof.
  intros.
  induction Gamma.
  simpl in *; assumption.
  simpl in *.
  inversion H.
  subst; simpl in *.
  auto.
  right; apply IHGamma; auto.
Qed.

Lemma open_rec_term_core :
  forall t j v i u, i <> j -> open_rec_source j (PFVar v) t = open_rec_source i (PFVar u) (open_rec_source j (PFVar v) t) ->
    t = open_rec_source i (PFVar u) t.
Proof.
  intro t; induction t; intros; simpl.
  - reflexivity.
  - simpl in *.
    case_eq (Nat.eqb i n); intros.
    case_eq (Nat.eqb j n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    rewrite H2 in H0.
    unfold open_rec_source in H0.
    rewrite H1 in H0.
    assumption.
    reflexivity.
  - reflexivity.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - inversion H0.
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2. 
Qed.

Lemma coercions_produce_terms :
  forall E A B, sub A B E -> STTerm (E var).
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - apply_fresh STTerm_Lam' as x. cbn; auto.
  (* Case SFun *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply_fresh STTerm_Lam' as y; cbn.
    apply STTerm_App.
    repeat rewrite <- open_rec_term; assumption.
    apply STTerm_App.
    apply STTerm_Var.
    apply STTerm_App; [ repeat rewrite <- open_rec_term; auto | apply STTerm_Var ].
  (* Case SAnd1 *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    rewrite <- open_rec_term; auto.
  (* Case SAnd2 *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.    
  (* Case SAnd3 *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  (* Case SPair *)  
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    rewrite <- open_rec_term; auto.    
Qed.

Hint Resolve coercions_produce_terms.

(* Subtyping rules produce type-correct coercions: Lemma 3 *)
Lemma type_correct_coercions :
  forall Gamma A B E, sub A B E ->
             ok Gamma -> 
             has_type_st Gamma (E var) (STFun (|A|) (|B|)) .
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - simpl.
    apply_fresh STTyLam' as x; cbn.
    simpl; apply STTyVar.
    apply Ok_push; auto.
    left; simpl; auto.
  (* Case SFun *)
  - apply_fresh STTyLam' as x; cbn.
    apply_fresh STTyLam' as y; cbn.
    apply STTyApp with (A := (| o2 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend.
    assumption.
    assumption. 
    simpl.
    not_in_L y.
    apply MSetProperties.Dec.F.add_iff in H4; inversion H4.
    exfalso; apply H2; apply MSetProperties.Dec.F.singleton_2; auto.
    assumption.
    eapply coercions_produce_terms; apply H1.
    rewrite <- open_rec_term; eapply coercions_produce_terms; apply H1.
    eapply STTyApp.
    apply STTyVar.
    apply Ok_push.
    apply Ok_push.
    assumption.
    assumption.
    not_in_L y.
    not_in_L x.
    right; left; reflexivity.
    apply STTyApp with (A := (| o3 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend.
    assumption.
    assumption. 
    simpl.
    not_in_L y.
    apply MSetProperties.Dec.F.add_iff in H4; inversion H4.
    exfalso; apply H2; apply MSetProperties.Dec.F.singleton_2; auto.
    assumption.
    eapply coercions_produce_terms; apply H.
    rewrite <- open_rec_term; now apply coercions_produce_terms in H.
    apply STTyVar.
    apply Ok_push.
    apply Ok_push.
    assumption.
    assumption.
    simpl.
    rewrite union_spec in Fry.
    apply not_or_and in Fry.
    inversion Fry.
    unfold not; intros.
    apply MSetProperties.Dec.F.add_iff in H4.
    inversion H4.
    apply H2.
    apply MSetProperties.Dec.F.singleton_2; assumption.
    contradiction.
    left; reflexivity.
  (* Case SAnd1 *)
  - apply_fresh STTyLam' as x; cbn.
    apply STTyPair.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub1.
    assumption.
    now apply coercions_produce_terms in H.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub2.
    assumption.
    now apply coercions_produce_terms in H1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  (* Case SAnd2 *)
  - apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  (* SAnd3 *)
  - apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj2.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  (* Case SPair *)
  - apply_fresh STTyLam' as x; cbn.
    apply STTyPair.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub1.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub2.
    assumption.
    now apply coercions_produce_terms in H1.
    eapply STTyProj2.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
Qed.

  
(* Type preservation: Theorem 1 *)
Lemma type_preservation :
  forall x ty dir E (Gamma : context PTyp) (H : has_type_source_alg Gamma x dir ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof.
  intros.
  induction H; subst.
  (* TyVar *)
  - apply STTyVar.
    apply (ok_map Gamma H).
    now apply in_persists.
  (* TyLit *)
  - apply STTyLit.
    apply (ok_map Gamma H).
  (* TyApp *)
  - simpl in *.
    apply STTyApp with (A := |A|).
    assumption.
    assumption.
  (* TyMerge *)
  - simpl; apply STTyPair; assumption.
  (* TyPair *)
  - simpl; apply STTyPair; assumption.
  (* TyAnn *)
  - auto.
  (* TyLam *)
  - simpl.
    apply_fresh STTyLam' as x.
    unfold open; simpl.
    assert (Ha : not (M.In x L)).
    not_in_L x.
    apply H0 in Ha.
    simpl in *.
    unfold extend.
    simpl.
    apply Ha.
  (* ATySub *)
  - apply STTyApp with (|A|).
    apply type_correct_coercions.
    assumption.
    now apply typing_ok_env in IHhas_type_source_alg.
    assumption.
Qed.
    
(* Completeness *)

(* An auxiliary lemma that, given suitable pre-conditions, I think it will hold. *)

Lemma erasure_open : forall t1 n t0 x,
  not (In x (fv_source t0)) ->
  not (In x (fv_source t1)) ->                     
  erase (open_rec_source n (PFVar x) t1) = open_rec_source n (PFVar x) t0 ->
  erase t1 = t0.
Proof.
  induction t1; intros; simpl in H1.
  (* PFVar *)
  - destruct t0; try (now (simpl in H1; inversion H1)).
    simpl in *.
    destruct (Nat.eqb n n0).
    exfalso; apply H0; apply MSetProperties.Dec.F.singleton_2; now inversion H1.
    inversion H1.
  (* PBVar *)
  - destruct t0; try now (simpl in *; destruct (Nat.eqb n0 n); inversion H1).
    simpl in *.
    case_eq (Nat.eqb n0 n); intros; simpl in *.
    rewrite H2 in H1.
    exfalso; apply H; apply MSetProperties.Dec.F.singleton_2; now inversion H1.
    rewrite H2 in H1.
    inversion H1.
    simpl in *.
    case_eq (Nat.eqb n0 n); intros; case_eq (Nat.eqb n0 n1); intros; simpl in *.
    apply beq_nat_true in H2; apply beq_nat_true in H3.
    subst; auto.
    rewrite H2 in H1; rewrite H3 in H1; simpl in *; inversion H1.
    rewrite H2 in H1; rewrite H3 in H1; simpl in *; inversion H1.
    rewrite H2 in H1; rewrite H3 in H1; simpl in *; assumption.
  (* Lit *)
  - destruct t0; simpl in H; (try inversion H1).
    destruct (Nat.eqb n0 n1); inversion H3.
    auto.
  (* Lam *)
  - destruct t0; simpl in *; try now inversion H1.
    destruct (Nat.eqb n n0); inversion H1.
    inversion H1; now rewrite (IHt1 (S n) t0 x H H0 H3).
  (* App *)
  - destruct t0; simpl in *; try now inversion H1.
    destruct (Nat.eqb n n0); inversion H1.
    inversion H1.
    rewrite union_spec in H, H0.
    apply not_or_and in H; apply not_or_and in H0.
    inversion H as [xt01 xt02]; inversion H0 as [xt11 xt12].
    rewrite (IHt1_1 n t0_1 x xt01 xt11 H3).
    rewrite (IHt1_2 n t0_2 x xt02 xt12 H4).
    reflexivity.
  (* Merge *)
  - destruct t0; simpl in *; try now inversion H1.
    destruct (Nat.eqb n n0); inversion H1.
    inversion H1.
    rewrite union_spec in H, H0.
    apply not_or_and in H; apply not_or_and in H0.
    inversion H as [xt01 xt02]; inversion H0 as [xt11 xt12].
    rewrite (IHt1_1 n t0_1 x xt01 xt11 H3).
    rewrite (IHt1_2 n t0_2 x xt02 xt12 H4).
    reflexivity.
  (* Pair *)
  - destruct t0; simpl in *; try now inversion H1.
    destruct (Nat.eqb n n0); inversion H1.
    inversion H1.
    rewrite union_spec in H, H0.
    apply not_or_and in H; apply not_or_and in H0.
    inversion H as [xt01 xt02]; inversion H0 as [xt11 xt12].
    rewrite (IHt1_1 n t0_1 x xt01 xt11 H3).
    rewrite (IHt1_2 n t0_2 x xt02 xt12 H4).
    reflexivity.
  (* Ann *)
  - simpl in *.
    erewrite (IHt1 n t0 x H H0 H1).
    reflexivity.
Qed.

Lemma typ_complete : forall Gamma e t e',
  has_type_source Gamma e t e' -> (has_ty Gamma e' Inf t) /\ erase e' = e.
intros Gamma e t e' H.
induction H; intros; split; try (simpl; auto).
(* Case TyVar *)
apply tyvar; auto.
(* Case TyLit *)
apply tylit; auto.
(* Case TyLam *)
apply tyann.
apply (tylam' (union (union (union L (dom Gamma)) (fv_source t0)) (fv_source t1))).
intros.
assert (d: not (In x L)) by (not_in_L x).
pose (H0 x d). destruct a. (*destruct H2. destruct x0.*)
apply (tysub _ _ B). auto. apply reflex. inversion H3.
now apply typing_wf_source_alg in H5.
(* erasure of Lam *)
pick_fresh x. assert (has_type_source (extend x A Gamma) (open_source t0 (PFVar x)) B
                                      (open_source t1 (PFVar x))). 
assert (d: not (In x L)) by (not_in_L x).
apply (H x d).
assert ( has_ty (extend x A Gamma) (open_source t1 (PFVar x)) Inf B /\
         erase (open_source t1 (PFVar x)) = open_source t0 (PFVar x)).
assert (d: not (In x L)) by (not_in_L x).
apply (H0 x d). clear H H0. destruct H3.
unfold open_source in H0, H, H1. inversion H. clear H.
assert (Hxt0 : not (In x (fv_source t0))) by not_in_L x.
assert (Hxt1 : not (In x (fv_source t1))) by not_in_L x.
pose (erasure_open t1 0 t0 x Hxt0 Hxt1 H0). 
rewrite e. reflexivity.
(* Case App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
apply (tyapp _ A).
inversion H1.
unfold has_ty. exists x. auto.
apply (tysub _ _ A). auto. apply reflex. now apply typing_wf_source in H0.
(* erasure of App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Merge *)
destruct IHhas_type_source1.
destruct IHhas_type_source2.
apply tymerge; auto.
(* erasure of Merge *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
subst; auto.
(* Case Pair *)
destruct IHhas_type_source1.
destruct IHhas_type_source2.
apply typair; auto.
(* erasure of Pair *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
subst; auto.
(* Case Ann *)
destruct IHhas_type_source.
apply tyann. apply (tysub _ _ A); auto.
destruct IHhas_type_source.
auto.
Qed.

Lemma erase_open : forall t n e,
                     erase (open_rec_source n e t) = open_rec_source n (erase e) (erase t).
induction t0; intros; simpl; try auto. destruct (Nat.eqb n0 n); auto.
(* don't know how to deal with this in Coq 8.5, but should be trivially true :) *)
rewrite (IHt0 (S n) e). reflexivity.
rewrite (IHt0_1 n e). rewrite (IHt0_2 n e). reflexivity.
rewrite (IHt0_1 n e). rewrite (IHt0_2 n e). reflexivity.
rewrite (IHt0_1 n e). rewrite (IHt0_2 n e). reflexivity.
Qed.

Lemma typ_sound : forall e d A Gamma, has_ty Gamma e d A -> has_type Gamma (erase e) A.
intros.  
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
apply tvar; auto.
(* PFLit *)
apply tlit; auto.
(* App *)
apply (tapp _ A). auto. auto.
(* Merge *)
apply tmerge; auto.
(* Pair *)
apply tpair; auto.
(* Ann *)
apply (tsub _ _ A). auto. apply reflex.
now apply typing_wf_source_alg in H0.
(* Lam *)
apply_fresh tlam as x.
assert (d: not (In x L)) by (not_in_L x).
intros. pose (H0 x d).
unfold open_source in h. unfold open_source.
rewrite (erase_open t0 0 (PFVar x)) in h. auto.
auto.
(* Sub *)
apply (tsub _ _ A). auto. unfold Sub. exists C. auto. auto.
Qed.

(* erasure typing *)

Lemma erasure_typing :
  forall {e Gamma t}, has_type_source Gamma (erase e) t e -> has_ty Gamma e Inf t.
induction e; intros.
(* case var *)  
apply tyvar;
inversion H; auto.
(* case bvar *)
simpl in H.
inversion H.
(* case lit *)
inversion H.
apply tylit.
assumption.
(* case lam *)
inversion H.
(* Case App *)
inversion H.
apply IHe1 in H5.
apply IHe2 in H7.
apply (tyapp _ A). auto.
apply (tysub _ _ A). auto. apply reflex.
subst.
inversion H7.
now apply typing_wf_source_alg in H0.
(* Case Merge *)
inversion H.
apply IHe1 in H6.
apply IHe2 in H7.
apply (tymerge); auto.
(* Case Pair *)
inversion H.
apply IHe1 in H5.
apply IHe2 in H7.
apply (typair); auto.
(* Case Ann *)
inversion H. subst.
apply tyann. 
pick_fresh x.
assert (H1 : not (In x L)). not_in_L x.
pose (H5 x H1) as e.


subst.
admit.
(*
destruct e. inversion H3. simpl in H0. injection H0. intros. injection H0. intros.
rewrite H7 in h. rewrite H9 in h. simpl in IHe.
(* need some kind of substitution lemmas here to apply IHe ? *)
assert (has_type_source (extend x A Gamma) (open_source (erase e) (PFVar x)) B
                        (open_source e (PFVar x)) = has_type_source Gamma (PLam (erase e)) B (PLam e)).
admit.
rewrite H10 in h. apply IHe in h.
assert (has_ty Gamma (PLam e) Inf B = has_ty (extend x A Gamma) (open_source e (PFVar x)) Inf B).
admit.
rewrite H11 in h. 
apply (tysub _ _ B). auto. apply reflex. *)
apply tyann.
simpl in *.
apply IHe in H2.
apply (tysub _ _ A); auto.
Admitted.

End CoherenceBasicBDPairs.