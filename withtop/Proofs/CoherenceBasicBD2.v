Require Import String.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the correnposing lemmas/theorems in the paper. 
The reader can just look for:

Lemma 5

for example, to look for the proof of lemma 5 in the paper.

All lemmas and theorems are complete: there are no uses of admit or Admitted. 

*)

(* Target language: Simply typed lambda calculus with pairs *)

Inductive STyp := 
  | STInt : STyp
  | STFun : STyp -> STyp -> STyp
  | STTuple : STyp -> STyp -> STyp.

Inductive SExp (A : Type) :=
  | STFVar  : A -> SExp A
  | STBVar  : nat -> SExp A                   
  | STLit   : nat -> SExp A
  | STLam   : SExp A -> SExp A
  | STApp   : SExp A -> SExp A -> SExp A
  | STPair  : SExp A -> SExp A -> SExp A
  | STProj1 : SExp A -> SExp A
  | STProj2 : SExp A -> SExp A.

Definition Exp := forall A, SExp A.


(* Our calculus: *)

(* Types *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp.

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
  end.


Require Import Arith.
Require Import Setoid.

(* Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

Inductive sub : PTyp -> PTyp -> Exp -> Prop :=
  | SInt : sub PInt PInt (fun A => STLam _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun o3 o4) (fun A => STLam _ (STLam _  (STApp _ (c2 A) (STApp _ (STBVar _ 1) (STApp _ (c1 A) (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (fun A => STLam _
       (STPair _ (STApp _ (c1 A) (STBVar _ 0)) (STApp _ (c2 A) (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam _ 
       ((STApp _ (c A) (STProj1 _ (STBVar _ 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam _  
       ((STApp _ (c A) (STProj2 _ (STBVar _ 0))))).

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:Exp), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (fun A => STLam _ (STBVar _ 0)). 
exact SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (fun A => STLam _ ( 
       STLam _ (STApp _ (x0 A) (STApp _ (STBVar _ 1) (STApp _ (x A) (STBVar _ 0)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (fun A => STLam _ (
       STPair _ (STApp _ (x A) (STBVar _ 0)) (STApp _ (x0 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (fun A => STLam _ ( 
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto. destruct H.
exists (fun A => STLam _ (
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto.
inversion H0.
Defined.

(* The No loss of Expressivity Lemmas *)

(* Theorem 3 *)

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
induction t; intros.
(* Case PInt *)
apply sand2_atomic. auto. exact AInt.
(* Case Fun *)
apply sand2_atomic. auto. apply AFun.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
exists (fun A => STLam _ (
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (fun A => STLam _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto. destruct H.
exists (fun A => STLam _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto.
inversion H0.
Defined.

(* Theorem 4 *)

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
induction t; intros.
(* Case PInt *)
apply sand3_atomic. auto. exact AInt.
(* Case Fun *)
apply sand3_atomic. auto. apply AFun.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
exists (fun A => STLam _ (
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
Defined.

(* Disjointness: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2).

(* Reflexivity *)
Hint Resolve sint sfun sand1 sand2 sand3 SInt SFun SAnd1 SAnd2 SAnd3.

Lemma reflex : forall (t1 : PTyp), Sub t1 t1.
Proof.
induction t1; intros; auto.
Defined.

(* Disjointness algorithm is complete: Theorem 7 *)

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
exists x. split. exact H0. apply sand2. exact H1.
apply IHt2_2. unfold not. unfold not in H. intros. apply H.
destruct H0. destruct H0. exists x.
split. auto. apply sand3.
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
apply sfun.
apply sand2.
apply reflex.
auto.
apply sfun.
apply sand3. apply reflex.
auto.
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
induction t; intros.
(* Case Int *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
(* Case Fun *)
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
inversion H1. inversion H3. unfold OrthoS in H. apply H. exists (PInt). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (PInt). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
inversion H1. inversion H3. unfold OrthoS in H. apply H. exists (Fun x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (Fun x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
assert (Sub C x1 /\ Sub C x2). apply invAndS1. auto. destruct H3.
inversion H1. inversion H5. apply IHx1. 
unfold Sub. exists c1. auto. unfold Sub.  unfold Sub in H3. destruct H3. exists x0. auto.
unfold OrthoS in H. apply H. exists (And x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
unfold OrthoS in H0. apply H0. exists (And x1 x2). split. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
Defined.

(* Soundness of the disjointness algorithm: Theorem 6 *)

Lemma ortho_soundness : forall (t1 t2 : PTyp), Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(* Hard case *)
apply ortho_and; auto.
assert (OrthoS t2 t1). apply ortho_sym. apply IHOrtho1; auto.
assert (OrthoS t3 t1). apply ortho_sym. apply IHOrtho2; auto.
apply ortho_sym.
apply ortho_and; auto.
(* Case FunFun *)
unfold OrthoS. unfold not. intros.
unfold OrthoS in IHOrtho. apply IHOrtho.
destruct H0. destruct H0. generalize H0. generalize H1. clear H0. clear H1.
induction x; intros. inversion H1. inversion H2. exists x2.
split. inversion H0. inversion H2. unfold Sub. exists c2. auto. unfold Sub. inversion H1. inversion H2. exists c2. auto.
apply IHx1.
inversion H1. inversion H2. unfold Sub. exists c1. auto. 
inversion H0. inversion H2. exists c1. auto.
(* Case IntFun *)
unfold OrthoS. unfold not. intros.
destruct H. destruct H. induction x. inversion H0. inversion H1. inversion H. inversion H1.
apply IHx1.
inversion H. inversion H1. unfold Sub. exists c1. auto.
inversion H0. inversion H1. unfold Sub. exists c1. auto.
(* Case FunInt *)
unfold OrthoS. unfold not. intros.
destruct H. destruct H. induction x. inversion H. inversion H1. inversion H0. inversion H1.
apply IHx1. inversion H. inversion H1. unfold Sub. exists c1. auto.
inversion H0. inversion H1. unfold Sub. exists c1. auto.
Defined.

(* Coercive subtyping is coeherent: Lemma 5 *)

Lemma sub_coherent : forall {A}, WFTyp A -> forall {B}, WFTyp B -> forall {C1}, sub A B C1 -> forall {C2}, sub A B C2 -> C1 = C2.
Proof.
intro. intro. intro. intro. intro. intro.
(* Case: Int <: Int *)
induction H1; intros.
inversion H1. 
reflexivity.
(* Case: Fun t1 t2 <: Fun t3 t4 *)
inversion H1; inversion H; inversion H0.
assert (c2 = c3). apply IHsub2; auto.
assert (c1 = c0). apply IHsub1; auto.
rewrite H17. rewrite H18.
reflexivity.
(* Case: t <: And t1 t2 *) 
inversion H1; inversion H0.
assert (c1 = c0). apply IHsub1; auto.
assert (c2 = c3). apply IHsub2; auto.
rewrite H13. rewrite H14.
reflexivity.
(* different coercion case*)
inversion H3.
(* different coercion case*)
inversion H3.
(* Case: And t1 t2 <: t (first) *)
inversion H3; inversion H.
(* different coercion *)
rewrite <- H7 in H2. inversion H2.
(* same coercion *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
(* contradiction: not orthogonal! *)
destruct H14. exists t. unfold Sub.
split. exists c; auto. exists c0. auto.
(* Case: And t1 t2 <: t (second) *)
inversion H3; inversion H.
rewrite <- H7 in H2. inversion H2.
(* contradiction: not orthogonal! *)
destruct H14. exists t. unfold Sub.
split. exists c0; auto. exists c. auto.
(* same coercion; no contradiction *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
Defined.


(* typing rules of lambda i *)

Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Print MSetInterface.
Print MSetWeakList.

Module TypingRules
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

Definition var : Type := VarTyp.t.
  
Module M := MSetWeakList.Make(VarTyp).
Export M.

Definition vars := M.t.

(* Definitions borrowed from STLC_Tutorial *)

Definition context (A : Type) := list (var * A). 

Definition extend {A} (x : var) (a : A) (c : context A) : context A := (x,a) :: c.

Definition dom {A} (c : context A) : vars :=
  fold_left (fun r el => add (fst el) r) c empty.

(* Our source language *)
Inductive PExp :=
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp                   
  | PLit   : nat -> PExp
  | PLam   : PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp
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
    | PAnn t1 A => fv_source t1
  end.

(** Target language **)
Fixpoint fv (sExp : SExp var) : vars :=
  match sExp with
    | STFVar _ v => singleton v
    | STBVar _ _ => empty
    | STLit _ _ => empty
    | STLam _ t => fv t
    | STApp _ t1 t2 => union (fv t1) (fv t2)
    | STPair _ t1 t2 => union (fv t1) (fv t2)
    | STProj1 _ t => fv t
    | STProj2 _ t => fv t
  end.

(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars_with F :=
  let rec gather V :=
   (match goal with
    | H:?S
      |- _ =>
          let FH := constr:(F H) in
          match V with
          | empty => gather FH
          | context [FH] => fail 1
          | _ => gather (union FH V)
          end
    | _ => V
    end)
  in
  let L := gather (empty : vars) in
  eval simpl in L.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  let C := gather_vars_with (fun (x : context STyp) => dom x) in
  (*let D := gather_vars_with (fun x : PExp => fv_source x) in*)
  let E := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union C E))).

Ltac beautify_fset V :=
  let rec go Acc E :=
   (match E with
    | union ?E1 ?E2 => let Acc1 := go Acc E1 in
                    go Acc1 E2
    | empty => Acc
    | ?E1 => match Acc with
             | empty => E1
             | _ => constr:(union Acc E1)
             end
    end)
  in
  go (empty : vars) V.

Definition var_fresh : forall L : vars, {x : var | not (In x L) }.
Admitted.
  
Ltac pick_fresh_gen L Y :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  destruct (var_fresh L) as (Y, Fr).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Ltac apply_fresh_base_simple lemma gather :=
  let L0 := gather in
  let L := beautify_fset L0 in
  first
  [ apply (lemma L) | eapply (lemma L) ].

Ltac intros_fresh x :=
  first
  [ let Fr := fresh "Fr" x in
    intros x Fr
  | let x2 :=
     (match goal with
      | |- ?T -> _ =>
            match T with
            | var => fresh "y"
            | vars => fresh "ys"
            | list var => fresh "ys"
            | _ => fresh "y"
            end
      end)
    in
    let Fr := fresh "Fr" x2 in
    intros x2 Fr ]. 

Fixpoint fresh (L : vars) (n : nat) (xs : list var) : Prop :=
  match xs with
  | nil => match n with
           | 0 => True
           | S _ => False
           end
  | (x :: xs')%list =>
      match n with
      | 0 => False
      | S n' => (not (In x L)) /\ fresh (union L (singleton x)) n' xs'
      end
  end.

Ltac apply_fresh_base lemma gather var_name :=
  apply_fresh_base_simple lemma gather;
   try
    match goal with
    | |- _ -> not (In _ _) -> _ => intros_fresh var_name
    | |- _ -> fresh _ _ _ -> _ => intros_fresh var_name
    end.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i    => if Nat.eqb k i then u else (PBVar i)
  | PFVar x    => PFVar x
  | PLit x     => PLit x                     
  | PLam t1    => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2 => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn t1 A => PAnn (open_rec_source k u t1) A
  end.

Definition open_source t u := open_rec_source 0 u t.

(*
Notation "{ k ~> u } t" := (open_rec_source k u t) (at level 67).
Notation "t ^^ u" := (open_source t u) (at level 67).
Notation "t ^ x" := (open_source t (PFVar x)).
 *)

(** Target language **)
Fixpoint open_rec {a} (k : nat) (u : SExp a) (t : SExp a) : SExp a :=
  match t with
  | STBVar _ i => if Nat.eqb k i then u else (STBVar _ i)
  | STFVar _ x => STFVar _ x
  | STLit _ x => STLit _ x
  | STLam _ t1 => STLam _ (open_rec (S k) u t1)
  | STApp _ t1 t2 => STApp _ (open_rec k u t1) (open_rec k u t2)
  | STPair _ t1 t2 => STPair _ (open_rec k u t1) (open_rec k u t2)
  | STProj1 _ t => STProj1 _ (open_rec k u t)
  | STProj2 _ t => STProj2 _ (open_rec k u t)
  end.

Definition open {a} (t : SExp a) u := open_rec 0 u t.

(* Functions on contexts *)
Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
  map (fun p => (fst p, (f (snd p)))) c. 

Definition conv_context (env : context PTyp) : context STyp :=
  mapctx ptyp2styp env.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).

(*
Reserved Notation "Gamma '|-' t ':' T" (at level 40).
*)

(* Typing rules of source language: Figure 2 
Note that we generate an Annotated expression, which serves as evidence for bi-directional
type-checking completness proof.
 *)

(* Declarative type system *)

Inductive has_type_source : context PTyp -> PExp -> PTyp -> PExp -> Prop :=
  | TyVar : forall Gamma x ty, List.Exists (fun a => (fst a) = x /\ snd a = ty) Gamma ->
                      has_type_source Gamma (PFVar x) ty (PFVar x) (* is this right? *)
  | TyLit : forall Gamma x, has_type_source Gamma (PLit x) PInt (PLit x)
  | TyLam : forall Gamma t t1 A B L, (forall x, not (In x L) -> 
                                 has_type_source (extend x A Gamma) (open_source t (PFVar x)) B (open_source t1 (PFVar x))) ->
                           has_type_source Gamma (PLam t) (Fun A B) (PAnn (PLam t1) (Fun A B)) 
  | TyApp : forall Gamma A B t1 t1' t2 t2' ,
              has_type_source Gamma t1 (Fun A B) t1' ->
              has_type_source Gamma t2 A t2' ->
              has_type_source Gamma (PApp t1 t2) B (PApp t1' t2')
  | TyMerge : forall Gamma A B t1 t1' t2 t2' ,
                has_type_source Gamma t1 A t1' ->
                has_type_source Gamma t2 B t2' ->
                has_type_source Gamma (PMerge t1 t2) (And A B) (PMerge t1' t2')
  | TySub : forall Gamma t t' A B, has_type_source Gamma t A t' -> Sub A B -> has_type_source Gamma t B (PAnn t' B).

(* Smart constructors *)

Definition has_type Gamma e t := exists s, has_type_source Gamma e t s.

Definition tvar : forall Gamma x ty, List.Exists (fun a => (fst a) = x /\ snd a = ty) Gamma ->
                                     has_type Gamma (PFVar x) ty.
intros.  unfold has_type. exists (PFVar x). apply TyVar. auto.
Defined.

Definition tlit : forall Gamma x, has_type Gamma (PLit x) PInt.
intros. unfold has_type. exists (PLit x). apply TyLit.
Defined.

Definition tlam : forall Gamma t A B L, (forall x, not (In x L) -> 
                                 has_type (extend x A Gamma) (open_source t (PFVar x)) B) ->
                                        has_type Gamma (PLam t) (Fun A B).
intros.
unfold has_type.
unfold has_type in H.
pick_fresh y.
pose (H y Fr).
destruct e.
exists (PAnn (PLam x) (Fun A B)).
apply (TyLam _ _ _ _ _ L). intros.
assert (forall {y z}, not (In y L) -> not (In z L ) -> has_type_source (extend y A Gamma) (open_source t0 (PFVar y)) B x = has_type_source (extend z A Gamma) (open_source t0 (PFVar z)) B x).
(* so, if y0 and z are both fresh *)
admit.
pose (H2 _ _ Fr H1). rewrite e in H0. clear e. clear H2.
unfold open_source.
assert (open_rec_source 0 (PFVar x0) x = x). (* should be true if x0 not in the fv(x), but do we know that? *)
admit.
rewrite H2. auto.
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
                has_type Gamma (PMerge t1 t2) (And A B).
unfold has_type. intros. destruct H, H0.
exists (PMerge x x0). apply (TyMerge); auto.
Defined.

Definition tsub : forall Gamma t A B, has_type Gamma t A -> Sub A B -> has_type Gamma t B.
unfold has_type. intros. destruct H. exists (PAnn x B). apply (TySub _ _ _ A). auto. auto.
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
  | ATyVar : forall Gamma x ty, List.Exists (fun a => (fst a) = x /\ snd a = ty) Gamma ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x) (* is this right? *)
  | ATyLit : forall Gamma x, has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp _ E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair _ E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E -> has_type_source_alg Gamma (PAnn t1 A) Inf A E
  (* Checking rules *)
  | ATyLam : forall Gamma t A B L E, (forall x, not (In x L) -> 
                                 has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B E) ->
                           has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam _ E)
  | ATySub : forall Gamma t A B C E, has_type_source_alg Gamma t Inf A E -> sub A B C -> has_type_source_alg Gamma t Chk B (STApp _ (C var) E).

(* Ignoring the generated expressions + smart constructors *)

Definition has_ty Gamma e d t := exists E, has_type_source_alg Gamma e d t E.

Definition tyvar : forall Gamma x ty, List.Exists (fun a => (fst a) = x /\ snd a = ty) Gamma ->
                                      has_ty Gamma (PFVar x) Inf ty.
intros.
unfold has_ty. exists (STFVar _ x). apply ATyVar. auto.
Defined.

Definition tylit : forall Gamma x, has_ty Gamma (PLit x) Inf PInt.
intros. unfold has_ty.
exists (STLit _ x).
apply ATyLit.
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
                has_ty Gamma (PMerge t1 t2) Inf (And A B).
intros.
inversion H. inversion H0.
unfold has_ty. exists (STPair _ x x0). apply ATyMerge. auto. auto.
Defined.

Definition tyann : forall Gamma t1 A, has_ty Gamma t1 Chk A -> has_ty Gamma (PAnn t1 A) Inf A.
intros. inversion H. unfold has_ty. exists x. apply ATyAnn. auto.
Defined.

Definition tylam : forall {Gamma t A B} L, (forall x, not (In x L) -> 
                                 has_ty (extend x A Gamma) (open_source t (PFVar x)) Chk B) ->
                                         has_ty Gamma (PLam t) Chk (Fun A B).
intros.
unfold has_ty.  
unfold has_ty in H.
pick_fresh y. 
pose (H y Fr). destruct e. exists (STLam _ x).
apply (ATyLam _ _ _ _ L). intros.
Admitted.

Lemma tysub : forall Gamma t A B, has_ty Gamma t Inf A -> Sub A B -> has_ty Gamma t Chk B.
intros.
unfold has_ty.
inversion H. inversion H0.
exists ((STApp _ (x0 var) x)).
apply  (ATySub _ _ A). auto. auto.
Defined.

Fixpoint erase (e : PExp) : PExp :=
  match e with
    | PFVar x => PFVar x
    | PBVar x => PBVar x
    | PLit x => PLit x
    | PLam e => PLam (erase e)
    | PApp e1 e2 => PApp (erase e1) (erase e2)
    | PMerge e1 e2 => PMerge (erase e1) (erase e2)
    | PAnn e t => erase e
  end.

(* Uniqueness *)

Definition almost_unique (A B : PTyp) (d : Dir) : Prop := 
  match d with
    | Inf => A = B
    | Chk => True (* Is this result useful for checking: exists C, Sub C A /\ Sub C B*)
  end.

Lemma typ_unique : forall Gamma e d t1 E1, has_type_source_alg Gamma e d t1 E1 -> forall t2 E2, has_type_source_alg Gamma e d t2 E2 -> almost_unique t1 t2 d.
intros Gamma e d t1 E1 H.
induction H; intros; unfold almost_unique.
(* case Var *)
inversion H0. 
admit. (* TODO *)
(* case Lit *)
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
auto. auto.
Admitted.

(* type inference always gives unique types *)

Lemma typ_inf_unique : forall {Gamma e t1 E1}, has_type_source_alg Gamma e Inf t1 E1 -> forall {t2 E2}, has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros.
pose (@typ_unique _ _ _ _ _ H _ _ H0). simpl in a. auto.
Defined.

(* erasure typing *)

Lemma erasure_typing :
  forall {e Gamma t}, has_type_source Gamma (erase e) t e -> has_ty Gamma e Inf t.
induction e; intros.
(* case var *)  
apply tyvar.
inversion H. auto.
(* case bvar *)
simpl in H.
inversion H.
(* case lit *)
inversion H.
apply tylit.
(* case lam *)
inversion H.
(* Case App *)
inversion H.
apply IHe1 in H5.
apply IHe2 in H7.
apply (tyapp _ A). auto.
apply (tysub _ _ A). auto. apply reflex.
(* Case Merge *)
inversion H.
apply IHe1 in H5.
apply IHe2 in H7.
apply (tymerge). auto. auto.
(* Case Ann *)
inversion H.
apply tyann. apply (tylam L).
intros. pose (H4 x H6).
destruct e; inversion H2. simpl in H0. injection H0. intros. injection H2. intros.
rewrite H7 in h. rewrite H9 in h. simpl in IHe.
(* need some kind of substitution lemmas here to apply IHe ? *)
assert (has_type_source (extend x A Gamma) (open_source (erase e) (PFVar x)) B
                        (open_source e (PFVar x)) = has_type_source Gamma (PLam (erase e)) B (PLam e)).
admit.
rewrite H10 in h. apply IHe in h.
assert (has_ty Gamma (PLam e) Inf B = has_ty (extend x A Gamma) (open_source e (PFVar x)) Inf B).
admit.
rewrite H11 in h.
apply (tysub _ _ B). auto. apply reflex.
apply tyann.
simpl in H5.
apply IHe in H5.
apply (tysub _ _ A). auto. auto.
Admitted.

Lemma typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.
intros Gamma e d t E1 H.
induction H; intros.
(* case PFVar *)
inversion H0. rewrite H6. auto.
(* case STLit *)
inversion H. rewrite H4. auto.
(* Case App *)
inversion H1.
assert (Fun A B = Fun A0 B).
apply (typ_inf_unique H H5). injection H9. intros.
rewrite <- H9 in H5. rewrite <- H10 in H6.
apply IHhas_type_source_alg1 in H5. 
apply IHhas_type_source_alg2 in H6.
rewrite H5. rewrite H6. auto.
(* Case Merge *)
inversion H1.
apply IHhas_type_source_alg1 in H7.
apply IHhas_type_source_alg2 in H9.
rewrite H7. rewrite H9. auto.
(* Case Ann *)
inversion H0.
apply IHhas_type_source_alg in H3. auto.
(* Case Lam *)
inversion H1.
admit.
inversion H2.
(* ATySub *)
inversion H1.
admit.
assert (A = A0).
apply (typ_inf_unique H H2).
rewrite <- H6 in H2.
apply IHhas_type_source_alg in H2. rewrite H2.
rewrite <- H6 in H3. 
assert (WFTyp A). admit. assert (WFTyp B). admit.
assert (C = C0).
apply (sub_coherent H9 H10 H0 H3). rewrite H11. 
auto.
Admitted.

(* Typing rules of STLC, inspired by STLC_Tutorial *)
Inductive has_type_st : (context STyp) -> (SExp var) -> STyp -> Prop :=
  | STTyVar : forall Gamma x ty, List.Exists (fun a => (fst a) = x) Gamma ->
                        has_type_st Gamma (STFVar _ x) ty
  | STTyLit : forall Gamma x, has_type_st Gamma (STLit _ x) STInt       
  | STTyLam : forall Gamma t A B L, (forall x, not (In x L) -> 
                                 has_type_st (extend x A Gamma) (open t (STFVar _ x)) B) ->
                           has_type_st Gamma (STLam _ t) (STFun A B)
  | STTyApp : forall Gamma A B t1 t2, has_type_st Gamma t1 (STFun A B) ->
                             has_type_st Gamma t2 A -> has_type_st Gamma (STApp _ t1 t2) B
  | STTyPair : forall Gamma A B t1 t2, has_type_st Gamma t1 A ->
                              has_type_st Gamma t2 B ->
                              has_type_st Gamma (STPair _ t1 t2) (STTuple A B)
  | STTyProj1 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj1 _ t) A
  | STTyProj2 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj2 _ t) B.

(* Completeness *)

(* An auxiliary lemma that, given suitable pre-conditions, I think it will hold. *)

Lemma erasure_open : forall t1 n t0 x, erase (open_rec_source n (PFVar x) t1) = open_rec_source n (PFVar x) t0 -> erase t1 = t0.
induction t1; intros; simpl in H.
(* PFVar *)
destruct t0; simpl in H; inversion H. simpl. auto. admit. (*PBVar *)
(* PBVar *)
admit. (* this case should never happen: PBVar is not well-formed; need pre-condition; both 
t1 and t0 should satisfy this condiction *)
(* Lit *)
destruct t0; simpl in H; inversion H.
destruct (Nat.eqb n0 n1); inversion H1.
simpl. auto.
(* Lam *)
destruct t0; simpl in H; inversion H. destruct (Nat.eqb n n0); inversion H1. 
simpl. rewrite (IHt1 (S n) t0 x H1). reflexivity.
(* App *)
destruct t0; simpl in H; inversion H. destruct (Nat.eqb n n0); inversion H1. simpl.
rewrite (IHt1_1 n t0_1 x H1).
rewrite (IHt1_2 n t0_2 x H2).
reflexivity.
(* Merge *)
destruct t0; simpl in H; inversion H. destruct (Nat.eqb n n0); inversion H1. simpl.
rewrite (IHt1_1 n t0_1 x H1).
rewrite (IHt1_2 n t0_2 x H2).
reflexivity.
(* Ann *)
simpl.
rewrite (IHt1 n t0 x H).
reflexivity.
Admitted.

Lemma typ_complete : forall Gamma e t e',
  has_type_source Gamma e t e' -> (has_ty Gamma e' Inf t) /\ erase e' = e.
intros Gamma e t e' H.
induction H; intros; split; try (simpl; auto).
(* Case TyVar *)
apply tyvar. auto.
(* Case TyLit *)
apply tylit.
(* Case TyLam *)
apply tyann. apply (tylam L). intros.
pose (H0 x H1). destruct a. (*destruct H2. destruct x0.*)
apply (tysub _ _ B). auto. apply reflex. 
(* erasure of Lam *)
pick_fresh x. assert (has_type_source (extend x A Gamma) (open_source t0 (PFVar x)) B
                                      (open_source t1 (PFVar x))). 
apply (H x Fr).
assert ( has_ty (extend x A Gamma) (open_source t1 (PFVar x)) Inf B /\
         erase (open_source t1 (PFVar x)) = open_source t0 (PFVar x)).
apply (H0 x Fr). clear H H0. destruct H2.
unfold open_source in H0, H, H1. inversion H. clear H.
pose (erasure_open t1 0 t0 x H0). (* 
I think the theorem will require some additional pre-conditions which should be supplied here:

- From the typing relation we know various well-formedness properties hold, which 
will allow excluding the problematic BVar case. 

*)
rewrite e. reflexivity.
(* Case App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
apply (tyapp _ A).
inversion H1.
unfold has_ty. exists x. auto.
apply (tysub _ _ A). auto. apply reflex.
(* erasure of App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Merge *)
destruct IHhas_type_source1.
destruct IHhas_type_source2.
apply tymerge. auto. auto.
(* erasure of Merge *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Ann *)
destruct IHhas_type_source.
apply tyann. apply (tysub _ _ A). auto. auto.
destruct IHhas_type_source.
auto.
Defined.

Lemma erase_open : forall t n e,
                     erase (open_rec_source n e t) = open_rec_source n (erase e) (erase t).
induction t0; intros; simpl; try auto. destruct (Nat.eqb n0 n); auto.
(* don't know how to deal with this in Coq 8.5, but should be trivially true :) *)
rewrite (IHt0 (S n) e). reflexivity.
rewrite (IHt0_1 n e). rewrite (IHt0_2 n e). reflexivity.
rewrite (IHt0_1 n e). rewrite (IHt0_2 n e). reflexivity.
Defined.

Lemma typ_sound : forall e d A Gamma, has_ty Gamma e d A -> has_type Gamma (erase e) A.
intros.
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
apply tvar. auto.
(* PFLit *)
apply tlit.
(* App *)
apply (tapp _ A). auto. auto.
(* Merge *)
apply tmerge. auto. auto.
(* Ann *)
apply (tsub _ _ A). auto. apply reflex.
(* Lam *)
apply (tlam _ _ _ _ L). intros. pose (H0 x H1).
unfold open_source in h. unfold open_source.
rewrite (erase_open t0 0 (PFVar x)) in h. auto.
(* Sub *)
apply (tsub _ _ A). auto. unfold Sub. exists C. auto.
Defined.