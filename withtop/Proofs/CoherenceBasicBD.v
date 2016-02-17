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

Module EqFacts := BoolEqualityFacts(VarTyp).

(* Definitions borrowed from STLC_Tutorial *)

Definition context (A : Type) := list (var * A). 

Definition extend {A} (x : var) (a : A) (c : context A) : context A := c ++ ((x,a) :: nil).

Definition dom {A} (c : context A) : vars :=
  fold_right (fun el r => add (fst el) r) empty c.

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
  let C := gather_vars_with (fun (x : context PTyp) => dom x) in
  let D := gather_vars_with (fun x : PExp => fv_source x) in
  let E := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union C (union D E)))).

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

Parameter var_fresh : forall L : vars, {x : var | not (In x L) }.
  
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
  | PBVar i      => if Nat.eqb k i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x                     
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  end.

Definition open_source t u := open_rec_source 0 u t.

(** Target language **)
Fixpoint open_rec (k : nat) (u : SExp var) (t : SExp var) {struct t} : SExp var :=
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

Definition open (t : SExp var) u := open_rec 0 u t.

(* Functions on contexts *)
Definition mapctx {A B} (f : A -> B) (c : context A) : context B :=
  map (fun p => (fst p, (f (snd p)))) c. 

Definition conv_context (env : context PTyp) : context STyp :=
  mapctx ptyp2styp env.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).

Inductive ok {A} : context A -> Prop :=
  | Ok_nil : ok nil
  | Ok_push : forall (E : context A) (v : var) (ty : A),
                ok E -> not (In v (dom E)) -> ok (E ++ ((v,ty) :: nil)).        

Hint Constructors ok.

(* Typing rules of source language: Figure 2 
Note that we generate an Annotated expression, which serves as evidence for bi-directional
type-checking completness proof.
 *)

(* Declarative type system *)

Inductive has_type_source : context PTyp -> PExp -> PTyp -> PExp -> Prop :=
| TyVar : forall Gamma x ty,
            ok Gamma -> 
            List.In (x,ty) Gamma ->
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
                has_type_source Gamma (PMerge t1 t2) (And A B) (PMerge t1' t2')
  | TySub : forall Gamma t t' A B, has_type_source Gamma t A t' -> Sub A B -> has_type_source Gamma t B (PAnn t' B).

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
  | PTerm_Ann : forall e t,
      PTerm e ->
      PTerm (PAnn e t).  

Hint Constructors PTerm.
  
Lemma open_rec_term_source_core :forall t j v i u, i <> j ->
  open_rec_source j v t = open_rec_source i u (open_rec_source j v t) ->
  t = open_rec_source i u t.
Proof.
  intro t; induction t; intros; simpl.
  reflexivity.
  simpl in *.
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
  reflexivity.
  inversion H0.
  erewrite <- IHt.
  reflexivity.
  apply not_eq_S.
  apply H.
  apply H2.
  inversion H0.
  erewrite <- IHt1.
  erewrite <- IHt2.
  reflexivity.
  apply H.
  apply H3.
  apply H.
  apply H2.
  inversion H0.
  erewrite <- IHt1.
  erewrite <- IHt2.
  reflexivity.
  apply H.
  apply H3.
  apply H.
  apply H2.
  inversion H0.
  erewrite <- IHt.
  reflexivity.
  apply H.
  apply H2. 
Defined.


Lemma dom_union : forall (A : Type) (E G : context A) x,
  M.In x (dom (E ++ G)) <-> M.In x (M.union (dom E) (dom G)).
Proof.
Admitted. 

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Program.Equality.
Require Import MSetProperties.
Module MSetProperties := WPropertiesOn(VarTyp)(M).

Ltac not_in_L x :=
  repeat rewrite dom_union; repeat rewrite M.union_spec;
  repeat match goal with
    | H: M.In x M.empty |- _ => inversion H
    | H:_ |- context [M.In x (dom nil)] => simpl
    | H:_ |- context [M.In x (dom ((?v, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H: _ |- context [M.In ?v (dom ((x, ?t) :: ?l))] => simpl; rewrite MSetProperties.Dec.F.add_iff
    | H1: ~ ?l, H2: ?l |- _ => contradiction
    | H: ~ M.In ?y (M.singleton x) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; assumption 
    | H: ~ M.In x (M.singleton ?y) |- not (VarTyp.eq x ?y) => rewrite MSetProperties.Dec.F.singleton_iff in H; unfold not; intros; apply H; symmetry; assumption
    | H: ~ M.In x (M.add ?v M.empty) |- _ => rewrite <- MSetProperties.singleton_equal_add in H 
    | H: not (M.In x (dom ?l)) |- _ => rewrite dom_union in H; simpl in H
    | H: not (M.In x (M.union ?l1 ?l2)) |- _ =>
      rewrite M.union_spec in H
    | H: not (M.In x ?l3 \/ ?l) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (?l \/ M.In x ?l3) |- _ =>
      let l := fresh in
      let r := fresh in
      apply not_or_and in H; destruct H as [l r]
    | H: not (M.In x ?l1) |- not (M.In x ?l1) => assumption
    | H:_ |- ~ (x == ?v \/ M.In ?v ?l) => unfold not; intro HInv; inversion HInv as [HH | HH]
    | H:_ |- not (?A \/ ?B) => apply and_not_or; split
    | H1: ~ M.In x (M.singleton ?v), H2: ?v == x |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; assumption
    | H1: ~ M.In x (M.singleton ?v), H2: x == ?v |- _ => exfalso; apply H1; apply MSetProperties.Dec.F.singleton_2; symmetry; assumption
    | H: not (M.In x ?l1) |- not (M.In x ?l2) =>
      unfold not; intros; apply H; repeat rewrite M.union_spec; auto 10 
  end.

(** Substitution on indices is identity on well-formed terms. *)

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
  rewrite <- IHPTerm.
  reflexivity.
Defined.


Fixpoint subst (z : var) (u : PExp) (t : PExp) {struct t} : PExp :=
  match t with
    | PBVar i     => PBVar i
    | PFVar x     => if VarTyp.eqb x z then u else (PFVar x)
    | PLit i      => PLit i
    | PLam t1     => PLam (subst z u t1)
    | PApp t1 t2  => PApp (subst z u t1) (subst z u t2)
    | PMerge t1 t2 => PMerge (subst z u t1) (subst z u t2)
    | PAnn t1 t2  => PAnn (subst z u t1) t2 
  end.

Lemma subst_fresh : forall t x u, 
  not (In x (fv_source t)) -> subst x u t = t.
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
  (* Case PAnn *)
  simpl in *; rewrite IHt; auto.
Defined.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, PTerm u -> 
  subst x u (open_source t1 t2) = open_source (subst x u t1) (subst x u t2).
Proof.
  intros. unfold open_source. generalize 0.
  induction t1; intros; simpl.
  (* STFVar *)
  - case_eq (eqb v x); intros.
    rewrite <- open_rec_source_term; auto.
    simpl; reflexivity.
  (* STFVar *)
  - case_eq (Nat.eqb n0 n); intros; auto.
  (* STLit *)  
  - reflexivity.
  (* STLam *)
  - rewrite IHt1; reflexivity.
  (* STApp *)
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  (* STPair *)
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
  (* STProj1 *)
  - rewrite IHt1; reflexivity.
Defined.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall (x y : var) u t, not (x == y) -> PTerm u ->
  open_source (subst x u t) (PFVar y) = subst x u (open_source t (PFVar y)).
Proof.
  intros. rewrite subst_open. simpl.
  case_eq (eqb y x); intros.
  apply eqb_eq in H1.
  exfalso; apply H; symmetry. assumption.
  reflexivity.
  assumption.
Defined.
  
(** Opening up an abstraction of body [t] with a term [u] is the same as opening
  up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)

Lemma subst_intro : forall x t u, 
  not (In x (fv_source t)) -> PTerm u ->
  open_source t u = subst x u (open_source t (PFVar x)).
Proof.
  intros.
  rewrite subst_open; [ | assumption ].
  rewrite subst_fresh; [ | assumption ].
  simpl.
  case_eq (eqb x x); intros.
  reflexivity.
  rewrite EqFacts.eqb_neq in H1.
  exfalso.
  apply H1.
  reflexivity.
Defined.

(* ********************************************************************** *)
(** ** Preservation of local closure *)

(** The goal of this section is to set up the appropriate lemmas 
    for proving goals of the form [term t]. First, we defined a
    predicate capturing that a term [t] is the body of a locally
    closed abstraction. *)

Definition body t :=
  exists L, forall x, not (In x L) -> PTerm (open_source t (PFVar x)).

(** We then show how to introduce and eliminate [body t]. *)

Lemma term_abs_to_body : forall t1, 
  PTerm (PLam t1) -> body t1.
Proof.
  intros; unfold body; inversion H; subst; exists L; assumption.
Defined.

Lemma body_to_term_abs : forall t1, 
  body t1 -> PTerm (PLam t1).
Proof. intros. inversion H. apply_fresh PTerm_Lam as x. apply H0.
       unfold not in *. intros; apply Fry; apply union_spec; auto.
Defined.

(* Hint Resolve term_abs_to_body body_to_term_abs. *)

(** We prove that terms are stable by substitution *)

Lemma subst_term : forall t z u,
  PTerm u -> PTerm t -> PTerm (subst z u t).
Proof.
  induction 2; simpl; auto.
  destruct (eqb x z).
  assumption.
  (* Var *)
  - apply PTerm_Var.
  (* Lam *)
  - apply_fresh PTerm_Lam as x.
    rewrite subst_open_var.
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
Defined.

Hint Resolve subst_term.

Lemma type_correct_source_terms : forall Gamma E ty e, has_type_source Gamma E ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Defined.

Lemma typing_weaken : forall G E F t T d,
   has_type_source (E ++ G) t T d -> 
   ok (E ++ F ++ G) ->
   has_type_source (E ++ F ++ G) t T d.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent G.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply TyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
  (* STTyLam *)
  - unfold extend in *.
    apply_fresh TyLam as x.
    unfold open in *; simpl in *.
    unfold extend; do 2 rewrite <- app_assoc.
    apply H0.
    not_in_L x.
    rewrite HeqH'.
    rewrite app_assoc.
    reflexivity.
    rewrite app_assoc.
    rewrite app_assoc.
    apply Ok_push.
    rewrite <- app_assoc.
    assumption.
    repeat (rewrite dom_union; rewrite M.union_spec).
    repeat rewrite M.union_spec in Frx.
    repeat rewrite or_assoc in *.
    unfold not; intro HInv; destruct HInv as [HInv | [HInv | HInv]]; apply Frx; auto 8.
    assumption.
Defined.

Lemma typing_subst_core : forall F E t T z u U d,
  has_type_source (((extend z U) E) ++ F) t T d ->
  (exists d', has_type_source E u U d') ->
  has_type_source (E ++ F) (subst z u t) T d.
Proof.
  (*
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_abs as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
*)
Admitted.

(* Smart constructors *)

Definition has_type Gamma e t := exists s, has_type_source Gamma e t s.

Definition tvar : forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma -> has_type Gamma (PFVar x) ty.
intros.  unfold has_type. exists (PFVar x). auto.
Defined.

Definition tlit : forall Gamma x, ok Gamma -> has_type Gamma (PLit x) PInt.
intros. unfold has_type. exists (PLit x); auto.
Defined.

Definition tlam : forall L Gamma t A B, (forall x, not (In x L) -> 
                                 has_type (extend x A Gamma) (open_source t (PFVar x)) B) ->
                               has_type Gamma (PLam t) (Fun A B).
intros. 
unfold has_type.
unfold has_type in H.
pick_fresh y.
rewrite union_spec in Fr.
apply not_or_and in Fr as [notLG notFvT].
rewrite union_spec in notLG.
apply not_or_and in notLG as [notL notG].
pose (H y notL).
destruct e.
exists (PAnn (PLam x) (Fun A B)).
apply_fresh TyLam as z.
intros.

assert (forall {y z}, not (z = y) -> not (In y (fv_source t0)) -> not (In z (fv_source t0)) -> has_type_source (extend y A Gamma) (open_source t0 (PFVar y)) B x -> has_type_source (extend z A Gamma) (open_source t0 (PFVar z)) B x).
intros.
rewrite subst_intro with (x := y0). Check typing_subst_core.
rewrite <- app_nil_r with (l := (extend z0 A Gamma)).
apply typing_subst_core with (U := A).
assert (forall t, has_type_source (extend z0 A (extend y0 A Gamma) ++ nil) t B x ->
has_type_source (extend y0 A (extend z0 A Gamma) ++ nil) t B x). admit.
apply H5.
unfold extend.
rewrite <- app_assoc.
apply typing_weaken.
unfold extend in H4.
rewrite app_nil_r.
assumption.
apply Ok_push.
apply Ok_push.
admit.
admit.
admit. 
exists (PFVar z0).
apply TyVar.
apply Ok_push.
admit.
admit.
unfold extend; apply in_or_app.
right; left; reflexivity.
assumption. 
apply PTerm_Var.
repeat rewrite union_spec in Frz.
apply not_or_and in Frz.
destruct Frz.
apply not_or_and in H2.
destruct H2.
apply not_or_and in H2.
destruct H2.
assert (Hnot : not (z = y)). admit.
pose (H1 _ _ Hnot notFvT H4) as e. apply e in H0. clear e.
unfold open_source.
assert (open_rec_source 0 (PFVar z) x = x).
rewrite <- open_rec_source_term.
reflexivity.
admit.
rewrite H6. auto.
admit.
Admitted.

Inductive Dir := Inf | Chk.

(* bidirection type-system (algorithmic): 

T |- e => t ~> E     (inference mode: infers the type of e producing target E) (use Inf)
T |- e <= t ~> E     (checking mode: checks the type of e producing target E) (use Chk)

Inspiration for the rules:

https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

*)

Inductive has_type_source_alg : context PTyp -> PExp -> Dir -> PTyp -> (SExp var) -> Prop :=
  (* Inference rules *)
  | ATyVar : forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x) 
  | ATyLit : forall Gamma x, ok Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
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
  | ATyLam : forall L Gamma t A B E, (forall x, not (In x L) -> 
                                 has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B E) -> WFTyp A ->
                           has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam _ E)
  | ATySub : forall Gamma t A B C E, has_type_source_alg Gamma t Inf A E -> sub A B C -> has_type_source_alg Gamma t Chk B (STApp _ (C var) E).

Hint Constructors has_type_source_alg.

(* Ignoring the generated expressions + smart constructors *)

Definition has_ty Gamma e d t := exists E, has_type_source_alg Gamma e d t E.

Definition tyvar : forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma ->
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
                has_ty Gamma (PMerge t1 t2) Inf (And A B).
intros.
inversion H. inversion H0.
unfold has_ty. exists (STPair _ x x0). apply ATyMerge. auto. auto.
Defined.

Definition tyann : forall Gamma t1 A, has_ty Gamma t1 Chk A -> has_ty Gamma (PAnn t1 A) Inf A.
intros. inversion H. unfold has_ty. exists x. apply ATyAnn. auto.
Defined.


Definition tylam : forall {Gamma t A B} L,
  (forall x, not (In x L) -> 
        has_ty (extend x A Gamma) (open_source t (PFVar x)) Chk B) ->
  has_ty Gamma (PLam t) Chk (Fun A B).
intros.
unfold has_ty.  
unfold has_ty in H.
pick_fresh y. 
rewrite union_spec in Fr.
apply not_or_and in Fr.
destruct Fr.
rewrite union_spec in H0.
apply not_or_and in H0.
destruct H0.
pose (H y H0). destruct e. exists (STLam _ (STLam var x)).
apply_fresh ATyLam as x.
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


Lemma list_impl_m : forall {A} Gamma x (v : A), List.In (x, v) Gamma -> M.In x (dom Gamma).
Proof.
  intros.
  induction Gamma.
  inversion H.
  simpl.
  destruct a.
  simpl in *.
  inversion H.
  apply MSetProperties.Dec.F.add_1.
  apply f_equal with (f := fst) in H0.
  simpl in H0.
  rewrite H0.
  reflexivity.
  apply MSetProperties.Dec.F.add_2.
  apply IHGamma; assumption.
Defined.

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
  
  destruct B.
  right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv.
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
Defined.

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
  apply in_app_or in H5.
  apply in_app_or in H6.
  inversion H5; inversion H6.
  apply list_impl_m in H7; apply (MSetProperties.Dec.F.In_1 H4) in H7; contradiction.
  apply list_impl_m in H7; apply (MSetProperties.Dec.F.In_1 H4) in H7; contradiction.
  apply list_impl_m in H8; apply (MSetProperties.Dec.F.In_1 H4) in H8; contradiction.
  inversion H7.
  inversion H9.
  subst.
  inversion H8.
  inversion H10; subst; reflexivity.
  inversion H10.
  inversion H9.

  inversion H3.
  simpl in *; subst.
  inversion H0.
  apply in_app_or in H5.
  apply in_app_or in H6.
  inversion H5; inversion H6.  
  apply list_impl_m in H7; apply (MSetProperties.Dec.F.In_1 H4) in H7; contradiction.
  apply list_impl_m in H7; apply (MSetProperties.Dec.F.In_1 H4) in H7; contradiction.
  apply list_impl_m in H8; apply (MSetProperties.Dec.F.In_1 H4) in H8; contradiction.
  inversion H7.
  inversion H9; subst; reflexivity.
  inversion H9.
    
  apply IHok.
  inversion H0; clear H0.
  split; [ (apply in_app_or in H4; inversion H4) | (apply in_app_or in H5; inversion H5) ]; try assumption; inversion H0; inversion H6; simpl in *; subst;
  exfalso; [ apply H2 | apply H3 ]; reflexivity.
Defined.
  

Lemma typ_unique : forall Gamma e d t1 E1, has_type_source_alg Gamma e d t1 E1 -> forall t2 E2, has_type_source_alg Gamma e d t2 E2 -> almost_unique t1 t2 d.
intros Gamma e d t1 E1 H.
induction H; intros; unfold almost_unique.
(* case Var *)
- inversion H1; subst.
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
- inversion H1.
  apply IHhas_type_source_alg1 in H5.
  apply IHhas_type_source_alg2 in H6.
  rewrite H5. rewrite H6. auto.
(* Case Ann *)
- inversion H0. auto.
(* Case Lam *)
- auto.
(* case Sub *)
- auto.
Defined.

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
(* Case Merge *)
inversion H.
apply IHe1 in H5.
apply IHe2 in H7.
apply (tymerge). auto. auto.
(* Case Ann *)
inversion H. subst.
apply tyann. 
pick_fresh x.
assert (H1 : not (In x L)). not_in_L x.
pose (H5 x H1) as e. 
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
simpl in H5.
apply IHe in H5.
apply (tysub _ _ A). auto. auto.
Admitted.

Lemma typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.
intros Gamma e d t E1 H.
induction H; intros.
(* case PFVar *)
- inversion H1; reflexivity. 
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
- inversion H1.
  apply IHhas_type_source_alg1 in H7.
  apply IHhas_type_source_alg2 in H9.
  rewrite H7. rewrite H9. auto.
(* Case Ann *)
- inversion H0.
  apply IHhas_type_source_alg in H3. auto.
(* Case Lam *)
- inversion H1.
  admit.
  inversion H2.
  admit.
  admit.
  admit.
(* ATySub *)
- inversion H1.
  subst.
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


(* Type preservation: Theorem 1 *)
Lemma type_preservation : forall x ty E (Gamma : context PTyp) (x : has_type_source Gamma x ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Admitted.



(* Completeness *)

(*
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
pick_fresh y. pose (H0 y Fr). pose (H y Fr). destruct a.
simpl in H2. inversion H1. rewrite <- H2 in h.
pose (erasure_typing h). inversion h0. inversion H4. clear H H0 H1.
unfold open_source in H5.
destruct t1; simpl in H5; inversion H5. simpl.
simpl in H2. unfold open_source in H2.
destruct t0; simpl in H2; inversion H2. auto.
destruct n. admit. inversion H1. destruct n. simpl.
destruct t0; simpl in H2; inversion H2. admit.
unfold open_source in H1. simpl in H1. destruct n. auto.
inversion H1. simpl. inversion H0.
destruct t1; unfold open_source in H7; inversion H7. destruct n; inversion H10.
simpl. simpl in H7. simpl in H2.
destruct t0; unfold open_source in h; inversion H2. unfold open_source in H11. simpl in H11.
destruct n; inversion H11. destruct n0; inversion H12. destruct n0; inversion H12. auto.
destruct t1; unfold open_source in H5; inversion H5.
destruct n; inversion H12. simpl.
unfold open_source in H2. simpl in H2. simpl in H5.
destruct t0; unfold open_source in H2; inversion H2.
destruct n; inversion H14. simpl in H2.
(* probably an auxialiary lemma here *)
admit. admit. admit.
(* Case App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
destruct H1. destruct H3. eapply ex_intro. apply (tyapp _ A).
destruct x. 
inversion H1.
unfold has_ty. exists x. auto.
inversion H. apply tyvar. auto. apply tyann.
rewrite <- H8 in H1.
inversion H1. inversion H11. inversion H12.
unfold has_ty. exists E. auto.
rewrite <- H10 in H1.
rewrite <- H2 in H. rewrite <- H10 in H2. simpl in H2. rewrite <- H10 in H.
apply (erasure_typing H).
rewrite <- H2 in H.
pose (erasure_typing H).
rewrite <- H10 in h. auto.
destruct x0.
apply (tysub _ _ A). auto. apply reflex. auto.
(* erasure of App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Merge *)
destruct IHhas_type_source1.
destruct IHhas_type_source2.
exists Inf. destruct H1. destruct H3.
apply tymerge.
destruct x. auto.
inversion H1. inversion H5.
rewrite <- H8 in H. rewrite <- H10 in H. inversion H.
rewrite <- H2 in H.
apply (erasure_typing H).
destruct x0. auto. destruct H3. inversion H3.
rewrite <- H7 in H0. rewrite <- H9 in H0. inversion H0.
rewrite <- H4 in H0.
apply (erasure_typing H0).
(* erasure of Merge *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Ann *)
exists Inf.
destruct IHhas_type_source.
destruct H1. destruct x.
apply tyann. apply (tysub _ _ A). auto. auto.
apply tyann. apply (tysub _ _ A). rewrite <- H2 in H.
apply (erasure_typing H). auto.
destruct IHhas_type_source.
auto.*)


Lemma typ_complete : forall {Gamma e t e'},
  has_type_source Gamma e t e' -> (exists d, has_ty Gamma e' d t) /\ erase e' = e.
intros Gamma e t e' H.
induction H; intros; split; try (simpl; auto).
(* Case TyVar *)
exists Inf. apply tyvar. auto.
(* Case TyLit *)
exists Inf. apply tylit.
(* Case TyLam *)
exists Inf. apply tyann. apply (tylam L). intros.
pose (H0 x H1). destruct a. destruct H2. destruct x0.
apply (tysub _ _ B). auto. apply reflex. auto.
(* erasure of Lam *)
pick_fresh y. pose (H0 y Fr). pose (H y Fr). destruct a.
simpl in H2. inversion H1. rewrite <- H2 in h.
pose (erasure_typing h). inversion h0. inversion H4. clear H H0 H1.
unfold open_source in H5.
destruct t1; simpl in H5; inversion H5. simpl.
simpl in H2. unfold open_source in H2.
destruct t0; simpl in H2; inversion H2. auto.
destruct n. admit. inversion H1. destruct n. simpl.
destruct t0; simpl in H2; inversion H2. admit.
unfold open_source in H1. simpl in H1. destruct n. auto.
inversion H1. simpl. inversion H0.
destruct t1; unfold open_source in H7; inversion H7. destruct n; inversion H10.
simpl. simpl in H7. simpl in H2.
destruct t0; unfold open_source in h; inversion H2. unfold open_source in H11. simpl in H11.
destruct n; inversion H11. destruct n0; inversion H12. destruct n0; inversion H12. auto.
destruct t1; unfold open_source in H5; inversion H5.
destruct n; inversion H12. simpl.
unfold open_source in H2. simpl in H2. simpl in H5.
destruct t0; unfold open_source in H2; inversion H2.
destruct n; inversion H14. simpl in H2.
(* probably an auxialiary lemma here *)
admit. admit. admit.
(* Case App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
destruct H1. destruct H3. eapply ex_intro. apply (tyapp _ A).
destruct x. 
inversion H1.
unfold has_ty. exists x. auto.
inversion H. apply tyvar. auto. apply tyann.
rewrite <- H8 in H1.
inversion H1. inversion H11. inversion H12.
unfold has_ty. exists E. auto.
rewrite <- H10 in H1.
rewrite <- H2 in H. rewrite <- H10 in H2. simpl in H2. rewrite <- H10 in H.
apply (erasure_typing H).
rewrite <- H2 in H.
pose (erasure_typing H).
rewrite <- H10 in h. auto.
destruct x0.
apply (tysub _ _ A). auto. apply reflex. auto.
(* erasure of App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Merge *)
destruct IHhas_type_source1.
destruct IHhas_type_source2.
exists Inf. destruct H1. destruct H3.
apply tymerge.
destruct x. auto.
inversion H1. inversion H5.
rewrite <- H8 in H. rewrite <- H10 in H. inversion H.
rewrite <- H2 in H.
apply (erasure_typing H).
destruct x0. auto. destruct H3. inversion H3.
rewrite <- H7 in H0. rewrite <- H9 in H0. inversion H0.
rewrite <- H4 in H0.
apply (erasure_typing H0).
(* erasure of Merge *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
rewrite H2. rewrite H4. auto.
(* Case Ann *)
exists Inf.
destruct IHhas_type_source.
destruct H1. destruct x.
apply tyann. apply (tysub _ _ A). auto. auto.
apply tyann. apply (tysub _ _ A). rewrite <- H2 in H.
apply (erasure_typing H). auto.
destruct IHhas_type_source.
auto.
Admitted.

(*
Lemma typ_sub : forall e t0 A Gamma, has_type_source Gamma e A t0 -> forall B, Sub A B ->
                                                                               has_type_source Gamma e B t0.
intros e t0 A Gamma H. induction H; intros.
(* Var *)
apply TyVar.
destruct H. simpl.
simpl. *)

Require Import Program.Equality.

(*
Lemma typ_sound : forall e d A Gamma, has_ty Gamma e d A -> has_type_source Gamma (erase e) A e.
intros.
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
apply TyVar. auto.
(* PFLit *)
apply TyLit.
(* App *)
apply (TyApp _ A). auto. auto.
(* Merge *)
apply TyMerge. auto. auto.
(* Ann *)
apply (TySub _ _ _ A). auto. apply reflex.
(* Lam *)
pick_fresh y. assert (not (In y L)). admit.
pose (H y H1). pose (H0 y H1). admit.
(* Sub *)
admit.*)

(*
Inductive EForm e t : PExp -> Prop  :=
| EBase : EForm e t e
| EStep : forall e', EForm e t e' -> EForm e t (PAnn e' t).

Lemma typ_erase : forall e Gamma t e', has_type_source Gamma (erase e) t e' -> e = e'.
induction e; intros; simpl in H.
(* Case PFVar *)
inversion H. auto.
destruct e; simpl in x; inversion x. apply EBase.
auto. destruct e; simpl in x; inversion x. simpl in H1.
 *)

Lemma typ_erasures : forall Gamma e t e1, has_type_source Gamma e t e1 -> forall e2, has_type_source Gamma e t e2 -> erase e1 = erase e2.
intros.
pose (typ_complete H). pose (typ_complete H0). destruct a. destruct a0. rewrite H2. rewrite H4.
reflexivity.
Defined.

(* Inductive Erasable : PExp -> PExp *)

Lemma typ_erasures2 : forall Gamma e d t e2, has_ty Gamma e2 d t
       -> forall e1, has_type_source Gamma e t e1 -> 
                                          erase e1 = erase e2 -> has_type_source Gamma e t e2.    intros Gamma e d t e2 H.
inversion H.  
induction H0; intros.
simpl in H2.
destruct H1; simpl in H2; inversion H2.
apply TyVar. auto.
destruct H3.
destruct t'; simpl in H5; inversion H5.
simpl. rewrite H6 in H1. inversion H1.
apply TyVar. auto. simpl.

simpl. simpl in H2.
destruct t'; simpl in H2; inversion H2.
inversion H1. simpl. rewrite <- H8 in H13.
rewrite H7 in H12.
inversion H1. simpl.


Lemma typ_sound : forall e d t Gamma, has_ty Gamma e d t -> exists e', has_type_source Gamma (erase e) t e' /\ (erase e = erase e').
intros.
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
eapply ex_intro. split. apply TyVar. auto. simpl. auto.
(* PFLit *)
eapply ex_intro. split. apply TyLit. auto.
(* App *)
destruct IHhas_type_source_alg1. destruct H. destruct IHhas_type_source_alg2. destruct H1.
eapply ex_intro. split.
apply (TyApp _ A).  exact H. exact H1.
simpl. rewrite H0. rewrite H2. auto.
(* Merge *)
destruct IHhas_type_source_alg1. destruct H. destruct IHhas_type_source_alg2. destruct H1.
eapply ex_intro. split.
apply TyMerge. exact H. exact H1.
simpl. rewrite H0. rewrite H2. auto.
(* Ann *)
destruct IHhas_type_source_alg. destruct H.
exists x. auto.
(* Lam *)
(*
pick_fresh y. assert (not (In y L)). admit.
pose (H y H1). pose (H0 y H1). destruct e. destruct H2.
inversion h. (*rewrite <- H4 in H3. simpl in H3. rewrite H4 in H2.*)
destruct t0; unfold open_source in H4; simpl in H4; inversion H4.
destruct n; inversion H10. simpl in H3. unfold open_source in H2. simpl in H2.
destruct x; simpl in H3; inversion H3. inversion H2. simpl.
clear H11.
exists (PAnn (PAnn x p) (Fun A (Fun A0 B0))). split.
apply (TyLam _ _ _ _ _ L). intros. rewrite <- H8 in H2.*)
exists (PAnn (PLam t0) (Fun A B)). split.
apply (TyLam _ _ _ _ _ L). intros.
pose (H x H1). pose (H0 x H1). destruct e. destruct H2.
inversion h. rewrite <- H4 in H3. simpl in H3. rewrite <- H4 in H2. simpl in H2.
destruct t0; unfold open_source in H4; simpl in H4; inversion H4.
destruct n; inversion H10. unfold open_source. simpl.
destruct x0; simpl in H3; inversion H3. inversion H2.
pose (typ_complete H2). destruct a. 
rewrite H10 in H11.
admit.
admit. (* some inductive property? *)
(*destruct x0; unfold open_source in H3; simpl in H3; inversion H3.*) 
simpl. auto.
(* Sub *)
destruct IHhas_type_source_alg. destruct H1.
exists (PAnn x B). split.
apply (TySub _ _ _ A). auto.
unfold Sub. exists C. auto.
simpl. auto.
Admitted.

Inductive soundness Gamma : PExp -> PTyp -> Dir -> Prop :=
| SInf : forall e t, has_type_source Gamma (erase e) t e -> soundness Gamma e t Inf
| SChk : forall d e t, soundness Gamma e t d -> soundness Gamma (PAnn e t) t Chk
| SChkInf : forall e t, soundness Gamma e t Inf -> soundness Gamma e t Chk.

(*
Definition soundness Gamma e t  (d : Dir) : Prop := 
  match d with
    | Inf => has_type_source Gamma (erase e) t e
    | Chk => has_type_source Gamma (erase e) t (PAnn e t) (* Something needed here? *)
  end.


Definition soundness Gamma e t  (d : Dir) : Prop := 
  match d with
    | Inf => has_type_source Gamma (erase e) t e
    | Chk => exists e', has_type_source Gamma (erase e) t e' (* Something needed here? *)
  end.
*)

Lemma soundness_aux : forall {Gamma e A d}, soundness Gamma e A d -> has_type_source Gamma (erase e) A (PAnn e A).
intros.
induction H.
apply (TySub _ _ _ t0). auto. apply reflex.
simpl. apply (TySub _ _ _ t0). auto. apply reflex.
auto.
Defined.

Lemma typ_sound : forall e d t Gamma, has_ty Gamma e d t -> soundness Gamma e t d.
intros.
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
apply SInf. apply TyVar. auto.
(* PFLit *)
apply SInf. apply TyLit.
(* App *)
apply SInf. simpl.
apply (TyApp _ A).
inversion IHhas_type_source_alg1. auto.
inversion IHhas_type_source_alg2. simpl.
apply (soundness_aux H).
inversion H. auto.
(* Merge *)
apply SInf. simpl.
inversion IHhas_type_source_alg1. inversion IHhas_type_source_alg2.
apply TyMerge. exact H. exact H2.
(* Ann *)
apply SInf. simpl.
inversion IHhas_type_source_alg. simpl. apply (TySub _ _ _ A).
apply (soundness_aux H). apply reflex.
inversion H. apply (TySub _ _ _ A). auto. apply reflex.
(* Lam *)
apply SChkInf. apply SInf. simpl.
pick_fresh y. assert (not (In y L)). admit.
pose (H0 y H1). pose (H y H1). admit.
inversion h. admit. rewrite <- H2 in h. admit.
(*
inversion h. destruct t0; unfold open_source in H2; inversion H2. destruct n; inversion H12.
simpl.*)
admit.

admit.
(* Sub *)
(* auxiliary lemma ? *)
generalize H0 IHhas_type_source_alg. generalize Gamma t0 E. clear Gamma H0 IHhas_type_source_alg t0 E.
induction H; intros; inversion IHhas_type_source_alg.
apply SChkInf. apply SInf. auto.

inversion H0. rewrite <- H5 in H. simpl in H.
(* exists (PAnn x B). *)
apply (TySub _ _ _ A). auto.
unfold Sub. exists C. auto.

Lemma typ_sound : forall e d t Gamma, has_ty Gamma e d t -> exists e', has_type_source Gamma (erase e) t e'.
intros.
inversion H. clear H.
induction H0; simpl.
(* PFVar *)
eapply ex_intro. apply TyVar. auto.
(* PFLit *)
eapply ex_intro. apply TyLit.
(* App *)
destruct IHhas_type_source_alg1. destruct IHhas_type_source_alg2.
eapply ex_intro.
apply (TyApp _ A).  exact H. exact H0.
(* Merge *)
destruct IHhas_type_source_alg1. destruct IHhas_type_source_alg2.
eapply ex_intro.
apply TyMerge. exact H. exact H0.
(* Ann *)
destruct IHhas_type_source_alg.
exists x. auto.
(* Lam *)
pick_fresh y. assert (not (In y L)). admit.
(*apply (TyLam _ _ _ _ _ L). intros.*)
pose (H y H1). pose (H0 y H1).
destruct e.
exists (PAnn (PLam x) (Fun A B)).
apply (TyLam _ _ _ _ _ L). intros.
inversion h.
unfold open_source in H4. destruct t0; simpl in H4; inversion H4.
destruct n; inversion H10. simpl.

simpl.
apply (TySub _ _ _ (Fun A B)).
admit.
(*
eapply ex_intro.
pick_fresh y. assert (not (In y L)). admit.
pose (H y H1). pose (H0 y H1).
destruct e.
inversion H2.
destruct t0; unfold open_source in H3; simpl in H3; inversion H3.
simpl in H2.
admit.

exists (PAnn (PLam t0) (Fun A B)).
apply (TyLam _ _ _ _ _ L). intros.
pose (H x H1). pose (H0 x H1).
destruct e.
*)
(*
unfold open_source in H2. unfold open_source in h. unfold open_source.
destruct t0; simpl; simpl in H2; simpl in h. inversion H2.
rewrite <- H7 in H2. auto. admit. destruct n.

inversion H2; unfold open_source; simpl; unfold open_source in H2; simpl in H2.
destruct t0; unfold open_source in H3; simpl in H3; inversion H3. simpl. simpl in H2.
rewrite H9 in H7. rewrite <- H7 in H2. auto.
destruct n; inversion H9. simpl in H2. simpl. rewrite H10 in H7. rewrite <- H7 in H2. auto.
simpl. simpl in H2.

unfold open_source. simpl.
rewrite <- H7 in H2. destruct t0; simpl in H9. simpl. simpl in H2.
admit.*)
(* Sub *)
destruct IHhas_type_source_alg.
exists (PAnn x B).
apply (TySub _ _ _ A). auto.
unfold Sub. exists C. auto.
Admitted.



