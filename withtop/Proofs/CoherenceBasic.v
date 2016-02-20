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

(* typing rules of lambda i *)

Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.
Require Import STLC.

Module CoherenceBasic
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  
Module ST := TLC(VarTyp)(set).
Import ST.  
  

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

Inductive sub : PTyp -> PTyp -> (SExp var) -> Prop :=
  | SInt : sub PInt PInt (STLam _ STInt (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun o3 o4) (STLam _ (ptyp2styp (Fun o1 o2)) (STLam _ (ptyp2styp o3) (STApp _ (c2) (STApp _ (STBVar _ 1) (STApp _ (c1) (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (STLam _ (ptyp2styp t)
       (STPair _ (STApp _ (c1) (STBVar _ 0)) (STApp _ (c2) (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam _ (ptyp2styp (And t1 t2)) 
       ((STApp _ (c) (STProj1 _ (STBVar _ 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam _ (ptyp2styp (And t1 t2)) 
       ((STApp _ (c) (STProj2 _ (STBVar _ 0))))).

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp var), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (STLam _ STInt (STBVar _ 0)). 
exact SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (STLam _ (ptyp2styp (Fun o1 o2)) ( 
       STLam _ (ptyp2styp o3) (STApp _ (x0) (STApp _ (STBVar _ 1) (STApp _ (x) (STBVar _ 0)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (STLam _ (ptyp2styp t0) (
       STPair _ (STApp _ (x) (STBVar _ 0)) (STApp _ (x0) (STBVar _ 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t0. destruct H.
exists (STLam _ (ptyp2styp (And t1 t2)) ( 
       (STApp _ (x) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto. destruct H.
exists (STLam _ (ptyp2styp (And t1 t2)) (
       (STApp _ (x) (STProj1 _ (STBVar _ 0))))).
apply SAnd2. auto. auto.
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
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
exists (STLam _ (ptyp2styp (And t0 t3)) (
       STPair _ (STApp _ (x0) (STBVar _ 0)) (STApp _ (x1) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And t1 t2) t.
unfold Sub. intros t t1 t2 H H0. destruct t. destruct H.
exists (STLam _ (ptyp2styp (And t1 t2)) ( 
       (STApp _ (x) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto. destruct H.
exists (STLam _ (ptyp2styp (And t1 t2)) ( 
       (STApp _ (x) (STProj2 _ (STBVar _ 0))))).
apply SAnd3. auto. auto.
inversion H0.
Defined.

(* Theorem 4 *)

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
intro t.
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
exists (STLam _ (ptyp2styp (And t0 t3)) (
       STPair _ (STApp _ (x0) (STBVar _ 0)) (STApp _ (x1) (STBVar _ 0)))).
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
intro t.
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

Lemma sub_coherent : forall A, WFTyp A -> forall B, WFTyp B -> forall C1, sub A B C1 -> forall C2, sub A B C2 -> C1 = C2.
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
destruct H14. exists t0. unfold Sub.
split. exists c; auto. exists c0. auto.
(* Case: And t1 t2 <: t (second) *)
inversion H3; inversion H.
rewrite <- H7 in H2. inversion H2.
(* contradiction: not orthogonal! *)
destruct H14. exists t0. unfold Sub.
split. exists c0; auto. exists c. auto.
(* same coercion; no contradiction *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
Defined.


(* typing rules of lambda i *)

(*
Module M := MSetWeakList.Make(VarTyp).
Export M.

Module EqFacts := BoolEqualityFacts(VarTyp).


Definition vars := M.t.

(* Definitions borrowed from STLC_Tutorial *)

Definition context (A : Type) := list (var * A). 

Definition extend {A} (x : var) (a : A) (c : context A) : context A := c ++ ((x,a) :: nil).

Definition dom {A} (c : context A) : vars :=
  fold_right (fun el r => add (fst el) r) empty c.
 *)

(* Our source language *)
Inductive PExp :=
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp                   
  | PLit   : nat -> PExp
  | PLam   : PTyp -> PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp.

(* Free variables *)

(** Source language **)
Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
    | PFVar v => singleton v
    | PBVar _ => empty
    | PLit _ => empty
    | PLam _ t => fv_source t
    | PApp t1 t2 => union (fv_source t1) (fv_source t2)
    | PMerge t1 t2 => union (fv_source t1) (fv_source t2)
  end.

(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)
(*
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
*)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  let C := gather_vars_with (fun (x : context STyp) => dom x) in
  let D := gather_vars_with (fun x : PExp => fv_source x) in
  let E := gather_vars_with (fun (x : SExp var) => fv x) in
  constr:(union A (union B (union C (union D E)))).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i    => if Nat.eqb k i then u else (PBVar i)
  | PFVar x    => PFVar x
  | PLit x     => PLit x                     
  | PLam ty t1 => PLam ty (open_rec_source (S k) u t1)
  | PApp t1 t2 => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  end.

Definition open_source t u := open_rec_source 0 u t.


(* Functions on contexts *)

Definition conv_context (env : context PTyp) : context STyp :=
  mapctx ptyp2styp env.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).

(*
Reserved Notation "Gamma '|-' t ':' T" (at level 40).
*)

(* Typing rules of source language: Figure 2 *)
Inductive has_type_source : (context PTyp) -> PExp -> PTyp -> (SExp var) -> Prop :=
  | TyVar : forall Gamma x ty,
              ok Gamma -> List.In (x,ty) Gamma ->
              WFTyp ty -> has_type_source Gamma (PFVar x) ty (STFVar _ x)
  | TyLit : forall Gamma x, ok Gamma -> has_type_source Gamma (PLit x) PInt (STLit _ x)
  | TyLam : forall L Gamma t A B E, (forall x, not (In x L) -> 
                                 has_type_source (extend x A Gamma) (open_source t (PFVar x)) B E) -> WFTyp A -> 
                           has_type_source Gamma (PLam A t) (Fun A B) (STLam _ (|A|) E) 
  | TyApp : forall Gamma A B C t1 t2 E E1 E2,
              has_type_source Gamma t1 (Fun A B) E1 ->
              has_type_source Gamma t2 C E2 ->
              sub C A E -> 
              has_type_source Gamma (PApp t1 t2) B (STApp _ E1 (STApp _ E E2))
  | TyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source Gamma t1 A E1 ->
                has_type_source Gamma t2 B E2 ->
                OrthoS A B -> 
                has_type_source Gamma (PMerge t1 t2) (And A B) (STPair _ E1 E2).


Hint Constructors has_type_source.

Lemma ptyp2styp_function : forall x y, x = y -> |x| = |y|.
Proof.                                                     
  induction x; intros.
  - inversion H; reflexivity.
  - rewrite <- H; reflexivity.
  - rewrite <- H; reflexivity.
Defined.  

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
Defined.

Lemma exists_persists : forall l x v,
  List.Exists (fun p : var * PTyp => (fst p) = x /\ (snd p) = v) l ->
  List.Exists (fun p : var * STyp => (fst p) = x /\ (snd p) = (|v|)) (∥ l ∥).
Proof.
  intros.
  induction H.
  simpl.
  apply Exists_cons_hd.
  simpl; destruct H as [H1 H2]; split; [ | apply ptyp2styp_function ]; assumption.
  
  unfold conv_context in *.
  simpl.
  apply Exists_cons.
  auto.
Defined.  

Lemma free_vars_in :
  forall t1 x y n, In x (fv t1) ->
  In x (fv (open_rec n (STFVar var y) t1)).
Proof.
  intro t.
  induction t; intros; try auto.
  (* STBVar *)
  simpl in *; inversion H.
  (* STLam *)
  simpl in *.
  apply IHt; assumption.
  simpl.
  apply IHt.
  now simpl in H.
  (* STApp *)
  simpl in *.
  apply union_spec.
  apply union_spec in H.
  destruct H.
  left; apply IHt1; assumption.
  right; apply IHt2; assumption.
  (* STPair *)
  simpl in *.
  apply union_spec in H.
  apply union_spec.
  destruct H.
  left; apply IHt1; assumption.
  right; apply IHt2; assumption.
  (* STProj1 *)
  simpl in *; apply IHt; assumption.
  (* STProj2 *)
  simpl in *; apply IHt; assumption.
Defined.

(*
Fixpoint subst (z : var) (u : Exp) (t : Exp) {struct t} : Exp :=
  match t with
    | STBVar _ i     => STBVar _ i
    | STFVar _ x     => if VarTyp.eqb x z then u else (STFVar _ x)
    | STLit _ i      => STLit _ i
    | STLam _ A t1   => STLam _ A (subst z u t1)
    | STApp _ t1 t2  => STApp _ (subst z u t1) (subst z u t2)
    | STPair _ t1 t2 => STPair _ (subst z u t1) (subst z u t2)
    | STProj1 _ t    => STProj1 _ (subst z u t)
    | STProj2 _ t    => STProj2 _ (subst z u t)
  end.

Require Import Coq.Init.Peano.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^ x" := (open t (STFVar var x)).
Notation "t ^^ u" := (open t u) (at level 67).

Lemma subst_fresh : forall t x u, 
  not (In x (fv t)) ->  [x ~> u] t = t.
Proof.
  intro t.
  induction t; intros; auto.
  (* Case STFVar *)
  simpl.
  remember (eqb a x) as H1.
  destruct H1.
  exfalso.
  apply H.
  unfold fv; simpl.
  apply singleton_spec.
  symmetry in HeqH1.
  apply eqb_eq in HeqH1; symmetry; assumption.
  reflexivity.
  (* Case STLam *)
  simpl in *.
  rewrite IHt; auto.
  (* Case STApp *)
  simpl in *; rewrite IHt1, IHt2; auto; unfold not in *; intros;
  apply H; apply union_spec; [ right | left ]; auto.
  (* Case STPair *)
  simpl in *; rewrite IHt1, IHt2; auto; unfold not in *; intros;
  apply H; apply union_spec; [ right | left ]; auto.
  (* Case STProj1 *)
  simpl in *; rewrite IHt; auto.
  (* Case STProj2 *)
  simpl in *; rewrite IHt; auto.
Defined.

(* ********************************************************************** *)
(** ** Proving the two axioms *)

(** We first set up four lemmas, and then we can prove our two axioms. *)

(** The first lemma is a technical auxiliary lemma which do not 
    want and do not need to read. *)


Lemma open_rec_term_core :forall t j v i u, i <> j ->
  { j ~> v }t = { i ~> u }({ j ~> v }t) -> t = { i ~> u }t.
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
  unfold open_rec in H0.
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
  inversion H0.
  erewrite <- IHt.
  reflexivity.
  apply H.
  apply H2.  
Defined.

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term : forall t u,
  STTerm  t -> forall k, t =  { k ~> u }t.
Proof.
  induction 1; intros; simpl; auto.
  pick_fresh x.
  rewrite <- open_rec_term_core with (j := 0) (v := STFVar _ x).
  reflexivity.
  auto.
  simpl.
  unfold open in *.
  rewrite <- H0.
  reflexivity.
  unfold not; intros; apply Fr; rewrite union_spec; rewrite union_spec; left; left.
  assumption.
  rewrite <- IHSTTerm1.
  rewrite <- IHSTTerm2.
  reflexivity.
  rewrite <- IHSTTerm1.
  rewrite <- IHSTTerm2.
  reflexivity.
  rewrite <- IHSTTerm.
  reflexivity.
  rewrite <- IHSTTerm.
  reflexivity.
Defined.

Hint Resolve open_rec_term.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, STTerm u -> 
  [x ~> u] (open t1 t2) = open ([x ~> u]t1) ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl.
  (* STFVar *)
  - case_eq (eqb a x); intros.
    rewrite <-  open_rec_term; auto.
    simpl; reflexivity.
  (* STFVar *)
  - case_eq (n0 =? n); intros; auto.
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
  (* STProj2 *)
  - rewrite IHt1; reflexivity.
Defined.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall (x y : var) u t, not (x == y) -> STTerm u ->
  ([x ~> u] t) ^ y = [x ~> u] (t ^ y).
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
  not (In x (fv t)) -> STTerm u ->
  open t u = [x ~> u](t ^ x).
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
  exists L, forall x, not (In x L) -> STTerm (t ^ x).

(** We then show how to introduce and eliminate [body t]. *)

Lemma term_abs_to_body : forall A t1, 
  STTerm (STLam _ A t1) -> body t1.
Proof.
  intros; unfold body; inversion H; subst; exists L; assumption.
Defined.

Lemma body_to_term_abs : forall A t1, 
  body t1 -> STTerm (STLam _ A t1).
Proof. intros. inversion H. apply_fresh STTerm_Lam as x. apply H0.
       unfold not in *. intros; apply Fry; apply union_spec; auto.
Defined.

(* Hint Resolve term_abs_to_body body_to_term_abs. *)

(** We prove that terms are stable by substitution *)

Lemma subst_term : forall t z u,
  STTerm u -> STTerm t -> STTerm ([z ~> u]t).
Proof.
  induction 2; simpl; auto.
  destruct (eqb x z).
  assumption.
  (* Var *)
  - apply STTerm_Var.
  (* Lam *)
  - apply_fresh STTerm_Lam as x.
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

(** We prove that opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> STTerm u -> STTerm (open t u).
Proof.
  intros t u H1 H2. destruct H1. pick_fresh y.
  rewrite union_spec in Fr.
  rewrite union_spec in Fr.
  assert (Ha : not (In y x)).
  unfold not; intros; apply Fr; left; left; assumption.
  rewrite (@subst_intro y); auto.
Defined.

Hint Resolve open_term.*)
Hint Resolve singleton_spec.
Hint Resolve union_spec.

Hint Unfold open.
Hint Unfold not.
Hint Unfold open_rec.

Hint Rewrite <- open_rec_term.

Lemma coercions_produce_terms :
  forall E A B, sub A B E -> STTerm E.
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - apply_fresh STTerm_Lam as x. cbn; auto.
  (* Case SFun *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_Lam as y; cbn.
    apply STTerm_App.
    repeat rewrite <- open_rec_term; assumption.
    apply STTerm_App.
    apply STTerm_Var.
    apply STTerm_App; [ repeat rewrite <- open_rec_term; auto | apply STTerm_Var ].
  (* Case SAnd1 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    rewrite <- open_rec_term; auto.
  (* Case SAnd2 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  (* Case SAnd3 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
Defined.

Hint Resolve coercions_produce_terms.

(*
Require Import Coq.Program.Equality.

Module MEnv := MSetWeakList.Make(SourceTyp).
Export MEnv.

Require Import MSetProperties.
Module MSetProperties := WPropertiesOn(VarTyp)(M).

Require Import Coq.MSets.MSetFacts.

Lemma dom_union : forall (A : Type) (E G : context A) x,
  M.In x (dom (E ++ G)) <-> M.In x (M.union (dom E) (dom G)).
Proof.
  intros. generalize dependent G.
  induction E; intros.
  unfold dom at 2; simpl.
  unfold "<->".
  split; intros.
  apply MSetProperties.Dec.F.union_3.
  assumption.
  apply MSetProperties.Dec.F.union_1 in H.
  inversion H.
  inversion H0.
  assumption.
  simpl.
  destruct a.
  split; intros.
  simpl in *.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.union_2.
  apply MSetProperties.Dec.F.add_iff.
  auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  assert (Ha : M.Equal (M.union (M.add v (dom E)) (dom G)) (M.add v (M.union (dom E) (dom G)))) by apply MSetProperties.union_add.
  apply Ha.
  apply IHE in H.
  unfold not in n.
  apply MSetProperties.Dec.F.add_2.
  assumption.
  simpl in *.
  apply MSetProperties.Dec.F.union_1 in H.
  destruct H.
  assert (Ha : sumbool (VarTyp.eq v x) (not( VarTyp.eq v x))) by apply VarTyp.eq_dec.
  destruct Ha.
  apply MSetProperties.Dec.F.add_iff; auto.
  rewrite (MSetProperties.Dec.F.add_neq_iff _ n) in H.
  apply MSetProperties.Dec.F.add_neq_iff; auto.
  apply IHE.
  apply MSetProperties.Dec.F.union_2; assumption.
  apply MSetProperties.Dec.F.add_iff.
  right.
  apply IHE.
  apply MSetProperties.Dec.F.union_3; assumption.
Defined.

Import Coq.Init.Logic.
Print Coq.Init.Logic.

Ltac not_in_L := 
  match goal with
    | H: not (M.In ?x ?l1) |- not (M.In ?x ?l2) =>
      unfold not; intros; apply H; repeat rewrite M.union_spec; auto 10
  end. 

Lemma typing_weaken : forall G E F t T,
   has_type_st (E ++ G) t T -> 
   ok (E ++ F ++ G) ->
   has_type_st (E ++ F ++ G) t T.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent G.
  dependent induction H; intros; eauto.
  (* STTyVar *)
  - subst.
    apply STTyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
  (* STTyLam *)
  - apply_fresh STTyLam as x.
    unfold open in *; simpl in *.
    do 2 rewrite <- app_assoc.
    apply H0.
    not_in_L.
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
Defined.
 *)
Require Import Coq.Logic.Classical_Prop.

Lemma not_in_app_l :
  forall A (a : A) l1 l2, not (List.In a (l1 ++ l2)) -> not (List.In a l1).
Proof.
  intros A a l1 l2 H.
  unfold not; intros; apply H.
  apply in_or_app.
  auto.
Defined.  

Lemma not_in_app_r :
  forall A (a : A) l1 l2, not (List.In a (l1 ++ l2)) -> not (List.In a l2).
Proof.
  intros A a l1 l2 H.
  unfold not; intros; apply H.
  apply in_or_app.
  auto. 
Defined.   

(*
Ltac not_in_L2 x :=
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


Lemma ok_push_l : forall A (Gamma : context A) x v,
  not (M.In x (dom Gamma)) -> ok Gamma -> ok ((x,v) :: Gamma).
Proof.
  Hint Rewrite <- app_nil_l.
  intros.
  generalize dependent H.
  generalize dependent x.
  generalize dependent v.
  dependent induction H0.
  intros.
  rewrite <- app_nil_l; auto.
  intros.
  rewrite app_comm_cons.
  apply Ok_push.
  apply IHok.
  not_in_L2 x.
  not_in_L2 x.
Defined.
 *)

Lemma app_inv_singleton :
  forall {A} l1 l2 (p1 : A) p2, l1 ++ p1 :: nil = l2 ++ p2 :: nil -> l1 = l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1.
  simpl in *.
  intros.
  rewrite <- app_nil_l in H at 1.
  induction l2.
  reflexivity.
  inversion H.
  exfalso.
  eapply app_cons_not_nil.
  apply H2.
  intros.
  generalize dependent l1.
  induction l2.
  intros.
  simpl in H.
  inversion H; subst.
  exfalso.
  eapply app_cons_not_nil.
  symmetry.
  apply H2.
  intros.
  inversion H.
  subst.
  apply f_equal.
  apply IHl1.
  assumption.
Defined.
  
Lemma type_correct_envs : forall x Gamma E ty, has_type_source Gamma x ty E -> ok Gamma.
Proof.
  intros; induction H; auto.
  pick_fresh x.
  assert (Ha : not (M.In x L)).
  unfold not; intro; apply Fr; rewrite M.union_spec; auto.
  not_in_L x.
  apply H0 in Ha.
  now inversion Ha.
Defined.

(*  
Lemma typing_weaken_extend' : forall t T x v Gamma,
   has_type_st Gamma t T ->
   not (M.In x (dom Gamma)) ->                            
   has_type_st ((x,v) :: Gamma) t T.
Proof.
  intros.
  induction H; eauto.
  apply STTyVar.
  apply Ok_push; assumption.
  apply in_cons; assumption.
  apply STTyLit.
  apply Ok_push; assumption.
  apply_fresh STTyLam as x; cbn.
  apply H1.
  not_in_L2 y.
  not_in_L2 x.
  not_in_L2 y.
Defined.
*)  

(* Subtyping rules produce type-correct coercions: Lemma 3 *)
Lemma type_correct_coercions' :
  forall A B E, sub A B E ->
           has_type_st nil E (STFun (|A|) (|B|)) .
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - simpl; apply_fresh STTyLam as x; cbn.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  (* Case SFun *)
  - apply_fresh STTyLam as x; cbn.
    apply_fresh STTyLam as y; cbn.
    apply STTyApp with (A := (| o2 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend; try assumption.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    not_in_L y.
    eauto.
    rewrite <- open_rec_term; eauto.
    eapply STTyApp.
    apply STTyVar.
    apply Ok_push.
    apply Ok_push.
    apply Ok_nil.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    right; left; reflexivity.
    apply STTyApp with (A := (| o3 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend; try assumption.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    eauto.
    rewrite <- open_rec_term; eauto.
    apply STTyVar.
    apply Ok_push.
    not_in_L x.
    not_in_L y.
    rewrite <- app_nil_l.
    apply Ok_push.
    apply Ok_nil.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    left; reflexivity.
  (* Case SAnd1 *)
  - apply_fresh STTyLam as x; cbn.
    apply STTyPair.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub1.
    not_in_L x.
    eauto.
    apply STTyVar.
    rewrite <- app_nil_l; apply Ok_push; [ apply Ok_nil | not_in_L x ].
    apply in_eq.
    rewrite <- open_rec_term.
    eapply STTyApp.
    apply typing_weaken_extend.
    apply IHsub2.
    not_in_L x.
    apply STTyVar.
    rewrite <- app_nil_l; apply Ok_push; [ apply Ok_nil | not_in_L x ].
    apply in_eq.
    eauto.
  (* Case SAnd2 *)
  - apply_fresh STTyLam as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    not_in_L x.
    eauto.
    eapply STTyProj1.
    apply STTyVar.
    rewrite <- app_nil_l; apply Ok_push; [ apply Ok_nil | not_in_L x ]. 
    apply in_eq.
  (* SAnd3 *)
  - apply_fresh STTyLam as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    not_in_L x.
    eauto.
    eapply STTyProj2.
    apply STTyVar.
    rewrite <- app_nil_l; apply Ok_push; [ apply Ok_nil | not_in_L x ]. 
    apply in_eq.
Defined.

(* Subtyping rules produce type-correct coercions: Lemma 3 *)
Lemma type_correct_coercions :
  forall Gamma A B E, sub A B E ->
             ok Gamma -> 
             has_type_st Gamma E (STFun (|A|) (|B|)) .
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - simpl.
    apply_fresh STTyLam as x; cbn.
    simpl; apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  (* Case SFun *)
  - apply_fresh STTyLam as x; cbn.
    apply_fresh STTyLam as y; cbn.
    apply STTyApp with (A := (| o2 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend.
    assumption.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    eapply coercions_produce_terms; apply H1.
    rewrite <- open_rec_term; eapply coercions_produce_terms; apply H1.
    eapply STTyApp.
    apply STTyVar.
    apply Ok_push.
    apply Ok_push.
    assumption.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    right; left; reflexivity.
    apply STTyApp with (A := (| o3 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend.
    apply IHsub1.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    eauto.
    rewrite <- open_rec_term; eauto.
    apply STTyVar.
    apply Ok_push.
    apply Ok_push.
    assumption.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    left; reflexivity.
  (* Case SAnd1 *)
  - apply_fresh STTyLam as x; cbn.
    apply STTyPair.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    eauto.
    not_in_L x.
    eauto.
    apply STTyVar.
    apply Ok_push.
    assumption.
    not_in_L x.
    left; reflexivity.
    eapply STTyApp.
    apply typing_weaken_extend.
    rewrite <- open_rec_term.
    eauto.
    eauto.
    not_in_L x.
    apply STTyVar.
    apply Ok_push.
    assumption.
    not_in_L x.
    left; reflexivity.
  (* Case SAnd2 *)
  - apply_fresh STTyLam as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    eauto.
    not_in_L x.
    eauto.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push.
    assumption.
    not_in_L x.
    left; reflexivity.
  (* SAnd3 *)
  - apply_fresh STTyLam as x.
    unfold open; simpl.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    eauto.
    not_in_L x.
    eauto.
    eapply STTyProj2.
    apply STTyVar.
    apply Ok_push.
    assumption.
    not_in_L x.
    left; reflexivity.
Defined.

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
  
(* Type preservation: Theorem 1 *)
Lemma type_preservation : forall x ty E (Gamma : context PTyp) (H : has_type_source Gamma x ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof.
  intros.
  induction H; subst.
  (* TyVar *)
  apply STTyVar.
  apply (ok_map Gamma H).
  now apply in_persists.
  (* TyLit *)
  apply STTyLit.
  apply (ok_map Gamma H).
  (* TyLam *)
  simpl.
  apply_fresh STTyLam as x.
  unfold open; simpl.
  assert (Ha : not (M.In x L)) by (not_in_L x).
  apply H0 in Ha.
  unfold conv_context in Ha.
  simpl in Ha; unfold mapctx in Ha.
  unfold extend; simpl.
  rewrite <- open_rec_term.
  assumption.
  apply typing_gives_terms in Ha.
  assumption.  
  (* TyApp *)
  simpl in *.
  apply STTyApp with (A := |A|).
  assumption.
  apply type_correct_coercions with (Gamma := (∥ Gamma ∥)) in H1.
  apply STTyApp with (A := |C|); assumption.
  apply type_correct_envs in H0.
  apply (ok_map Gamma H0).
  (* TyPair *)
  simpl.
  apply STTyPair; assumption.
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
Defined. 
  
Theorem unique_type :
  forall t Gamma A1 A2 E1 E2, has_type_source Gamma t A1 E1 ->
                     has_type_source Gamma t A2 E2 ->
                     A1 = A2.
Proof.  
  intros t Gamma A1 A2 E1 E2 H1 H2.
  generalize dependent A2.
  generalize dependent E2.
  induction H1; intros. Print has_type_source.
  (* TyVar *)
  - inversion H2. subst.
    assert (HIn : List.In (x, ty) Gamma /\ List.In (x, A2) Gamma) by (split; assumption).
    clear H0; clear H5.
    induction H4; intros.
    inversion HIn; inversion H0.
    apply ok_unique_type in HIn; auto.
  (* TyLit *)  
  - inversion H2; reflexivity.
  (* TyFun *)
  - inversion H2; subst.
    apply f_equal.
    pick_fresh x.
    eapply H0 with (x := x).
    not_in_L x.
    apply H6.
    not_in_L x.
  (* TyApp *)
  - inversion H2; subst.
    apply IHhas_type_source1 in H3.
    apply IHhas_type_source2 in H5.
    inversion H3.
    reflexivity.
  (* TyMerge *)
  - inversion H2; subst.
    apply IHhas_type_source1 in H3.
    apply IHhas_type_source2 in H5.
    subst; reflexivity.
Defined.


Lemma typing_wf : forall Gamma t T E, has_type_source Gamma t T E -> WFTyp T.
Proof.
  intros Gamma t T E H.
  induction H.
  assumption.
  apply WFInt.
  pick_fresh x.
  assert (Ha : not (M.In x L)) by (not_in_L x).
  apply WFFun.
  apply H in Ha.
  assumption.
  apply H0 with (x := x); assumption.
  inversion IHhas_type_source1; assumption.
  apply WFAnd; try assumption.
Defined.
  
(* Theorem 5 *)
Theorem type_coherence :
  forall t Gamma A1 A2 E1 E2, has_type_source Gamma t A1 E1 ->
                     has_type_source Gamma t A2 E2 ->
                     E1 = E2.
Proof.  
  intros; generalize dependent E2; generalize dependent A2; induction H; intros.
  (* STFVar *)
  - inversion H2; reflexivity.
  (* STInt *)
  - inversion H0; reflexivity.
  (* STLam *)
  - inversion H2; subst.    
    pick_fresh x.
    assert (Ha1: not (M.In x L0)) by (not_in_L x).
    erewrite H0.
    reflexivity.
    assert (Ha4: not (M.In x L)) by (not_in_L x).
    exact Ha4.
    apply H6 in Ha1.
    apply Ha1.
  (* STApp *)
  - inversion H2; subst.
    assert (Ha : Fun A0 A2 = Fun A B).
    apply (unique_type _ _ _ _ _ _ H5 H).
    inversion Ha.
    subst.
    apply IHhas_type_source1 in H5.
    subst.
    apply f_equal.
    assert (Ha2: C0 = C) by (apply (unique_type _ _ _ _ _ _ H7 H0)).
    subst.
    apply IHhas_type_source2 in H7.
    subst.
    apply typing_wf in H.
    erewrite sub_coherent with (C1 := E) (C2 := E3) (A := C) (B := A).
    reflexivity.
    apply typing_wf in H0; assumption.
    inversion H; assumption.
    assumption.
    assumption.
  (* STPair *)
  - inversion H2; subst.
    apply IHhas_type_source1 in H5.
    apply IHhas_type_source2 in H7.
    subst; reflexivity.
Defined.
