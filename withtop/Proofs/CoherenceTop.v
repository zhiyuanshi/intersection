Require Import String.
Require Import STLC.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.

Module CoherenceTop
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


(* Types *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp
  | TopT : PTyp.

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | TopT => STUnitT
  end.


Inductive TopLike : PTyp -> Prop :=
| TLTop : TopLike TopT
| TLAnd : forall A B, TopLike A -> TopLike B -> TopLike (And A B)
| TLFun : forall A B, TopLike B -> TopLike (Fun A B).

(* Unrestricted Subtyping *)

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4) 
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2) 
  | USAnd2 : forall t t1 t2 , usub t1 t -> usub (And t1 t2) t 
  | USAnd3 : forall t t1 t2, usub t2 t -> usub (And t1 t2) t 
  | USTop : forall t, usub t TopT.

(* TODO: Show transitivity of usub here, and easily derive transitivity 
for sub *)

(* Restricted Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

Fixpoint genCoerce (n : nat) : Exp :=
  match n with
    | 0 => fun A => STLam' _ (STUnit _)
    | S m => fun A => STLam' _ (genCoerce m A)
  end.

Fixpoint and_coercion (t : PTyp) (e1 : Exp) (n : nat) : Exp :=
  match t with
    | PInt => e1
    | TopT => genCoerce n
    | Fun A B => and_coercion B e1 (S n)
    | And A B => e1
  end.
  
Inductive sub : PTyp -> PTyp -> Exp -> Prop :=
  | SInt : sub PInt PInt (fun A => STLam' _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun  o3 o4) (fun A => STLam' _ ( 
       STLam' _ (STApp _ (c2 A) (STApp _ (STBVar _ 1) (STApp _ (c1 A) (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (fun A => STLam' _ (
       STPair _ (STApp _ (c1 A) (STBVar _ 0)) (STApp _ (c2 A) (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (and_coercion t (fun A => STLam' _ (
       (STApp _ (c A) (STProj1 _ (STBVar _ 0))))) 0)
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (and_coercion t (fun A => STLam' _ (
       (STApp _ (c A) (STProj2 _ (STBVar _ 0))))) 0)
  | STop : forall t, sub t TopT (fun A => STLam' _ (STUnit _)).

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:Exp), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (fun A => STLam' _ (STBVar _ 0)). 
exact SInt.
Defined.

Definition stop : forall t, Sub t TopT.
intros; unfold Sub.
exists (fun A => STLam' _ (STUnit _)).
apply STop.
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
unfold Sub. intro t. intros. destruct t. destruct H.
exists (and_coercion PInt (fun A => STLam' _ (
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))) 0).
apply SAnd2. auto. auto. destruct H.
exists (and_coercion (Fun t3 t4) (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj1 _ (STBVar _ 0))))) 0).
apply SAnd2. auto. auto.
inversion H0.
apply stop. (* a top case here *)
Defined.

(* The No loss of Expressivity Lemmas *)

(* Theorem 3 *)

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
intro t; induction t; intros.
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
exists (fun A => STLam' _ (
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
(* Case Top *)
apply stop. (* a top case here *)
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intro t; intros. destruct t. destruct H.
exists (and_coercion PInt (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))) 0).
apply SAnd3. auto. auto. destruct H.
exists (and_coercion (Fun t3 t4) (fun A => STLam' _ ( 
       (STApp _ (x A) (STProj2 _ (STBVar _ 0))))) 0).
apply SAnd3. auto. auto.
inversion H0.
apply stop. (* a top case here *)
Defined.

(* Theorem 4 *)

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And  t1 t2) t.
intro t; induction t; intros.
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
exists (fun A => STLam' _ ( 
       STPair _ (STApp _ (x0 A) (STBVar _ 0)) (STApp _ (x1 A) (STBVar _ 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
(* Case Top *)
apply stop. (* top case *)
Defined.

(* Hints Reflexivity *)
Hint Resolve sint sfun sand1 sand2 sand3 SInt SFun SAnd1 SAnd2 SAnd3 stop USInt USFun USAnd1 USAnd2 USAnd3 USTop.

(* Restricted subtyping is sound and complete with respect to the unrestricted 
subtyping relation *)

Lemma sound_sub : forall t1 t2, usub t1 t2 -> Sub t1 t2.
intros.  
induction H; try auto.
Defined.

Lemma complete_sub : forall t1 t2, Sub t1 t2 -> usub t1 t2.
intros. destruct H. induction H; try auto.
Defined.  

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := 
  (not (TopLike A) /\ not (TopLike B)) /\ (forall C, Sub A C -> Sub B C -> TopLike C).

Lemma applyOrthoS : forall {A B}, OrthoS A B -> forall C, Sub A C -> Sub B C -> TopLike C.
intros. destruct H. apply H2; auto.
Defined.

(* Disjointness: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OIntFun : forall t1 t2, not (TopLike t2) -> Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, not (TopLike t2) -> Ortho (Fun t1 t2) PInt
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2)
  | WFTop : WFTyp TopT.

Lemma reflex : forall (t1 : PTyp), Sub t1 t1.
Proof.
induction t1; intros; auto.
Defined.

Lemma OrthoSNotEq : forall A B, OrthoS A B -> not (A = B). 
intros. destruct H. destruct H. unfold not; intros. rewrite <- H2 in H0.
assert (TopLike A). apply H0. apply reflex. apply reflex.
contradiction.
Defined.

(* Lemmas needed to prove soundness of the disjointness algorithm *)

Lemma ortho_sym : forall {A B}, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS. 
intros. destruct H. split. destruct H. split. auto. auto.
intros.
apply H0.
auto. auto.
Defined.

Lemma invAndS1 : forall t t1 t2, Sub t (And t1 t2) -> Sub t t1 /\ Sub t t2.
Proof.
intro t; induction t; intros.
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
(* Top cases *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
Defined.

Lemma ortho_and : forall {A B C}, OrthoS A C -> OrthoS B C -> OrthoS (And A B) C.
Proof.
intros. unfold OrthoS. split. 
destruct H. destruct H0. destruct H. destruct H0. split.
unfold not; intros. inversion H5. 
(*apply H. auto. apply H0. auto.*) auto. auto.
intros. destruct H. destruct H0.
induction C0. 
inversion H1. inversion H5. apply H3. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
apply H4.  
unfold Sub. exists c. auto. auto.
inversion H1. inversion H5.
apply H3. unfold Sub. exists c. auto. auto.
apply H4. unfold Sub. exists c. auto. auto.
assert (Sub C C0_1 /\ Sub C C0_2). apply invAndS1. auto. destruct H5.
assert (Sub (And A B) C0_1 /\ Sub (And A B) C0_2). apply invAndS1. auto.
destruct H7. pose (IHC0_1 H7 H5). pose (IHC0_2 H8 H6).
apply TLAnd. auto. auto.
apply TLTop.
Defined.

(*
Lemma ortho_and2 : forall {A B C}, OrthoS (And A B) C -> OrthoS A C /\ OrthoS B C.
intros. destruct H.
split.
unfold OrthoS. split.
destruct H.
left.
unfold not. intros.
apply H.
apply H0. apply reflex.
*)  

(* Disjointness algorithm is complete: Theorem 7 *)

Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
Proof.
intros t1 wft1.
induction wft1; intros.
(* Case PInt *)
generalize H0. clear H0. induction H; intros.
destruct H0.
pose (H0 PInt sint sint). inversion t0.
apply OIntFun.
destruct H1. destruct H1. unfold not. intros. apply H3. apply TLFun. auto.
apply OAnd2. 
apply IHWFTyp1. unfold OrthoS. split.
destruct H2. destruct H2. destruct H1. destruct H1.
split; auto.
intros. apply H2.
auto. apply sand2.
auto. apply IHWFTyp2.
unfold OrthoS. destruct H1. destruct H2. destruct H1. destruct H2.
split; auto. destruct H0. destruct H. destruct H1. apply TLTop.
(* Case Fun t1 t2 *)
induction H.
apply OFunInt. destruct H0.
destruct H. unfold not. intros. apply H. apply TLFun. auto.
apply OFun. apply IHwft1_2. auto.
unfold OrthoS. split. destruct H0.
destruct H0. split. unfold not; intros.
apply H0. apply TLFun. auto.
unfold not; intros. apply H3.
apply TLFun. auto.
intros. destruct H0. destruct H0.
assert (TopLike (Fun (And t1 t0) C)).
apply H4. apply sfun. apply sand2. apply reflex.
auto. apply sfun. apply sand3. apply reflex. auto.
inversion H6. auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHWFTyp1.
destruct H2. destruct H2.
destruct H0. destruct H0.
unfold OrthoS. split.
split. auto. auto.
intros.
apply H5. auto.
apply sand2. auto.
apply IHWFTyp2.
destruct H2. destruct H2.
destruct H0. destruct H0.
unfold OrthoS. split.
split. auto. auto.
intros.
apply H5. auto.
apply sand3. auto.
destruct H0. destruct H.
(* Case t11 -> t12 _|_ T *)
destruct H1. apply TLTop.
(* Case (t11 & t12) _|_ t2 *)
destruct H. destruct H. destruct H1. destruct H1.
apply OAnd1.
apply IHwft1_1. auto.
unfold OrthoS. split. split; auto.
intros.
apply H4.
apply sand2; auto. auto.
apply IHwft1_2. auto.
unfold OrthoS. split. split; auto.
unfold OrthoS; intros. apply H4.
apply sand3. auto. auto.
(* Case T _|_ t2 *)
destruct H0. destruct H0. destruct H0. apply TLTop.
Defined.

(*
Lemma nosub : forall t1 t2, OrthoS t1 t2 -> not (Sub t1 t2) /\ not (Sub t2 t1).
Proof.
intros; split; unfold not.
unfold OrthoS in H. intros.
apply H.
exists t2.
split. auto. apply reflex.
unfold OrthoS in H. unfold not in H. intros.
apply H.
exists t1. split. apply reflex. auto.
Defined.
*)


(* Unique subtype contributor: Lemma 4 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> Sub (And A B) C -> not (TopLike C) ->  not (Sub A C /\ Sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. destruct H2.
destruct H. 
pose (H4 C H2 H3). contradiction. 
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
(* Case IntFun *)
unfold OrthoS. split. split. unfold not; intros. inversion H0.
unfold not. intros. apply H. inversion H0. auto.
induction C; intros. inversion H1. inversion H2. inversion H0. inversion H2.
inversion H0. inversion H2. inversion H1. inversion H9.
apply TLAnd. apply IHC1. unfold Sub. exists c1. auto.
unfold Sub. exists c0. auto.
apply IHC2.
unfold Sub. exists c2. auto. unfold Sub. exists c3. auto.
(* TopT *)
apply TLTop.
(* Case IntFun *)
unfold OrthoS. split.
split.
unfold not; intros.
apply H. inversion H0. auto.
unfold not. intros. inversion H0.
induction C; intros. inversion H0. inversion H2. inversion H1. inversion H2.
apply TLAnd.
apply IHC1.
inversion H0. inversion H2. unfold Sub. exists c1. auto.
inversion H1. inversion H2. unfold Sub. exists c1. auto.
apply IHC2.
inversion H0. inversion H2. unfold Sub. exists c2. auto.
inversion H1. inversion H2. unfold Sub. exists c2. auto.
(* TopT *)
apply TLTop.
(* FunFun *)
destruct IHOrtho. destruct H0. 
unfold OrthoS. split. split. unfold not. intros.
apply H0. inversion H3. auto.
unfold not; intros. apply H2. inversion H3. auto.
intros.
induction C. inversion H3. inversion H5.
apply TLFun. apply H1. inversion H3. inversion H5.
unfold Sub. exists c2. auto.
inversion H4. inversion H5. unfold Sub. exists c2. auto.
apply TLAnd. apply IHC1. inversion H3. inversion H5.
unfold Sub. exists c1. auto.
inversion H4. inversion H5.
unfold Sub. exists c1. auto.
apply IHC2. inversion H3. inversion H5.
unfold Sub. exists c2. auto.
inversion H4. inversion H5.
unfold Sub. exists c2. auto. 
apply TLTop.
Defined.

Lemma same_coercion : forall B, TopLike B -> WFTyp B -> forall A e1 e2 n, and_coercion (Fun A B) e1 n = and_coercion (Fun A B) e2 n.
intro. intro.
induction H; intros.
(* Case TopT *)
simpl. reflexivity.
(* Case And *)
simpl in IHTopLike1.
simpl in IHTopLike2.
simpl. inversion H1. destruct H6. destruct H6. contradiction.
(* Case Fun *)
simpl in IHTopLike.
simpl. inversion H0.
apply IHTopLike. auto. apply A0.
Defined.

(* Coercive subtyping is coeherent: Lemma 5 *)

Lemma sub_coherent : forall A, WFTyp A -> forall B, WFTyp B -> forall C1, sub A B C1 -> forall C2, sub A B C2 -> C1 = C2.
Proof.
intro. intro. intro. intro. intro. intro.
induction H1; intros.
(* Case: Int <: Int *)
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
destruct H14. 
assert (TopLike t0). apply H15. unfold Sub.
exists c; auto. unfold Sub. exists c0. auto.
inversion H16. rewrite <- H17 in H2. inversion H2.
rewrite <- H19 in H2. inversion H2.
apply same_coercion. auto. rewrite <- H18 in H0. inversion H0. auto.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* Case: And t1 t2 <: t (second) *)
inversion H3; inversion H.
rewrite <- H7 in H2. inversion H2.
(* contradiction: not orthogonal! *)
destruct H14.
inversion H14.
assert (TopLike t0). apply H15.
unfold Sub. exists c0. auto.
unfold Sub. exists c. auto.
inversion H18. rewrite <- H19 in H2. inversion H2.
rewrite <- H21 in H2. inversion H2.
apply same_coercion. auto. rewrite <- H20 in H0. inversion H0. auto.
(* same coercion; no contradiction *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* last top case *)
inversion H1. inversion H3. inversion H3.
reflexivity.
Defined.


(* Remaining Issues:

(\(x : T) . x) (True,,3) 

e1 : T -> T ~> (\x:().x)    e2 : Bool & Int ~> (True,3)   Bool & Int <: T ~> (\x . ())
--------------------------------------------------------------
e1 e2 : T ~> (\x:().x) ((\x.()) (True,3))

Int & Int -> Char <: Int -> T ~> \x. \y . ()

Basically when we have:

A1 & A2 <: A3

if A3 is FTop, then the generated coercion should always be of the form:

\x . \y . ()

TopLike, includes functions that return T.

Int -> T & Int -> Char 

Int -> T <: C and Int -> Char <: C -> FTop C

but the types intersect, clearly 

C = Int -> T

A * B = not (TopLike A

not (A <: B) /\ not (B <: A) /\
forall C, A <: C and B <: C -> 

forbid TopLike Types in intersections!

allow Int -> String & Int -> Char, even though the types intersect

 *)

(* Looking for some alternative specifications *)

Lemma rest : forall A B, not (Sub A B) /\ not (Sub B A) -> not (TopLike A).
intros.
destruct H. 
unfold not. intros. generalize H H0 B. clear H H0. generalize B. clear B.
induction H1; intros. apply H0. apply stop.
assert (not (Sub B0 A) /\ not (Sub B0 B)).
split. unfold not. intros.
Admitted.


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
  | PAnn   : PExp -> PTyp -> PExp (* only for the algorithmic version *)
  | PTop   : PExp.

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
    | PTop => empty
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
  | PAnn e t     => PAnn (open_rec_source k u e) t
  | PTop         => PTop
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
  | TySub : forall Gamma t t' A B,
              has_type_source Gamma t A t' ->
              Sub A B ->
              WFTyp B ->
              has_type_source Gamma t B (PAnn t' B)
  | TyTop : forall Gamma, ok Gamma -> has_type_source Gamma PTop TopT PTop.

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
      PTerm (PAnn e t)
  | PTerm_Top : PTerm PTop.  

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
  reflexivity.
Defined.

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

(*
Fixpoint subst_source (z : var) (u : PExp) (t : PExp) {struct t} : PExp :=
  match t with
    | PBVar i     => PBVar i
    | PFVar x     => if VarTyp.eqb x z then u else (PFVar x)
    | PLit i      => PLit i
    | PLam t1     => PLam (subst_source z u t1)
    | PApp t1 t2  => PApp (subst_source z u t1) (subst_source z u t2)
    | PMerge t1 t2 => PMerge (subst_source z u t1) (subst_source z u t2)
    | PAnn t1 t2  => PAnn (subst_source z u t1) t2 
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
  (* Case PAnn *)
  simpl in *; rewrite IHt; auto.
Defined.

(** Substitution distributes on the open operation. *)

Lemma subst_source_open : forall x u t1 t2, PTerm u -> 
  subst_source x u (open_source t1 t2) = open_source (subst_source x u t1) (subst_source x u t2).
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

Lemma subst_source_open_var : forall (x y : var) u t, not (x == y) -> PTerm u ->
  open_source (subst_source x u t) (PFVar y) = subst_source x u (open_source t (PFVar y)).
Proof.
  intros. rewrite subst_source_open. simpl.
  case_eq (eqb y x); intros.
  apply eqb_eq in H1.
  exfalso; apply H; symmetry. assumption.
  reflexivity.
  assumption.
Defined.
  
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
Defined.

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
Defined.

Lemma body_source_to_term_abs : forall t1, 
  body_source t1 -> PTerm (PLam t1).
Proof. intros. inversion H. apply_fresh PTerm_Lam as x. apply H0.
       unfold not in *. intros; apply Fry; apply union_spec; auto.
Defined.

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
Defined.

Hint Resolve subst_source_term.
 *)

Lemma type_correct_source_terms : forall Gamma E ty e, has_type_source Gamma E ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Defined.

Lemma type_correct_source_terms' : forall Gamma E ty e, has_type_source Gamma E ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Defined.

Lemma typing_wf_source :
  forall Gamma t T E, has_type_source Gamma t T E -> WFTyp T.
Proof.
  intros Gamma t  T E H.
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
  assumption.
  apply WFTop.
Defined.

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
    eapply TySub.
    apply IHhas_type_source.
    assumption.
    reflexivity.
    apply H1.
    assumption.
  - apply TyTop.
    subst.
    now apply ok_remove in H0.
Defined.    

Lemma typing_source_ok_env : forall Gamma E ty e, has_type_source Gamma E ty e -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Defined.
  
  
Definition has_type Gamma e t := exists s, has_type_source Gamma e t s.

Definition tvar :
  forall Gamma x ty, ok Gamma -> List.In (x,ty) Gamma -> WFTyp ty -> has_type Gamma (PFVar x) ty.
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
  assert (HNot : not (In y L)) by not_in_L y.
  pose (H y HNot).
  destruct e. exists (PAnn (PLam x) (Fun A B)).
  eapply TyLam with (L := union (union L (dom Gamma)) (fv_source t0)). intros.
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
  admit.
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

Definition tsub : forall Gamma t A B, has_type Gamma t A -> Sub A B -> WFTyp B -> has_type Gamma t B.
unfold has_type. intros. destruct H. exists (PAnn x B). apply (TySub _ _ _ A); auto.
Defined.

Definition ttop : forall Gamma, ok Gamma -> has_type Gamma PTop TopT.
intros. unfold has_type. exists PTop. apply TyTop. auto.
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
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E -> has_type_source_alg Gamma (PAnn t1 A) Inf A E
  (* Checking rules *)
  | ATyLam : forall L Gamma t A B E, (forall x, not (In x L) -> 
                                 has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) -> WFTyp A ->
                           has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam' _ E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp B ->
               has_type_source_alg Gamma t Chk B (STApp _ (C var) E)
  | ATyTop : forall Gamma, ok Gamma -> has_type_source_alg Gamma PTop Inf TopT (STUnit _).

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
  apply right; unfold not; intros HInv; inversion HInv.

  destruct B.
  apply right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv.
  apply right; unfold not; intros HInv; inversion HInv.
  apply left; reflexivity.
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

Lemma typing_wf_source_alg:
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp T.
Proof.
  intros Gamma t dir T E H.
  induction H.
  assumption.
  apply WFInt.
  inversion IHhas_type_source_alg1; assumption.
  apply WFAnd; try assumption.
  assumption.
  pick_fresh x.
  assert (Ha : not (M.In x L)) by (not_in_L x).
  apply WFFun.
  apply H in Ha.
  assumption.
  apply H0 with (x := x); assumption.
  assumption.
  apply WFTop.
Defined.
    
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
Defined.
    
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
  - subst.
    apply ok_remove in H0.
    now apply ATyTop.
Defined.    

Lemma type_correct_alg_terms : forall Gamma E ty e dir, has_type_source_alg Gamma E dir ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  apply_fresh PTerm_Lam as x; auto.
  apply H0; not_in_L x.
Defined.


Lemma typing_alg_ok_env : forall Gamma E dir ty e, has_type_source_alg Gamma E dir ty e -> ok Gamma.
Proof.
  intros.
  induction H; auto;
  pick_fresh x;
  assert (Ha: not (In x L)) by not_in_L x;
  pose (H0 _ Ha) as HInv;
  inversion HInv; auto.
Defined.


Definition body_typ t A B Gamma E :=
  exists L, forall x, not (In x L) -> has_type_source_alg (extend x A Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x)).

(** We then show how to introduce and eliminate [body t]. *)
Print has_type_source_alg.

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

Lemma foo : forall L Gamma A B t1,
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
       eexists (STLam' _ _). Check ATyLam.
       unfold has_ty in H1. Check foo.
       eapply (foo L Gamma A B t1) in H1. Check ATyLam.
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
  Check ATyLam.
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

Lemma tytop : forall Gamma : context PTyp, ok Gamma -> has_ty Gamma PTop Inf TopT.
intros. unfold has_ty. exists (STUnit _). apply ATyTop. auto.
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
    | PTop => PTop
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
(* Case Ann *)
- inversion H0. auto.
(* Case Lam *)
- auto.
(* case Sub *)
- auto.
(* case Top *)
- now inversion H0.
Defined.

(* type inference always gives unique types *)

Lemma typ_inf_unique : forall {Gamma e t1 E1}, has_type_source_alg Gamma e Inf t1 E1 -> forall {t2 E2}, has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros.
pose (@typ_unique _ _ _ _ _ H _ _ H0). simpl in a. auto.
Defined.

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
  eapply (sub_coherent _ H3 _ H6 _ H0 _ H4).  
  subst; reflexivity. 
(* ATyTop *)
- now inversion H0.
Defined.

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
Defined.

Print open_rec_source.

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
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2. 
  - reflexivity.
Defined.

Lemma and_coercion_proj1_term :
  forall t0 n (c : Exp),
    STTerm (c var) ->
    STTerm (and_coercion t0 (fun A : Type =>
                               STLam' A (STApp A (c A) (STProj1 A
                                                                (STBVar A 0)))) n
        var).
Proof.
  intros.
  generalize dependent n.
  induction t0; intros; simpl; try apply IHt0_2.
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  - induction n.
    simpl.
    apply_fresh STTerm_Lam' as x; auto.
    simpl.
    apply_fresh STTerm_Lam' as x; simpl in *.
    unfold open.
    rewrite <- open_rec_term; auto.
Qed.

Lemma and_coercion_proj2_term :
  forall t0 n (c : Exp),
    STTerm (c var) ->
    STTerm (and_coercion t0 (fun A : Type =>
                               STLam' A (STApp A (c A) (STProj2 A
                                                                (STBVar A 0)))) n
        var).
Proof.
  intros.
  generalize dependent n.
  induction t0; intros; simpl; try apply IHt0_2.
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  - induction n.
    simpl.
    apply_fresh STTerm_Lam' as x; auto.
    simpl.
    apply_fresh STTerm_Lam' as x; simpl in *.
    unfold open.
    rewrite <- open_rec_term; auto.
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
  - apply and_coercion_proj1_term; auto.
  (* Case SAnd3 *)
  - apply and_coercion_proj2_term; auto.
  (* Case STop *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_Unit.
Qed.

Hint Resolve coercions_produce_terms.

Inductive TopSig : PTyp -> Prop :=
  | TopSigF : forall A B, TopSig B -> TopSig (Fun A B)
  | TopSigT : TopSig TopT.                    

Print genCoerce.
Print and_coercion.

Fixpoint and_type (p : PTyp) (seed : PTyp) {struct p} : STyp :=
  match p with
  | PInt    => STUnitT
  | Fun A B => STFun (|seed|) (and_type B A)
  | And A B => STUnitT
  | TopT    => STFun (|seed|) STUnitT
  end.

Lemma and_type_has_type_st :
  forall t e r Gamma,
    TopSig t ->
    and_coercion t e 0 = r ->
    exists A, has_type_st Gamma (STLam' _ (r var)) (and_type t A).
Proof.
  intros.
  induction H.
  
Admitted.

Fixpoint genCoerce' (n : nat) : Exp :=
  match n with
    | 0 => fun A : Type => STUnit A
    | S m => fun A : Type => STLam' A (genCoerce' m A)
  end.

Fixpoint and_coercion' (t : PTyp) (e : Exp) (n : nat) {struct t} : Exp :=
  match t with
    | PInt    => e
    | Fun _ B => and_coercion' B e (S n)
    | And _ _ => e
    | TopT    => genCoerce' n
  end.

Print genCoerce.

Fixpoint and_coercion2 (t : PTyp) (e : Exp) {struct t} : sum Exp Exp :=
  match t with
    | PInt    => inr e
    | Fun _ B => match (and_coercion2 B e) with
                  | inl l => inl (fun A : Type => STLam' A (l A))
                  | inr r => inr r
                 end 
    | And _ _ => inr e
    | TopT    => inl (fun A : Type =>  STLam' A (STUnit A))
  end.

Lemma and_type_has_type_st' :
  forall t e,
    TopSig t ->
    exists r, and_coercion2 t e = inl r.  
Proof.
  intros.
  induction H.
  destruct IHTopSig.
  exists (fun A : Type => STLam' A (x A)).
  simpl.
  rewrite H0.
  reflexivity.
  exists (fun A : Type =>  STLam' A (STUnit A)).
  now simpl.
Qed.
  
(*
Inductive and_coercion_def : PTyp -> Exp -> Exp -> Prop :=
  | CPInt : forall e1, and_coercion_def PInt e1 e1
  | CTopT : forall e1, and_coercion_def TopT e1 (fun T => STLam' T (STUnit _))
  | CFun1 : forall A B e1 e2,
              TopSig B ->
              and_coercion_def B e1 e2 ->
              and_coercion_def (Fun A B) e1 (fun T => STLam' T (e2 T))
  | CFun2 : forall A B e1,
              not (TopSig B) ->
              and_coercion_def B e1 e1 ->
              and_coercion_def (Fun A B) e1 e1
  | CAnd : forall e1 A B, and_coercion_def (And A B) e1 e1.

Check and_coercion_def_ind.

Definition and_coercion_top_sig_ind :
  forall (P : PTyp -> Exp -> Exp -> Prop),
       (forall e1 : Exp, P TopT e1 (fun T : Type => STLam' T (STUnit T))) ->
       (forall (A B : PTyp) (e1 e2 : Exp),
        TopSig (Fun A B) ->
        and_coercion_def B e1 e2 ->
        P B e1 e2 -> P (Fun A B) e1 (fun T : Type => STLam' T (e2 T))) ->
    forall t e r, and_coercion_def t e r -> TopSig t -> P t e r.
  intros.
  induction H1.
  inversion H2.
  auto.
  apply H0; auto.
  inversion H2; contradiction.
  inversion H2.
Defined.  
*)

Lemma and_coercion_rewrite_topsig :
  forall t e r n,
    TopSig t ->
    and_coercion t e n var = r ->
    exists m, genCoerce m var = r.              
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  simpl in H0.
  now apply IHTopSig in H0.
  simpl in *.
  now exists n.
Qed.

(*
Inductive CountLam : PTyp -> nat -> Prop :=
  | ZLam : CountLam TopT 0 
  | SLam : forall t A n, CountLam t n ->
                    CountLam (Fun A t) (S n).

Lemma test :
  forall B n e r,
    TopSig B ->
    and_coercion B e (S n) var = STLam' var r ->
    and_coercion B e n var = r.
Proof.
Admitted.
  
Lemma and_coercion_rewrite_topsig' :
  forall t e (r : SExp var) n,
    TopSig t ->
    and_coercion t e n var = r ->
    exists m, genCoerce m var = r /\ CountLam t m.              
Proof.
  intros.
  generalize dependent n.
  generalize dependent r.
  generalize dependent e.
  dependent induction H; intros.
  induction r; try now (
  simpl in H0;
  apply IHTopSig in H0;
  inversion H0; inversion H1;
  unfold genCoerce in H2;
  destruct x; inversion H2).

  simpl in H0.
  apply test in H0.
  apply IHTopSig in H0.
  inversion H0.
  exists (S x).
  inversion H1.
  split.
  simpl.
  apply f_equal; auto.
  apply SLam; auto.
  auto.

  simpl in H0.
  
Admitted.
*)
Lemma and_coercion_rewrite_not_topsig : 
  forall t e r n,
    not (TopSig t) ->
    and_coercion t e n = r ->
    e = r.
Proof.
  intros.
  generalize dependent n.
  induction t0; intros.
  now simpl in H0.
  eapply IHt0_2.
  unfold not; intros; apply H.
  apply TopSigF.
  assumption.
  simpl in H0.
  apply H0.
  now simpl in H0.
  exfalso; apply H; apply TopSigT.
Qed.  

Lemma topsig_dec : forall t, sumbool (TopSig t) (not (TopSig t)).
Proof.
  intro t.
  induction t.
  - right; unfold not; intros HInv; inversion HInv. 
  - inversion IHt2.
    left.
    apply TopSigF.
    apply H.
    right.
    unfold not; intros HInv; inversion HInv; subst.
    contradiction.
  - right; unfold not; intros HInv; inversion HInv.
  - left; apply TopSigT.
Qed.    
    
Lemma and_coercion_rewrite' :
  forall t e (r : SExp var) n, and_coercion t e n var = r ->
                          (r = (e var) \/ exists m, r = genCoerce m var).
Proof.
  intros.
  generalize dependent n.
  induction t0; intros.
  simpl; auto.
  simpl in H.
  eapply IHt0_2.
  apply H.
  simpl; auto.
  unfold and_coercion in H.
  right; exists n; auto.
Qed.

Fixpoint and_coercion3 (t : PTyp) (e : Exp) {struct t} : sum Exp Exp :=
  match t with
    | PInt    => inr e
    | Fun _ B => match (and_coercion3 B e) with
                  | inl l => inl (fun A : Type => STLam' A (l A))
                  | inr r => inr r
                 end 
    | And _ _ => inr e
    | TopT    => inl (fun A => (STUnit A))
  end.

Definition join_sum : forall {A}, A + A -> A.
  intros A H; destruct H as [a | a]; exact a.
Defined.

Inductive sub' : PTyp -> PTyp -> Exp -> Prop :=
  | SSInt : sub' PInt PInt (fun A => STLam' _ (STBVar _ 0))
  | SSFun : forall o1 o2 o3 o4 c1 c2, sub' o3 o1 c1 -> sub' o2 o4 c2 -> 
     sub' (Fun o1 o2) (Fun  o3 o4) (fun A => STLam' _ ( 
       STLam' _ (STApp _ (c2 A) (STApp _ (STBVar _ 1) (STApp _ (c1 A) (STBVar _ 0))))))
  | SSAnd1 : forall t t1 t2 c1 c2, sub' t t1 c1 -> sub' t t2 c2 -> 
     sub' t (And  t1 t2) (fun A => STLam' _ (
       STPair _ (STApp _ (c1 A) (STBVar _ 0)) (STApp _ (c2 A) (STBVar _ 0))))
  | SSAnd2 : forall t t1 t2 c, sub' t1 t c -> Atomic t ->
     sub' (And  t1 t2) t (fun A => STLam' _ (join_sum (and_coercion3 t (fun A => (
       (STApp _ (c A) (STProj1 _ (STBVar _ 0)))))) A))
  | SSAnd3 : forall t t1 t2 c, sub' t2 t c -> Atomic t ->
     sub' (And  t1 t2) t (fun A => STLam' _ (join_sum (and_coercion3 t (fun A => (
       (STApp _ (c A) (STProj2 _ (STBVar _ 0)))))) A))
  | SSTop : forall t, sub' t TopT (fun A => STLam' _ (STUnit _)).

Lemma and_type_term3 :
  forall {t e},
    TopSig t ->
    exists r, and_coercion3 t e = inl r /\ STTerm (r var).  
Proof.
  intros.
  induction H.
  inversion IHTopSig.
  exists (fun A : Type => STLam' A (x A)).
  inversion H0.
  split.
  simpl.
  rewrite H1.
  reflexivity.
  apply_fresh STTerm_Lam' as x.
  unfold open; rewrite <- open_rec_term; auto.
  exists (fun A : Type => STUnit A); auto.
Qed.
  
Lemma and_type_has_type_st3 :
  forall {t e Gamma},
    ok Gamma ->
    TopSig t ->
    exists r, and_coercion3 t e = inl r /\ has_type_st Gamma (r var) (|t|).  
Proof.
  intros.
  induction H0.
  destruct IHTopSig.
  exists (fun A : Type => STLam' A (x A)).
  simpl.
  destruct H1.
  rewrite H1.
  split.
  reflexivity.
  apply_fresh STTyLam' as v.
  unfold open.
  rewrite <- open_rec_term.
  rewrite <- app_nil_l with (l := extend v (| A |) Gamma).
  apply typing_weaken; rewrite app_nil_l.
  apply H2.
  apply Ok_push; assumption.
  now apply typing_gives_terms in H2.
  exists (fun A : Type =>  STUnit A).
  split.
  now simpl.
  simpl.
  apply STTyUnit.
  auto.
Qed.

Lemma and_type_has_type_st3_not_topsig :
  forall {t e},
    not (TopSig t) ->
    and_coercion3 t e = inr e.
Proof.
  intros.
  generalize dependent e.
  induction t0; try simpl; auto.
  intros.
  assert (not (TopSig t0_2)).
  unfold not; intros HTS; apply H.
  apply TopSigF; apply HTS.
  apply IHt0_2 with (e := e) in H0.
  rewrite H0.
  reflexivity.
  exfalso; apply H; apply TopSigT.
Qed.
  
Lemma type_correct_coercions' :
  forall Gamma A B E, sub' A B E ->
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
    now apply typing_gives_terms in IHsub'2.
    rewrite <- open_rec_term.
    now apply typing_gives_terms in IHsub'2.
    now apply typing_gives_terms in IHsub'2.
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
    now apply typing_gives_terms in IHsub'1.
    rewrite <- open_rec_term; now apply typing_gives_terms in IHsub'1.
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
    apply IHsub'1.
    assumption.
    now apply typing_gives_terms in IHsub'1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub'2.
    assumption.
    now apply typing_gives_terms in IHsub'2.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  - pose (topsig_dec t0).
    inversion s; clear s.
    assert (Ha : exists r, and_coercion3 t0 ((fun A : Type => STApp A (c A) (STProj1 A (STBVar A 0)))) = inl r /\ has_type_st Gamma (r var) (|t0|)) by (apply and_type_has_type_st3; auto).
    destruct Ha as [r [HCoerce HHasTy]].
    rewrite HCoerce.
    apply_fresh STTyLam' as x.
    simpl.
    unfold open; rewrite <- open_rec_term.
    rewrite <- app_nil_l with (l := (extend x (STTuple (| t1 |) (| t2 |)) Gamma)).
    apply typing_weaken; rewrite app_nil_l.
    apply HHasTy.
    apply Ok_push; auto.
    now apply typing_gives_terms in HHasTy.
    eapply and_type_has_type_st3_not_topsig in H2.
    rewrite H2; simpl.
    apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub'.
    assumption.
    now apply typing_gives_terms in IHsub'.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  - pose (topsig_dec t0).
    inversion s; clear s.
    assert (Ha : exists r, and_coercion3 t0 ((fun A : Type => STApp A (c A) (STProj2 A (STBVar A 0)))) = inl r /\ has_type_st Gamma (r var) (|t0|)) by (apply and_type_has_type_st3; auto).
    destruct Ha as [r [HCoerce HHasTy]].
    rewrite HCoerce.
    apply_fresh STTyLam' as x.
    simpl.
    unfold open; rewrite <- open_rec_term.
    rewrite <- app_nil_l with (l := (extend x (STTuple (| t1 |) (| t2 |)) Gamma)).
    apply typing_weaken; rewrite app_nil_l.
    apply HHasTy.
    apply Ok_push; auto.
    now apply typing_gives_terms in HHasTy.
    eapply and_type_has_type_st3_not_topsig in H2.
    rewrite H2; simpl.
    apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub'.
    assumption.
    now apply typing_gives_terms in IHsub'.
    eapply STTyProj2.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
  - apply_fresh STTyLam' as x; cbn; apply STTyUnit.
    apply Ok_push; auto.
Qed.  
  
Lemma and_coercion_proj1_term' :
  forall t0 (c : Exp),
    STTerm (c var) ->
    STTerm (STLam' var (join_sum (and_coercion3 t0 (fun A : Type => (STApp A (c A) (STProj1 A (STBVar A 0)))))
        var)).
Proof.
  intros.
  apply_fresh STTerm_Lam' as x; unfold open; simpl.
  pose (topsig_dec t0).
  inversion s; clear s.
  assert (exists r : Exp, and_coercion3 t0 (fun A : Type =>
                          STApp A (c A) (STProj1 A (STBVar A 0))) = inl r /\ STTerm (r var)).
  apply and_type_term3; auto.
  inversion H1.
  inversion H2.
  rewrite H3.
  simpl.
  rewrite <- open_rec_term; auto.
  eapply and_type_has_type_st3_not_topsig in H0.
  rewrite H0.
  simpl.
  apply STTerm_App; auto.
  rewrite <- open_rec_term; auto.
Qed.

Lemma and_coercion_proj2_term' :
  forall t0 (c : Exp),
    STTerm (c var) ->
    STTerm (STLam' var (join_sum (and_coercion3 t0 (fun A : Type => (STApp A (c A) (STProj2 A (STBVar A 0)))))
        var)).
Proof.
  intros.
  apply_fresh STTerm_Lam' as x; unfold open; simpl.
  pose (topsig_dec t0).
  inversion s; clear s.
  assert (exists r : Exp, and_coercion3 t0 (fun A : Type =>
                          STApp A (c A) (STProj2 A (STBVar A 0))) = inl r /\ STTerm (r var)).
  apply and_type_term3; auto.
  inversion H1.
  inversion H2.
  rewrite H3.
  simpl.
  rewrite <- open_rec_term; auto.
  eapply and_type_has_type_st3_not_topsig in H0.
  rewrite H0.
  simpl.
  apply STTerm_App; auto.
  rewrite <- open_rec_term; auto.
Qed.

Lemma coercions_produce_terms' :
  forall E A B, sub' A B E -> STTerm (E var).
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
  - apply and_coercion_proj1_term'; auto.
  (* Case SAnd3 *)
  - apply and_coercion_proj2_term'; auto.
  (* Case STop *)
  - apply_fresh STTerm_Lam' as x; cbn.
    apply STTerm_Unit.
Qed.

(* Subtyping rules produce type-correct coercions: Lemma 3 *)
Lemma type_correct_coercions' :
  forall Gamma A B E, sub A B E ->
             ok Gamma -> 
             has_type_st Gamma (E var) (STFun (|A|) (|B|)) .
Proof.
  intros.
  pose (topsig_dec B).
  inversion s; clear s.
  induction H.
  admit.
  admit.
  admit.
  remember (and_coercion t0
        (fun A : Type => STLam' A (STApp A (c A) (STProj1 A (STBVar A 0)))) 0
        var).
  symmetry in Heqs.
  apply (and_coercion_rewrite_topsig _ _ _ _ H1) in Heqs.

  (*
  inversion Heqs.
  induction x.
  rewrite <- H3.
  simpl.
  *)
  
  (* eapply (and_coercion_rewrite_topsig _ _ _ _ H1) in Heqs. *)
Admitted.
  
(* Subtyping rules produce type-correct coercions: Lemma 3 *)
Lemma type_correct_coercions :
  forall Gamma A B E, sub A B E ->
             ok Gamma -> 
             has_type_st Gamma (E var) (STFun (|A|) (|B|)) .
Proof.
  intros.
  induction H. Print sub.
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
  - generalize dependent IHsub.
    induction t0; intros.
    simpl.
    apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    subst; apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    induction t0_2.
    simpl; apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    subst; apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    simpl in *.
    destruct t
    SearchAbout Atomic.
    admit.

    Print sub. inversion H. simpl.
    
    induction H1.
    apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    subst; apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj1.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity. simpl.
    admit. (* admit.
    simpl. apply_fresh STTyLam' as x; simpl in *.
    unfold open.
    rewrite <- open_rec_term.
    apply STTyUnit.
    apply Ok_push; auto.
    auto. *)
  (* SAnd3 *)
  - inversion H1.
    apply_fresh STTyLam' as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    subst; apply IHsub.
    assumption.
    now apply coercions_produce_terms in H.
    eapply STTyProj2.
    apply STTyVar.
    apply Ok_push; auto.
    left; reflexivity.
    admit.
  (* STop *)
  - apply_fresh STTyLam' as x; cbn. apply STTyUnit.
    apply Ok_push; auto.
Admitted.

  
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
  - apply STTyUnit.
    apply (ok_map Gamma H).
Defined.
    
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
  (* Ann *)
  - simpl in *.
    erewrite (IHt1 n t0 x H H0 H1).
    reflexivity.
  - simpl in *.
    destruct t0; simpl in *; try now inversion H1.
    destruct (Nat.eqb n n0); inversion H1.
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
(* Case Ann *)
destruct IHhas_type_source.
apply tyann. apply (tysub _ _ A); auto.
destruct IHhas_type_source.
auto.
(* Case Top *)
apply tytop.
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
apply tvar; auto.
(* PFLit *)
apply tlit; auto.
(* App *)
apply (tapp _ A). auto. auto.
(* Merge *)
apply tmerge; auto.
(* Ann *)
apply (tsub _ _ A). auto. apply reflex.
now apply typing_wf_source_alg in H0.
(* Lam *)
apply_fresh tlam as x.
assert (d: not (In x L)) by (not_in_L x).
intros. pose (H0 x d).
unfold open_source in h. unfold open_source.
rewrite (erase_open t0 0 (PFVar x)) in h. auto.
(* Sub *)
apply (tsub _ _ A). auto. unfold Sub. exists C. auto. auto.
(* Top *)
apply ttop.
auto.
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
subst.
inversion H7.
now apply typing_wf_source_alg in H0.
(* Case Merge *)
inversion H.
apply IHe1 in H6.
apply IHe2 in H7.
apply (tymerge); auto.
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

End CoherenceTop.



