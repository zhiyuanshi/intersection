Require Import String.

(* Notes:

The syntax is encoded using Chipala's Parametric HOAS:

http://adam.chlipala.net/papers/PhoasICFP08/

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
  | STTuple : STyp -> STyp -> STyp
  | STUnitT : STyp.

Inductive SExp :=
  | STVar   : nat -> SExp (* de Bruijn indices *)
  | STLit   : nat -> SExp
  | STLam   : SExp -> SExp
  | STApp   : SExp -> SExp -> SExp
  | STPair  : SExp -> SExp -> SExp
  | STProj1 : SExp -> SExp
  | STProj2 : SExp -> SExp
  | STUnit   : SExp.

(*
Inductive Simp : SExp -> SExp -> Prop :=
  | NormLam : forall E1 E2, Simp E1 E2 -> Simp (STLam E1) (STLam E2)
  | NormUnit : forall E, Simp (STApp (STLam STUnit) E) STUnit.
*)

Fixpoint simp (e : SExp) : SExp :=
  match e with
    | STLam E => STLam (simp E)
    | STApp (STLam STUnit) E => STUnit
    | STApp (STLam (STLam STUnit)) E => STLam STUnit
    | _ => e
  end.

(*
Definition substitute (n : nat) (e1 : SExp) (e2 : SExp) : SExp :=
  match e2 with
    | STVar v => if (eq_nat_dec n v) then e1 else STVar v
    | STLit i => STLit i
    | STLam e => 
*)

(* Our calculus: *)

(* Types *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp
  | TopT : PTyp.

(*
Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | TopT => STUnitT
  end.
*)

Require Import Arith.
Require Import Setoid.

(* Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

Inductive sub : PTyp -> PTyp -> SExp -> Prop :=
  | SInt : sub PInt PInt (STLam (STVar 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun  o3 o4) (simp (STLam (STLam (STApp c2 (STApp (STVar 1) (STApp c1 (STVar 0)))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (STLam (STPair (STApp c1 (STVar 0)) (STApp c2 (STVar 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t -> 
     sub (And  t1 t2) t (simp (STLam (STApp c (STProj1 (STVar 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t -> 
     sub (And  t1 t2) t (simp (STLam (STApp c (STProj2 (STVar 0)))))
  | STop : forall t, sub t TopT (STLam STUnit).

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (STLam (STVar 0)). 
exact SInt.
Defined.


Definition stop : forall t, Sub t TopT.
intros; unfold Sub.
exists (STLam STUnit).
apply STop.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (simp (STLam (STLam (STApp x0 (STApp (STVar 1) (STApp x (STVar 0))))))). 
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (STLam (STPair (STApp x (STVar 0)) (STApp x0 (STVar 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (simp (STLam (STApp x (STProj1 (STVar 0))))).
apply SAnd2. auto. auto. destruct H.
exists (simp (STLam (STApp x (STProj1 (STVar 0))))).
apply SAnd2. auto. auto.
inversion H0.
apply stop. (* a top case here *)
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
exists (STLam (STPair (STApp x0 (STVar 0)) (STApp x1 (STVar 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
(* Case Top *)
apply stop. (* a top case here *)
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (simp (STLam (STApp x (STProj2 (STVar 0))))).
apply SAnd3. auto. auto. destruct H.
exists (simp (STLam (STApp x (STProj2 (STVar 0))))).
apply SAnd3. auto. auto.
inversion H0.
apply stop. (* a top case here *)
Defined.

(* Theorem 4 *)

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And  t1 t2) t.
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
exists (STLam (STPair (STApp x0 (STVar 0)) (STApp x1 (STVar 0)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
(* Case Top *)
apply stop. (* top case *)
Defined.


(* Disjointness: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt
  | OTop1 : forall t, Ortho t TopT
  | OTop2 : forall t, Ortho TopT t.

(* Top-Like *)

Inductive TopLike : PTyp -> Prop :=
  | TLTop : TopLike TopT
  | TLFun : forall t1 t2, TopLike t2 -> TopLike (Fun t1 t2)
  | TLAnd1 : forall t1 t2, TopLike t1 -> TopLike (And t1 t2)
  | TLAnd2 : forall t1 t2, TopLike t2 -> TopLike (And t1 t2).

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := forall C, Sub A C -> Sub B C -> TopLike C.

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2)
  | WFTop : WFTyp TopT.

(* Reflexivity *)
Hint Resolve sint sfun sand1 sand2 sand3 SInt SFun SAnd1 SAnd2 SAnd3 stop.

Lemma reflex : forall (t1 : PTyp), Sub t1 t1.
Proof.
induction t1; intros; auto.
Defined.

(* Disjointness algorithm is complete: Theorem 7 *)

Lemma ortho_completness : forall (t1 t2 : PTyp), OrthoS t1 t2 -> Ortho t1 t2.
Proof.
induction t1; intros.
(* Case PInt *)
induction t2. 
pose (H PInt sint sint). inversion t.
apply OIntFun.
apply OAnd2. 
apply IHt2_1. unfold OrthoS. intros; apply H.
exact H0. apply sand2. exact H1.
apply IHt2_2. unfold OrthoS. intros. apply H.
auto. apply sand3.
auto. apply OTop1.
(* Case Fun t1 t2 *)
induction t2.
apply OFunInt. 
apply OFun.
apply IHt1_2. unfold OrthoS. intros.
unfold OrthoS in H.
assert (TopLike (Fun (And t1_1 t2_1) C)).
apply H.
apply sfun.
apply sand2.
apply reflex.
auto.
apply sfun.
apply sand3. apply reflex.
auto. inversion H2. auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2.
apply IHt2_1.
unfold OrthoS. intros. 
apply H.
auto. apply sand2. exact H1.
apply IHt2_2.
unfold OrthoS. intros. apply H.
auto. apply sand3. exact H1.
(* Case t11 -> t12 _|_ T *)
apply OTop1.
(* Case (t11 & t12) _|_ t2 *) 
apply OAnd1.
apply IHt1_1.
unfold OrthoS.
intros.
apply H.
(*clear H. destruct H0. destruct H.
exists x.
split.*)
apply sand2. exact H0.
exact H1.
apply IHt1_2.
unfold OrthoS; intros. 
apply H. 
apply sand3.
exact H0.
exact H1.
(* Case T _|_ t2 *)
apply OTop2.
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
(* Top cases *)
inversion H. inversion H0. split; unfold Sub. exists c1. auto. exists c2. auto.
Defined.

(* Unique subtype contributor: Lemma 4 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> Sub (And A B) C -> not (TopLike C) -> not (Sub A C /\ Sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. destruct H2.
pose (H C H2 H3). contradiction. 
Defined.

(* Lemmas needed to prove soundness of the disjointness algorithm *)

Lemma ortho_sym : forall A B, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS. 
intros. apply H.
auto. auto.
Defined.

Lemma ortho_and : forall A B C, OrthoS A C -> OrthoS B C -> OrthoS (And A B) C.
Proof.
intros. unfold OrthoS.
intros.
induction C0. 
inversion H1. inversion H3. apply H. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
apply H0.  
unfold Sub. exists c. auto. auto.
inversion H1. inversion H3.
apply H. unfold Sub. exists c. auto. auto.
apply H0. unfold Sub. exists c. auto. auto.
assert (Sub C C0_1 /\ Sub C C0_2). apply invAndS1. auto. destruct H3.
inversion H1. inversion H5.  
apply TLAnd1. apply IHC0_1. 
unfold Sub.  exists c1. auto. auto.
apply H. 
unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
apply H0. unfold Sub. exists c. auto. unfold Sub.  unfold Sub in H2. destruct H2. exists x0. auto.
apply TLTop.
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
unfold OrthoS. intros.
generalize H0. generalize H1. clear H0. clear H1.
induction C; intros. inversion H1. inversion H2.
apply TLFun. 
apply IHOrtho.
inversion H0. inversion H2. unfold Sub. exists c2. auto. unfold Sub. inversion H1. inversion H2. exists c2. auto.
apply TLAnd1.
apply IHC1.
inversion H1. inversion H2. unfold Sub. exists c1. auto. 
inversion H0. inversion H2. exists c1. auto.
(* TopT *)
apply TLTop.
(* Case IntFun *)
unfold OrthoS. intros.
induction C. inversion H0. inversion H1. inversion H. inversion H1.
apply TLAnd1.
apply IHC1.
inversion H. inversion H1. unfold Sub. exists c1. auto.
inversion H0. inversion H1. unfold Sub. exists c1. auto.
(* TopT *)
apply TLTop.
(* Case FunInt *)
unfold OrthoS. intros.
induction C. inversion H. inversion H1. inversion H0. inversion H1.
apply TLAnd1.
apply IHC1. inversion H. inversion H1. unfold Sub. exists c1. auto.
inversion H0. inversion H1. unfold Sub. exists c1. auto.
(* TopT *)
apply TLTop.
(* t TopT *)
unfold OrthoS; intros. generalize t H H0. clear t H H0. 
induction C; intros; try (inversion H0; inversion H1). 
apply TLAnd1. apply (IHC1 TopT); unfold Sub; exists c1; auto.
apply TLTop.
(* TopT t *)
unfold OrthoS; intros. generalize t H H0. clear t H H0. 
induction C; intros; try (inversion H; inversion H1).
apply TLAnd1. apply (IHC1 TopT); unfold Sub; exists c1; auto.
apply TLTop.
Defined.

Inductive Coerce : SExp -> Prop :=
  | CZero : Coerce (STLam STUnit)
  | CSucc : forall c, Coerce c -> Coerce (STLam c).

Require Import Coq.Program.Equality.

Lemma coerceUnit : forall {B}, TopLike B -> forall {A c}, sub A B c -> Coerce c.
intro. intro.
induction H; intros.
(* case TopT *)
inversion H. inversion H1. inversion H1.
apply CZero.
(* Case Fun *)
inversion H0. 
pose (IHTopLike _ _ H6).


Lemma sameCoercion : forall {C}, TopLike C -> 
                                 forall A B D c1 c2, sub A (Fun B C) c1 -> sub D (Fun B C) c2 -> Coerce c1 = Coerce c2.
intros.



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
unfold OrthoS in H14.
assert (TopLike t). apply H14.
unfold Sub. exists c. auto. unfold Sub. exists c0. auto.
inversion H9. rewrite <- H16 in H15. inversion H15.
rewrite H15
admit.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* Case: And t1 t2 <: t (second) *)
inversion H3; inversion H.
rewrite <- H7 in H2. inversion H2.
(* contradiction: not orthogonal! *)
admit.
(*
destruct H14. exists t. unfold Sub.
split. exists c0; auto. exists c. auto.*)
(* same coercion; no contradiction *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* last top case *)
inversion H1. inversion H3. inversion H3.
reflexivity.
Defined.

