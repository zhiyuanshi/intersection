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

Inductive SExp (A : Type) :=
  | STVar   : A -> SExp A
  | STLit   : nat -> SExp A
  | STLam   : STyp -> (A -> SExp A) -> SExp A
  | STApp   : SExp A -> SExp A -> SExp A
  | STPair  : SExp A -> SExp A -> SExp A
  | STProj1 : SExp A -> SExp A
  | STProj2 : SExp A -> SExp A
  | STUnit   : SExp A.

Definition Exp := forall A, SExp A.

(* Our calculus: *)

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

Require Import Arith.
Require Import Setoid.

Inductive TopLike : PTyp -> Prop :=
| TLTop : TopLike TopT
| TLAnd : forall A B, TopLike A -> TopLike B -> TopLike (And A B).

(* Unrestricted Subtyping *)

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4) 
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2) 
  | USAnd2 : forall t t1 t2 , usub t1 t -> usub (And  t1 t2) t 
  | USAnd3 : forall t t1 t2, usub t2 t -> usub (And  t1 t2) t 
  | USTop : forall t, usub t TopT.

(* TODO: Show transitivity of usub here, and easily derive transitivity 
for sub *)

(* Restricted Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

Inductive sub : PTyp -> PTyp -> Exp -> Prop :=
  | SInt : sub PInt PInt (fun A => STLam _ STInt (fun x => STVar _ x))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun  o3 o4) (fun A => STLam _ (ptyp2styp (Fun o1 o2)) (fun f => 
       STLam _ (ptyp2styp o3) (fun x => STApp _ (c2 A) (STApp _ (STVar _ f) (STApp _ (c1 A) (STVar _ x))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (fun A => STLam _ (ptyp2styp t1) (fun x => 
       STPair _ (STApp _ (c1 A) (STVar _ x)) (STApp _ (c2 A) (STVar _ x))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x => 
       (STApp _ (c A) (STProj1 _ (STVar _ x)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x => 
       (STApp _ (c A) (STProj2 _ (STVar _ x)))))
  | STop : forall t, sub t TopT (fun A => STUnit _).

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:Exp), sub t1 t2 e.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt.
unfold Sub. exists (fun A => STLam _ STInt (fun x => STVar _ x)). 
exact SInt.
Defined.

Definition stop : forall t, Sub t TopT.
intros; unfold Sub.
exists (fun A => STUnit _).
apply STop.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (fun A => STLam _ (ptyp2styp (Fun o1 o2)) (fun f => 
       STLam _ (ptyp2styp o3) (fun x1 => STApp _ (x0 A) (STApp _ (STVar _ f) (STApp _ (x A) (STVar _ x1)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (fun A => STLam _ (ptyp2styp t1) (fun x1 => 
       STPair _ (STApp _ (x A) (STVar _ x1)) (STApp _ (x0 A) (STVar _ x1)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x1 => 
       (STApp _ (x A) (STProj1 _ (STVar _ x1))))).
apply SAnd2. auto. auto. destruct H.
exists (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x1 => 
       (STApp _ (x A) (STProj1 _ (STVar _ x1))))).
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
exists (fun A => STLam _ (ptyp2styp t1) (fun x => 
       STPair _ (STApp _ (x0 A) (STVar _ x)) (STApp _ (x1 A) (STVar _ x)))).
apply SAnd1. auto. auto.
inversion H1.
inversion H1.
(* Case Top *)
apply stop. (* a top case here *)
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And  t1 t2) t.
unfold Sub. intros. destruct t. destruct H.
exists (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x1 => 
       (STApp _ (x A) (STProj2 _ (STVar _ x1))))).
apply SAnd3. auto. auto. destruct H.
exists (fun A => STLam _ (ptyp2styp (And t1 t2)) (fun x1 => 
       (STApp _ (x A) (STProj2 _ (STVar _ x1))))).
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
exists (fun A => STLam _ (ptyp2styp t1) (fun x => 
       STPair _ (STApp _ (x0 A) (STVar _ x)) (STApp _ (x1 A) (STVar _ x)))).
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
(*  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4) *)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt.
(*  | OTop1 : forall t, not (t = TopT) -> Ortho t TopT
  | OTop2 : forall t, not (t = TopT) -> Ortho TopT t.*)

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
pose (H0 PInt sint sint). inversion t.
apply OIntFun. 
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
apply OFunInt. 
destruct H0.
assert (TopLike (Fun (And t1 t0) TopT)).
apply H2.
apply sfun. apply sand2. apply reflex. apply stop.
apply sfun. apply sand3. apply reflex. apply stop.
inversion H3.
(* Case t11 -> t12 _|_ t21 & t22 *)
destruct H2. destruct H0. destruct H2. destruct H0.
apply OAnd2.
apply IHWFTyp1. unfold OrthoS. split; auto.
apply IHWFTyp2. unfold OrthoS. split; auto.
(* Case t11 -> t12 _|_ T *)
destruct H0. destruct H. destruct H1. apply TLTop.
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
(* Case FunFun *)
unfold OrthoS. split. split; unfold not; intros; inversion H.
induction C; intros. inversion H0. inversion H1. inversion H. inversion H1.
inversion H. inversion H1. inversion H0. inversion H8.
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
inversion H.
unfold not. intros. inversion H.
induction C; intros. inversion H. inversion H1. inversion H0. inversion H1.
apply TLAnd.
apply IHC1.
inversion H. inversion H1. unfold Sub. exists c1. auto.
inversion H0. inversion H1. unfold Sub. exists c1. auto.
apply IHC2.
inversion H. inversion H1. unfold Sub. exists c2. auto.
inversion H0. inversion H1. unfold Sub. exists c2. auto.
(* TopT *)
apply TLTop.
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
assert (TopLike t). apply H15. unfold Sub.
exists c; auto. unfold Sub. exists c0. auto.
inversion H16. rewrite <- H17 in H2. inversion H2.
rewrite <- H19 in H2. inversion H2.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* Case: And t1 t2 <: t (second) *)
inversion H3; inversion H.
rewrite <- H7 in H2. inversion H2.
(* contradiction: not orthogonal! *)
destruct H14.
inversion H14.
assert (TopLike t). apply H15.
unfold Sub. exists c0. auto.
unfold Sub. exists c. auto.
inversion H18. rewrite <- H19 in H2. inversion H2.
rewrite <- H21 in H2. inversion H2.
(* same coercion; no contradiction *)
assert (c = c0). apply IHsub; auto. rewrite H15.
reflexivity.
(* top case *)
rewrite <- H5 in H2. inversion H2.
(* last top case *)
inversion H1. inversion H3. inversion H3.
reflexivity.
Defined.

