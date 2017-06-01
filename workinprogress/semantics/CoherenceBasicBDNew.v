Set Implicit Arguments.
Require Import LibLN STLCNew.
Require Import Coq.Program.Tactics.


(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the correnposing lemmas/theorems in the paper. 
The reader can just look for:sub

Lemma 4

for example, to look for the proof of lemma 4 in the paper.

All lemmas and theorems are complete: there are no uses of admit or Admitted,
with the exceptions of "tlam" and "tylam" due to a technical limitation.

*)

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

(* Subtyping relation *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2).

Inductive sub : PTyp -> PTyp -> SExp -> Prop :=
  | SInt : sub PInt PInt (STLam (STBVar 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun o3 o4) (STLam (STLam (STApp c2 (STApp (STBVar 1) (STApp c1 (STBVar 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (STLam
       (STPair (STApp c1 (STBVar 0)) (STApp c2 (STBVar 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam ((STApp c (STProj1 (STBVar 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam ((STApp c (STProj2 (STBVar 0))))).

Hint Constructors sub Atomic.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e: SExp), sub t1 t2 e.

Hint Unfold Sub.

(* Smart constructors for Sub *)

Definition sint : Sub PInt PInt. eauto. Defined.

Definition sfun : forall o1 o2 o3 o4,
                    Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
  introv [c1 H1] [c2 H2]; autos*. Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
  introv [c1 H1] [c2 H2]; autos*. Defined.

Definition sand2_atomic : forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
  introv [c1 H1] HAtomic; autos*. Defined.

Hint Resolve sint sfun sand1 sand2_atomic.

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
intro t.
induction t; intros; autos*.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
eauto.
inversion H1.
inversion H1.
Defined.

Definition sand3_atomic : forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And t1 t2) t.
  introv [c1 H1] HAtomic; autos*. Defined.

Hint Resolve sand2 sand3_atomic.

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
  intro t.
  induction t; intros; autos*.
(* Case And *)
unfold Sub. unfold Sub in H. destruct H. inversion H.
assert (Sub (And t0 t3) t1). apply IHt1.
unfold Sub. exists c1. auto. 
assert (Sub (And t0 t3) t2). apply IHt2.
unfold Sub. exists c2. auto.
unfold Sub in H6. destruct H6.
unfold Sub in H7. destruct H7.
eauto.
inversion H1.
inversion H1.
Defined.

Hint Resolve sand3.

(* Disjointness: Implementation *)

Inductive Ortho : PTyp -> PTyp -> Prop :=
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (And t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (And t2 t3)
  | OFun  : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (Fun t1 t2) (Fun t3 t4)
  | OIntFun : forall t1 t2, Ortho PInt (Fun t1 t2)
  | OFunInt : forall t1 t2, Ortho (Fun t1 t2) PInt.

Hint Constructors Ortho.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

(* Well-formed types *)

Inductive WFTyp : PTyp -> Prop := 
  | WFInt : WFTyp PInt
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (Fun t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (And t1 t2).

Hint Constructors WFTyp.

(* Reflexivity *)
Lemma reflex : forall (t1 : PTyp), Sub t1 t1.
Proof. induction t1; intros; autos*. Qed.

(* Disjointness algorithm is complete: Theorem 8 *)

Lemma ortho_completeness : forall (t1 t2 : PTyp), OrthoS t1 t2 -> Ortho t1 t2.
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
Qed.

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
Qed.


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
Qed.

(* Unique subtype contributor: Lemma 2 *)

Lemma uniquesub : forall A B C, 
  OrthoS A B -> Sub (And A B) C -> not (Sub A C /\ Sub B C).
Proof.
intros. unfold OrthoS in H. unfold not. intros. apply H. exists C. auto.
Qed.

(* Lemmas needed to prove soundness of the disjointness algorithm *)

Lemma ortho_sym : forall A B, OrthoS A B -> OrthoS B A.
Proof.
unfold OrthoS. unfold not.
intros. apply H.
destruct H0. destruct H0.
exists x.
split; auto.
Qed.

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

(* Soundness of the disjointness algorithm: Theorem 7 *)

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

(* Coercive subtyping is coeherent: Lemma 3 *)

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
Qed.


(* typing rules of lambda i *)

(* Definitions borrowed from STLC_Tutorial *)

(* Our source language *)
Inductive PExp :=
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp                   
  | PLit   : nat -> PExp
  | PLam   : PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp
  | PAnn   : PExp -> PTyp -> PExp.

(* Free variables *)

(** Source language **)
Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
    | PFVar v => \{v}
    | PBVar _ => \{}
    | PLit _ => \{}
    | PLam t => fv_source t
    | PApp t1 t2 => (fv_source t1) \u (fv_source t2)
    | PMerge t1 t2 => (fv_source t1) \u (fv_source t2)
    | PAnn t1 A => fv_source t1
  end.


(* Tactics dealing with instantiation of fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  let C := gather_vars_with (fun (x : ctx) => dom x) in
  let D := gather_vars_with (fun (x : env PTyp) => dom x) in
  let E := gather_vars_with (fun x : PExp => fv_source x) in
  let F := gather_vars_with (fun (x : SExp) => fv x) in
  constr:(A \u (B \u (C \u (D \u (E \u F))))).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(** The tactic [apply_fresh* T as y] is the same as 
    [apply_fresh T as y] except that it calls [intuition eauto]
    subsequently. It is also possible to call [apply_fresh]
    without specifying the name that should be used.
*)

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i      => If k = i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x                     
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  end.

Definition open_source t u := open_rec_source 0 u t.

(* Functions on contexts *)

Definition conv_context (env : env PTyp) : ctx :=
  map ptyp2styp env.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).
Notation "'∥' t '∥'" := (conv_context t) (at level 60).

Hint Unfold ptyp2styp conv_context.

Lemma ok_map : forall Gamma, ok Gamma -> ok (∥ Gamma ∥).
Proof. introv H; unfold ptyp2styp, conv_context; induction H; simpls*. Qed.

Lemma fv_source_distr :
  forall t1 t2 x n, x \in (fv_source (open_rec_source n t2 t1)) ->
               x \in ((fv_source t1) \u (fv_source t2)).
Proof.
  introv H.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; autos*; rewrite* in_union; try case_nat*.
  - rewrites* in_union in *;
    destruct H; [ forwards* : IHt1_1 n t2 | forwards* : IHt1_2 n t2 ];
    rewrites* in_union in *.
  - rewrites* in_union in *;
    destruct H; [ forwards* : IHt1_1 n t2 | forwards* : IHt1_2 n t2 ];
    rewrites* in_union in *.
Qed.  

Lemma fv_source_distr2 : forall z n t1 t2,
                    z \notin (fv_source t1) ->
                    z \notin (fv_source t2) ->
                    z \notin (fv_source (open_rec_source n t2 t1)).
Proof.
  introv H1 H2; gen n t2; induction t1; intros; simpls*; case_nat*.
Qed.

Hint Resolve fv_source_distr fv_source_distr2.

(* Typing rules of source language: Figure 2 
Note that we generate an Annotated expression, which serves as evidence for bi-directional
type-checking completness proof.
 *)

(* Declarative type system *)

Inductive has_type_source : env PTyp -> PExp -> PTyp -> PExp -> Prop :=
  | TyVar : forall Gamma x ty,
            ok Gamma -> 
            binds x ty Gamma ->
            WFTyp ty ->
            has_type_source Gamma (PFVar x) ty (PFVar x)
  | TyLit : forall Gamma x, ok Gamma -> has_type_source Gamma (PLit x) PInt (PLit x)
  | TyLam : forall L Gamma t t1 A B, (forall x, x \notin L -> 
                                  has_type_source (Gamma & x ~ A) (open_source t (PFVar x)) B (open_source t1 (PFVar x))) ->
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
              has_type_source Gamma t B (PAnn t' B).

Hint Constructors has_type_source.

Inductive PTerm : PExp -> Prop :=
  | PTerm_Var : forall x,
      PTerm (PFVar x)
  | PTerm_Lit : forall n,
      PTerm (PLit n)
  | PTerm_Lam : forall L t1,
      (forall x, x \notin L -> PTerm (open_source t1 (PFVar x))) ->
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
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.
  case_nat*. case_nat*.  
Qed.  

Lemma open_rec_source_term : forall t u,
  PTerm t -> forall k, t =  open_rec_source k u t.
Proof.
  induction 1; intros; simpls; fequals*.
  pick_fresh x. apply* (@open_rec_term_source_core t1 0 (PFVar x)).
Qed.


Fixpoint subst_source (z : var) (u : PExp) (t : PExp) {struct t} : PExp :=
  match t with
    | PBVar i      => PBVar i
    | PFVar x      => If x = z then u else (PFVar x)
    | PLit i       => PLit i
    | PLam t1      => PLam (subst_source z u t1)
    | PApp t1 t2   => PApp (subst_source z u t1) (subst_source z u t2)
    | PMerge t1 t2 => PMerge (subst_source z u t1) (subst_source z u t2)
    | PAnn t1 t2   => PAnn (subst_source z u t1) t2 
  end.


Lemma subst_source_fresh : forall t x u, 
  x \notin (fv_source t) -> subst_source x u t = t.
Proof. intro t; induction t; intros; simpls*; fequals*; case_var*. Qed.

Hint Resolve open_rec_source_term subst_source_fresh.

(** Substitution distributes on the open operation. *)

Lemma subst_source_open : forall x u t1 t2, PTerm u -> 
  subst_source x u (open_source t1 t2) = open_source (subst_source x u t1) (subst_source x u t2).
Proof.
  intros. unfold open_source. generalize 0.
  induction t1; intros; simpl; simpls*; fequals*.
  case_var*. case_nat*.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_source_open_var : forall (x y : var) u t, not (x = y) -> PTerm u ->
  open_source (subst_source x u t) (PFVar y) = subst_source x u (open_source t (PFVar y)).
Proof. intros; rewrite* subst_source_open; simpls; case_var*. Qed.

Hint Rewrite subst_source_open subst_source_open_var.

(** Opening up an abstraction of body [t] with a term [u] is the same as opening
  up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)

Lemma subst_source_intro : forall x t u, 
  x \notin (fv_source t) -> PTerm u ->
  open_source t u = subst_source x u (open_source t (PFVar x)).
Proof.
  intros; rewrite* subst_source_open; rewrite* subst_source_fresh; simpls*; case_var*.
Qed.

Hint Rewrite subst_source_intro.

Lemma subst_fresh_var :
  forall x z t, x \notin (fv_source t) ->
           subst_source x (PFVar z) (open_source t (PFVar x)) = open_source t (PFVar z).
Proof.
  introv H1.
  rewrite* subst_source_open; simpls*; case_var*; rewrite* subst_source_fresh.
Qed.

(** We prove that terms are stable by substitution *)

Lemma subst_source_term : forall t z u,
  PTerm u -> PTerm t -> PTerm (subst_source z u t).
Proof.
  induction 2; simpls*; autos*.
  case_var*.
  apply_fresh* PTerm_Lam as x; rewrite* subst_source_open_var.
Qed.

Hint Resolve subst_source_term.

Lemma type_correct_source_terms : forall Gamma E ty e, has_type_source Gamma E ty e -> PTerm E.
Proof. intros; induction H; autos*. Qed.

Lemma type_correct_source_terms' : forall Gamma E ty e, has_type_source Gamma e ty E -> PTerm E.
Proof. intros; induction H; autos*. Qed.

Lemma typing_source_ok_env : forall Gamma E ty e, has_type_source Gamma E ty e -> ok Gamma.
Proof.
  introv H; induction H; auto.
  pick_fresh x.
  assert (Ha: x \notin L) by auto.
  lets* H2 : H0 x.
Qed.
  

Lemma typing_wf_source :
  forall Gamma t T E, has_type_source Gamma t T E -> WFTyp T.
Proof.
  introv H; induction H; autos*.
  pick_fresh x; autos*.
  inverts* IHhas_type_source1.
Qed.  

Hint Resolve type_correct_source_terms type_correct_source_terms'.
Hint Resolve typing_source_ok_env typing_wf_source.

Lemma typing_weaken_source : forall G E F t T d,
   has_type_source (E & G) t T d -> 
   ok (E & F & G) ->
   has_type_source (E & F & G) t T d.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; substs*.
  apply* TyVar. apply* binds_weaken.
  apply_fresh* TyLam as y. apply_ih_bind* H0.
Qed.

Lemma typing_weaken_source_extend : forall x E t T d A,
   has_type_source E t T d -> 
   x \notin (dom E) ->
   has_type_source (E & x ~ A) t T d.
Proof.
  introv Typ H.
  rewrite <- concat_empty_r with (E := x ~ A).
  rewrite concat_assoc.
  apply typing_weaken_source.
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.

Lemma typing_strengthen_source : forall z U E F t T d,
  z \notin (fv_source t) ->
  has_type_source (E & z ~ U & F) t T d ->
  has_type_source (E & F) t T d.
Proof.
  intros.
  remember (E & z ~ U & F).
  gen Heqe. gen F. 
  induction H0; intros; substs*; simpls*.
  - apply* TyVar; simpls*; apply* binds_remove.
  - apply_fresh* TyLam as x.
    apply_ih_bind* H1; apply* fv_source_distr2; simpls*.
Qed.
  
Definition has_type Gamma e t := exists s, has_type_source Gamma e t s.

Definition tvar :
  forall Gamma x ty, ok Gamma -> binds x ty Gamma -> WFTyp ty -> has_type Gamma (PFVar x) ty.
intros.  unfold has_type. exists (PFVar x). auto. Defined.

Definition tlit : forall Gamma x, ok Gamma -> has_type Gamma (PLit x) PInt.
intros. unfold has_type. exists (PLit x); auto. Defined.


Lemma fv_source_distr_open_l :
  forall t1 t2 x n, x \in (fv_source t1) ->
               x \in (fv_source t2) ->
               x \in (fv_source (open_rec_source n t2 t1)).
Proof.
  induction t1; intros; simpls*.
  case_nat*. rewrites* in_union in *. rewrites* in_union in *.
Qed.

(*
not (In y (dom Gamma)) =>  
(x,A)::Gamma :- t1 ^ x : B (-> t2 ^ x) => 
(y,A)::Gamma :- [x -> y] (t1 ^ x) : B (-> [x -> y] (t2 ^ x))
 *)
  
Lemma tsubst :
  forall E F t1 t2 x y A B,
    y \notin (dom (E & F)) ->
    has_type_source (E & x ~ A & F) (open_source t1 (PFVar x)) B (open_source t2 (PFVar x)) ->
    has_type_source (E & y ~ A & F) (subst_source x (PFVar y) (open_source t1 (PFVar x))) B (subst_source x (PFVar y) (open_source t2 (PFVar x))).
Proof.
  intros.
  remember (E & x ~ A & F) as G.
  generalize dependent HeqG.
  generalize dependent E.
  generalize dependent F.
  induction H0; intros; simpls*.
  case_var*; substs*.
  apply* TyVar.
  lets* [H3 H4] : ok_middle_inv H.
Admitted.
 
Lemma fv_source_in_open :
  forall x z t0 n, x <> z ->
              x \in (fv_source t0) ->
              x \in (fv_source (open_rec_source n (PFVar z) t0)). 
Proof.
  intros. gen n.
  induction t0; simpls*.
  rewrite* in_empty in H0.
  intros; rewrite in_union in *; autos*.
  intros; rewrite in_union in *; autos*.
Qed.
 
  
Lemma env_impl_fv_source :
  forall Gamma x t A E, has_type_source Gamma t A E -> x \in (fv_source t) -> x \in (dom Gamma).
Proof.
  intros.
  induction H; simpls*.
  - rewrite in_singleton in H0; substs*; apply* get_some_inv.
  - rewrite* in_empty in H0.
  - pick_fresh y.
    assert (Ha1 : y \notin \{ x}) by autos*.
    assert (Ha2 : y \notin L) by autos*.
    assert (Ha3 : x \in fv_source (open_source t (PFVar y))) by
        apply* fv_source_in_open.
    lets* H3 : H1 Ha2 Ha3.
    rewrite dom_concat in H3; rewrite in_union in H3.
    destruct H3; autos*.
    rewrite* dom_single in H3.
    unfold "\notin" in Ha1; rewrite in_singleton in *.
    tryfalse.
  - rewrite in_union in H0; inverts* H0.
  - rewrite in_union in H0; inverts* H0.
Qed.

    
Lemma not_env_impl_not_fv_source :
  forall Gamma x t A E, has_type_source Gamma t A E ->
               (x \notin (dom Gamma)) ->
               (x \notin (fv_source t)).
Proof.
  intros Gamma x t A E H HNot.
  induction H; simpls*.
  - apply notin_singleton_l.
    unfold not; intros; substs*.
    eapply binds_fresh_inv; eauto.
  - admit.
Admitted.

Lemma not_env_impl_not_fv_source_E :
  forall Gamma x t A E, has_type_source Gamma t A E ->
               (x \notin (dom Gamma)) ->
               (x \notin (fv_source E)).
Proof.
  intros Gamma x t A E H HNot.
  induction H; simpls*.
  - apply notin_singleton_l.
    unfold not; intros; substs*.
    eapply binds_fresh_inv; eauto.
  - admit.
Admitted.

  (*
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
    has_type_source (Gamma & y ~ A) (open_rec_source n (PFVar y) t) B E ->
    (exists E', E = open_rec_source n (PFVar y) E').
Proof.
  intros.
  inversion H; intros; subst.
  eexists. apply H0.
  eexists. apply H0.
  exists (PAnn (PLam t1) (Fun A0 B0)).
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
  exists (PAnn t' B).
  rewrite <- open_rec_source_term.
  reflexivity.
  now apply type_correct_source_terms' in H.   
Qed.

  
Definition tlam : forall L Gamma t A B, (forall x, x \notin L -> 
                                     has_type (Gamma & x ~ A) (open_source t (PFVar x)) B) ->
                               WFTyp A ->
                               has_type Gamma (PLam t) (Fun A B).
Proof.
  intros.
  unfold has_type.
  unfold has_type in H.
  pick_fresh y.
  (* at this point we should have not (In y (fv_source x0)), see admit below *)
  assert (HNot : y \notin L) by auto.
  pose (H y HNot).
  destruct e.
  assert (Ha : has_type_source (Gamma & y ~ A) (open_source t (PFVar y)) B x) by apply H1.
  apply typing_open_rec_source in H1.
  destruct H1 as [x0 H1].
  subst.
  assert (Ha2 : has_type_source (Gamma & y ~ A) (open_source t (PFVar y)) B
         (open_rec_source 0 (PFVar y) x0)) by apply Ha.
  exists (PAnn (PLam x0) (Fun A B)).  
  apply_fresh TyLam as z.
  rewrite <- concat_empty_r with (E := y ~ A) in Ha.
  rewrite concat_assoc in Ha.
  apply tsubst with (y := z) in Ha.
  rewrite concat_empty_r in Ha.
  rewrite subst_fresh_var in Ha.
  rewrite subst_fresh_var in Ha.
  apply Ha. (* apply not_env_impl_not_fv_source_E with (x := y) in Ha. *)
  (* this admit is related to the problem described above (in this same proof) *)
  admit.
  autos*.
  autos*.
  autos*.
Admitted.

Definition tapp : forall Gamma A B t1 t2,
              has_type Gamma t1 (Fun A B)  ->
              has_type Gamma t2 A  ->
              has_type Gamma (PApp t1 t2) B.
unfold has_type. intros. destruct H, H0.
exists (PApp x x0). eapply TyApp; eauto.
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
unfold has_type. intros. destruct H. exists (PAnn x B). eapply TySub; eauto.
Defined.  

Inductive Dir := Inf | Chk.

(* bidirection type-system (algorithmic): 

T |- e => t ~> E     (inference mode: infers the type of e producing target E) (use Inf)
T |- e <= t ~> E     (checking mode: checks the type of e producing target E) (use Chk)

Inspiration for the rules:

https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

*)

Inductive has_type_source_alg : env PTyp -> PExp -> Dir -> PTyp -> SExp -> Prop :=
  (* Inference rules *)
  | ATyVar : forall Gamma x ty, ok Gamma -> binds x ty Gamma -> WFTyp ty ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar x) 
  | ATyLit : forall Gamma x, ok Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                OrthoS A B ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E ->
                         has_type_source_alg Gamma (PAnn t1 A) Inf A E
  (* Checking rules *)
  | ATyLam : forall L Gamma t A B E, (forall x, x \notin L -> 
                                 has_type_source_alg (Gamma & x ~ A) (open_source t (PFVar x)) Chk B (open E (STFVar x))) -> WFTyp A ->
                           has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp B ->
               has_type_source_alg Gamma t Chk B (STApp C E).

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
Qed.

Lemma typing_wf_source_alg:
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp T.
Proof.
  intros Gamma t dir T E H.
  induction H; simpls*.
  - inverts* IHhas_type_source_alg1.
  - pick_fresh x; autos*.
Qed.
    
Lemma typing_weaken_alg : forall G E F t T d dir,
   has_type_source_alg (E & G) t dir T d -> 
   ok (E & F & G) ->
   has_type_source_alg (E & F & G) t dir T d.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; substs*.
  apply* ATyVar. apply* binds_weaken.
  apply_fresh* ATyLam as y. apply_ih_bind* H0.
Qed.  

Lemma typing_strengthen_alg : forall z U E F t T d c,
  z \notin (fv_source t) ->
  has_type_source_alg (E & z ~ U & F) t T d c ->
  has_type_source_alg (E & F) t T d c.
Proof.
  intros.
  remember (E & z ~ U & F).
  gen Heqe. gen F. 
  induction H0; intros; substs*; simpls*.
  - apply* ATyVar; simpls*; apply* binds_remove.
  - apply_fresh* ATyLam as x.
    apply_ih_bind* H1; apply* fv_source_distr2; simpls*.
Qed.

Lemma type_correct_alg_terms : forall Gamma E ty e dir, has_type_source_alg Gamma E dir ty e -> PTerm E.
Proof.
  intros; induction H; autos*.
Qed.


Lemma typing_alg_ok_env : forall Gamma E dir ty e, has_type_source_alg Gamma E dir ty e -> ok Gamma.
Proof.
  intros; induction H; autos*.
  pick_fresh x.
  assert (Ha: x \notin L) by autos*.
  apply H0 in Ha.
  apply ok_push_inv in Ha; now destruct Ha.
Qed.
  
(* Ignoring the generated expressions + smart constructors *)

Definition has_ty Gamma e d t := exists E, has_type_source_alg Gamma e d t E.

(*
Lemma tylam' : forall {Gamma t A B} L,
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
*)
  
Definition tylam : forall {Gamma t A B} L,
  (forall x, x \notin L -> 
        has_ty (Gamma & x ~ A) (open_source t (PFVar x)) Chk B) ->
  has_ty Gamma (PLam t) Chk (Fun A B).
Proof.
  intros.
  unfold has_ty in *.  
  pick_fresh y.
  assert (Ha : y \notin L) by autos*.
  apply H in Ha.
  inversion Ha.
  (* we will have the same problem present in the definition of "tlam" *)
Admitted.

Definition tyvar : forall Gamma x ty, ok Gamma -> binds x ty Gamma -> WFTyp ty ->
                                      has_ty Gamma (PFVar x) Inf ty.
intros.
unfold has_ty. exists (STFVar x). apply ATyVar; auto.
Defined.

Definition tylit : forall Gamma x, ok Gamma -> has_ty Gamma (PLit x) Inf PInt.
intros. unfold has_ty; eauto. Defined.

Definition tyapp : forall Gamma A B t1 t2,
              has_ty Gamma t1 Inf (Fun A B) ->
              has_ty Gamma t2 Chk A ->
              has_ty Gamma (PApp t1 t2) Inf B.
intros. unfold has_ty.
inversion H. inversion H0.
exists (STApp x x0).
eapply (ATyApp ). eauto. eauto.
Defined.

Definition tymerge : forall Gamma A B t1 t2,
                has_ty Gamma t1 Inf A ->
                has_ty Gamma t2 Inf B ->
                OrthoS A B ->
                has_ty Gamma (PMerge t1 t2) Inf (And A B).
intros.
inversion H. inversion H0.
unfold has_ty. exists (STPair x x0). apply ATyMerge; auto.
Defined.

Definition tyann : forall Gamma t1 A, has_ty Gamma t1 Chk A -> has_ty Gamma (PAnn t1 A) Inf A.
intros. inversion H. unfold has_ty. exists x. apply ATyAnn. auto.
Defined.

Lemma tysub : forall Gamma t A B, has_ty Gamma t Inf A -> Sub A B -> WFTyp B -> has_ty Gamma t Chk B.
intros.
unfold has_ty.
inversion H. inversion H0.
exists ((STApp x0 x)).
eapply ATySub; eauto.
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


Lemma typ_unique : forall Gamma e d t1 E1, has_type_source_alg Gamma e d t1 E1 -> forall t2 E2, has_type_source_alg Gamma e d t2 E2 -> almost_unique t1 t2 d.
Proof.
  introv H.
  induction H; intros; unfold almost_unique; simpls*.
  (* case Var *)
  - inverts* H2; eapply binds_func; eauto.
  (* case Lit *)
  - inverts* H0.
  (* case App *)
  - inverts* H1; apply IHhas_type_source_alg1 in H5; inverts* H5.
  (* Case Merge *)
  - inverts* H2; apply IHhas_type_source_alg1 in H5; substs*.
    apply IHhas_type_source_alg2 in H7; substs*.
  (* Case Ann *)
  - inverts* H0.
Qed.

(* Theorem 5. Type inference always gives unique types *)

Lemma typ_inf_unique : forall {Gamma e t1 E1}, has_type_source_alg Gamma e Inf t1 E1 -> forall {t2 E2}, has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros.
pose (@typ_unique _ _ _ _ _ H _ _ H0). simpl in a. auto.
Qed.

(* Theorem 6. *)
Lemma typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.
intros Gamma e d t E1 H.
induction H; intros; simpls*.
(* case PFVar *)
- inverts* H2. 
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
- inverts* H0.
(* Case Lam *)
- inverts* H2.
  fequals*.
  pick_fresh x.
  assert (Ha1: x \notin L0) by autos*.
  apply H7 in Ha1.
  apply H0 in Ha1.
  assert (HNotE : x \notin (fv E)) by autos*.
  assert (HNotF : x \notin (fv E0)) by autos*.
  eapply open_app_eq; eauto.
  autos*.
  inverts* H3. 
(* ATySub *)
- inverts* H2.
  inversion H.
  assert (A = A0).
  apply (typ_inf_unique H H3).
  subst.
  apply IHhas_type_source_alg in H3.
  subst.
  assert (WFTyp A0). now apply typing_wf_source_alg in H.
  assert (WFTyp B). assumption.
  assert (C = C0).
  apply (sub_coherent H2 H3 H0 H4).
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

Lemma open_rec_term_core :
  forall t j v i u, i <> j -> open_rec_source j (PFVar v) t = open_rec_source i (PFVar u) (open_rec_source j (PFVar v) t) ->
    t = open_rec_source i (PFVar u) t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.
  case_nat*. case_nat*. 
Qed.  

Lemma coercions_produce_terms :
  forall E A B, sub A B E -> STTerm E.
Proof.
  intros.
  induction H; simpls*.
  (* Case SInt *)
  - apply_fresh STTerm_Lam as x. cbv. case_nat*. 
  (* Case SFun *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_Lam as y; cbn.
    apply STTerm_App.
    repeat rewrite <- open_rec_term; assumption.
    apply STTerm_App.
    case_nat*.
    apply STTerm_Var.
    apply STTerm_App; [ repeat rewrite <- open_rec_term; auto | ].
    case_nat*.
    cbv.
    case_nat*.
  (* Case SAnd1 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    case_nat*.
    case_nat*.
    rewrite <- open_rec_term; auto.
  (* Case SAnd2 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
    case_nat*.
  (* Case SAnd3 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
    case_nat*.
Qed.

Hint Resolve coercions_produce_terms.

(* Subtyping rules produce type-correct coercions: Lemma 1 *)
Lemma type_correct_coercions :
  forall Gamma A B E, sub A B E ->
             ok Gamma -> 
             has_type_st Gamma E (STFun (|A|) (|B|)) .
Proof.
  intros.
  induction H; substs*.
  (* Case SInt *)
  - apply_fresh STTyLam as x; cbn; case_nat*.
  (* Case SFun *)
  - apply_fresh STTyLam as x; cbn.
    apply_fresh STTyLam as y; cbn.
    apply STTyApp with (A := (| o2 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend; autos*.
    autos*.
    rewrite <- open_rec_term; autos*.
    eapply STTyApp.
    case_nat*; simpls*.
    apply STTyApp with (A := (| o3 |)).
    repeat rewrite <- open_rec_term; autos*.
    repeat apply typing_weaken_extend; autos*.
    case_nat*.
    simpls*.
    case_nat*.
  (* Case SAnd1 *)
  - apply_fresh STTyLam as x; cbn.
    apply STTyPair.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub1.
    autos*.
    autos*.
    case_nat*.
    case_nat*.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub2.
    autos*.
    autos*.
    autos*.
  (* Case SAnd2 *)
  - apply_fresh STTyLam as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    autos*.
    autos*.
    case_nat*.
  (* SAnd3 *)
  - apply_fresh STTyLam as x; cbn.
    eapply STTyApp.
    rewrite <- open_rec_term.
    apply typing_weaken_extend.
    apply IHsub.
    autos*.
    autos*.
    case_nat*.
Qed.

  
(* Type preservation: Theorem 1 *)
Lemma type_preservation :
  forall x ty dir E (Gamma : env PTyp) (H : has_type_source_alg Gamma x dir ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof.
  intros; induction H; simpls*.
  (* TyVar *)
  - apply STTyVar.
    apply* ok_map.
    apply* binds_map.
  (* TyLit *)
  - apply STTyLit; apply* ok_map.
  (* TyLam *)
  - apply_fresh STTyLam as x.
    unfold open; simpl.
    assert (Ha : x \notin L) by autos*.
    apply H0 in Ha. 
    unfold open in Ha; unfold conv_context in Ha.
    rewrite map_push in Ha.
    apply Ha.
  (* ATySub *)
  - apply STTyApp with (|A|).
    apply type_correct_coercions.
    assumption.
    now apply typing_ok_env in IHhas_type_source_alg.
    assumption.
Qed.
    
(* Completeness *)

Lemma erasure_open : forall t1 n t0 x,
  x \notin (fv_source t0) ->
  x \notin (fv_source t1) ->                     
  erase (open_rec_source n (PFVar x) t1) = open_rec_source n (PFVar x) t0 ->
  erase t1 = t0.
Proof.
  induction t1; intros; simpls*; destruct t0; inverts* H1; simpl in *;
  (repeat case_nat*); try fequals*.
  (* PFVar *)
  - inverts* H3; apply notin_singleton in H0; tryfalse*.
  (* PBVar *)
  - simpls*; inverts* H3; apply notin_singleton in H; tryfalse*.
Qed.

(* Theorem 4 *)
Lemma typ_complete : forall Gamma e t e',
  has_type_source Gamma e t e' -> (has_ty Gamma e' Inf t) /\ erase e' = e.
intros Gamma e t e' H.
induction H; intros; split; autos*.
(* Case TyVar *)
apply tyvar; auto.
(* Case TyLit *)
apply tylit; auto.
(* Case TyLam *)
apply tyann.
apply (@tylam _ _ _ _ (((L \u (dom Gamma)) \u (fv_source t)) \u (fv_source t1))).
intros.
assert (d: x \notin L) by autos*.
pose (H0 x d). destruct a. (*destruct H2. destruct x0.*)
eapply tysub. eauto. apply reflex. inversion H3.
now apply typing_wf_source_alg in H5.
(* erasure of Lam *)
pick_fresh x.
assert (has_type_source (Gamma & x ~ A) (open_source t (PFVar x)) B
                                      (open_source t1 (PFVar x))). 
assert (d: x \notin L) by autos*.
apply (H x d).
assert ( has_ty (Gamma & x ~ A) (open_source t1 (PFVar x)) Inf B /\
         erase (open_source t1 (PFVar x)) = open_source t (PFVar x)).
assert (d: x \notin L) by autos*.
apply (H0 x d). clear H H0. destruct H3.
unfold open_source in H0, H, H1. inversion H. clear H.
assert (Hxt0 : x \notin (fv_source t)) by autos*.
assert (Hxt1 : x \notin (fv_source t1)) by autos*.
lets* Ha : (erasure_open _ _ _ Hxt0 Hxt1 H0).
simpls*; rewrite* Ha.
(* Case App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
eapply tyapp.
inversion H1.
unfold has_ty. exists x. eauto.
eapply tysub. apply H3. apply reflex. now apply typing_wf_source in H0.
(* erasure of App *)
destruct IHhas_type_source1. destruct IHhas_type_source2.
simpl.
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
apply tyann. eapply tysub; eauto. 
Qed.

Lemma erase_open : forall t n e,
                     erase (open_rec_source n e t) = open_rec_source n (erase e) (erase t).
Proof.
  induction t; intros; simpls*; try case_nat*; fequals*.
Qed.

(* Theorem 3 *)
Lemma typ_sound : forall e d A Gamma, has_ty Gamma e d A -> has_type Gamma (erase e) A.
Proof.
  intros; inversion H; clear H.
  induction H0; simpls*.
  (* PFVar *)
  - apply tvar; auto.
  (* PFLit *)
  - apply tlit; auto.
  (* App *)
  - eapply tapp; eauto.
  (* Merge *)
  - eapply tmerge; eauto.
  (* Lam *)
  - apply_fresh tlam as x.
    assert (d: x \notin L) by autos*.
    intros. pose (H0 x d).
    unfold open_source in h. unfold open_source.
    rewrite (erase_open t 0 (PFVar x)) in h. auto.
    auto.
  (* Sub *)
  - eapply tsub; eauto.
Qed.

(**** Bi-directional type-system (non-elaborating) ****)

Inductive bidityping : env PTyp -> PExp -> Dir -> PTyp -> Prop :=
  | ATyVar' : forall Gamma x ty,
                ok Gamma ->
                binds x ty Gamma ->
                WFTyp ty ->
                bidityping Gamma (PFVar x) Inf ty
  | ATyLit' : forall Gamma (x : nat),
                ok Gamma ->
                bidityping Gamma (PLit x) Inf PInt
  | ATyApp' : forall Gamma (A B : PTyp) (t1 t2 : PExp),
                bidityping Gamma t1 Inf (Fun A B) ->
                bidityping Gamma t2 Chk A ->
                bidityping Gamma (PApp t1 t2) Inf B
  | ATyMerge' : forall Gamma (A B : PTyp) (t1 t2 : PExp),
                  bidityping Gamma t1 Inf A ->
                  bidityping Gamma t2 Inf B ->
                  OrthoS A B ->
                  bidityping Gamma (PMerge t1 t2) Inf (And A B)
  | ATyAnnCT' : forall Gamma (t1 : PExp) (A : PTyp),
                  bidityping Gamma t1 Chk A ->
                  bidityping Gamma (PAnn t1 A) Inf A
  | ATyLam' : forall L Gamma 
                (t : PExp) (A B : PTyp),
                (forall x, x \notin L ->
                      bidityping (Gamma & x ~ A) (open_source t (PFVar x)) Chk B) ->
                WFTyp A ->
                bidityping Gamma (PLam t) Chk (Fun A B)
  | ATySub' : forall Gamma (t : PExp) 
                (A B : PTyp) C,
                bidityping Gamma t Inf A ->
                sub A B C ->
                WFTyp B ->
                bidityping Gamma t Chk B.

Hint Constructors bidityping.

(** Soundness and Completeness wrt to the elaborating biditypecheker **)

Theorem has_type_source_alg_rename :
  forall L Gamma A B t1 c m y,
    has_type_source_alg (Gamma & y ~ A) (open_source t1 (PFVar y)) B m 
                        (open c (STFVar y)) ->
    (forall x, x \notin L ->
          has_type_source_alg (Gamma & x ~ A) (open_source t1 (PFVar x)) B m
                              (open c (STFVar x))).
Proof.
  intros.
  (* subst_typ_source_intro *)
Admitted.

Theorem soundness : forall Gamma e A m, bidityping Gamma e A m -> has_ty Gamma e A m.
Proof.
  intros Gamma e A m H; unfold has_ty.
  induction H; destruct_conjs; eauto.
  - pick_fresh x.
    assert (Ha : x \notin L) by autos*.
    destruct (H0 _ Ha) as [c H2].
    exists (STLam c).
    apply_fresh ATyLam as z; auto.
    apply has_type_source_alg_rename with (L := L) (y := x).
    admit. (* missing the good old renaming lemma... *)
    autos*.
Admitted.
    
Theorem completeness :
  forall Gamma A m d e, has_type_source_alg Gamma e A m d -> bidityping Gamma e A m.
Proof. intros Gamma A m d e H; induction H; eauto. Qed.

Hint Resolve soundness completeness.

(** Some necessary properties about bidityping, which are lifted from 
    the elaborated version **)

Theorem bityping_ok : forall Gamma t A m, bidityping Gamma t m A -> ok Gamma.
Proof.
  intros; apply soundness in H as [c H]; eapply typing_alg_ok_env; eauto.
Qed.
  
Theorem bityping_wf : forall Gamma t A m, bidityping Gamma t m A -> WFTyp A.
Proof.
  intros; apply soundness in H as [c H]; eapply typing_wf_source_alg; eauto.
Qed.

Theorem bityping_term : forall Gamma e A m, bidityping Gamma e m A -> PTerm e.
Proof.
  intros; apply soundness in H as [c H]; eapply type_correct_alg_terms; eauto.
Qed.

Theorem bityping_weaken:
  forall G E F t T dir, bidityping (E & G) t dir T ->
                   ok (E & F & G) ->
                   bidityping (E & F & G) t dir T.
Proof.
  intros; apply soundness in H as [c H].
  lets* Ha : typing_weaken_alg H.
Qed.

Theorem bityping_strengthen:
  forall z U E F e dir A,
    z \notin (fv_source e) ->
    bidityping (E & z ~ U & F) e dir A ->
    bidityping (E & F) e dir A.
Proof.
  intros z U E F e dir A H1 H2; apply soundness in H2 as [c H2].
  lets* Ha : typing_strengthen_alg H1 H2.
Qed.

Hint Resolve bityping_ok bityping_wf bityping_term bityping_weaken.

(** defining body on bityping. (i.e. used for subject reduction) **)

Definition body_bityping Gamma t A B m :=
  exists L, forall x, x \notin L ->
            bidityping (Gamma & x ~ A) (open_source t (PFVar x)) m B.

Hint Unfold body_bityping.

Lemma abs_to_body_bityping : forall A B e Gamma m, 
  bidityping Gamma (PLam e) m (Fun A B) -> body_bityping Gamma e A B m.
Proof. intros; inversion H; subst; eauto; inversion H0. Qed.

Lemma bityping_subst : forall Gamma A B e u m x,
                         binds x B Gamma ->
                         bidityping Gamma e m A ->
                         bidityping Gamma u Inf B ->
                         bidityping Gamma (subst_source x u e) m A.
Proof.
  intros Gamma A B e u m x HIn H1 H2.
  induction H1; simpl; eauto.
  - case_var*.
    assert (Ha : B = ty) by (eapply binds_func; eauto). now subst.
  - apply_fresh ATyLam' as x; auto.
    rewrite subst_source_open_var; eauto.
    apply H0; autos*.
    rewrite <- concat_empty_r with (E := (Gamma & y ~ A)).
    apply bityping_weaken; rewrite concat_empty_r; autos*.
Qed.

Lemma open_body_bityping :
  forall e A B u Gamma m, body_bityping Gamma e A B m -> bidityping Gamma u Inf A ->
                 bidityping Gamma (open_source e u) m B.
Proof.
  intros e A B u Gamma m H1 H2; destruct H1. pick_fresh y.
  assert (Ha : y \notin x) by autos*; apply H in Ha.
  rewrite <- concat_empty_r with (E := Gamma).
  eapply bityping_strengthen with (z := y) (U := A).
  apply fv_source_distr2; autos*.
  rewrite concat_empty_r.
  rewrite subst_source_intro with (x := y); autos*.
  apply bityping_subst with (B := A); autos*.
  rewrite <- concat_empty_r with (E := (Gamma & y ~ A)).
  apply bityping_weaken; rewrite concat_empty_r; autos*.
Qed.

Lemma elaboration_regular :
  forall Gamma e A m E, has_type_source_alg Gamma e m A E -> STTerm E.
Proof.
  introv Typ. apply type_preservation in Typ. apply* typing_gives_terms.
Qed.

Hint Resolve elaboration_regular.

Definition body_type_source Gamma e1 A B m E1 :=
  exists L, forall x : var, x \notin L ->
                  has_type_source_alg (Gamma & x ~ A) (open_source e1 (PFVar x)) m B
                                      (open E1 (STFVar x)).

Hint Unfold body_type_source.

Lemma abs_to_body_type_source :
  forall A B e c Gamma m, has_type_source_alg Gamma (PLam e) m (Fun A B) (STLam c) ->
                 body_type_source Gamma e A B m c.
Proof. intros; inversion H; subst; eauto. Qed.

Lemma sub_fv_empty : forall A B c, sub A B c -> fv c = \{}.
Proof.
  introv Hsub.
  induction* Hsub; simpls*;
  try rewrite IHHsub; try rewrite IHHsub1; try rewrite IHHsub2;
  now repeat rewrite union_empty_l. 
Qed.

Lemma has_type_source_subst :
  forall Gamma A B e u x m E1 E2,
    binds x B Gamma ->
    has_type_source_alg Gamma e m A E1 ->
    has_type_source_alg Gamma u Inf B E2 ->
    has_type_source_alg Gamma (subst_source x u e) m A (subst x E2 E1).
Proof.
  introv HIn H1 H2.
  induction H1; simpl; eauto.
  - case_var*.
    assert (Ha : B = ty) by (eapply binds_func; eauto). now subst.
  - apply_fresh ATyLam as x; auto.
    rewrite subst_source_open_var; eauto 3.
    rewrite subst_open_var; eauto 3.
    apply* H0.
    rewrite <- concat_empty_r with (E := (Gamma & y ~ A)).
    apply typing_weaken_alg; rewrite concat_empty_r; autos*.
  - forwards* Ha : IHhas_type_source_alg HIn H2.
    apply* ATySub; rewrite* subst_fresh.
    forwards* Ha1 : sub_fv_empty H; rewrite* Ha1. 
Qed.

Lemma open_body_type :
  forall Gamma A B e1 e2 E1 E2 m,
    body_type_source Gamma e1 A B m E1 -> 
    has_type_source_alg Gamma e2 Inf A E2 ->
    has_type_source_alg Gamma (open_source e1 e2) m B (open E1 E2).
Proof.
  introv H1 H2; destruct H1. pick_fresh y.
  assert (Ha : y \notin x) by autos*; apply H in Ha.
  rewrite <- concat_empty_r with (E := Gamma).
  eapply typing_strengthen_alg with (z := y) (U := A).
  apply fv_source_distr2; autos*.
  rewrite concat_empty_r.
  rewrite subst_source_intro with (x := y); autos*.
  rewrite subst_intro with (x := y); autos*.
  apply has_type_source_subst with (B := A); autos*.
  rewrite <- concat_empty_r with (E := (Gamma & y ~ A)).
  apply typing_weaken_alg; rewrite concat_empty_r; autos*.
Qed.


