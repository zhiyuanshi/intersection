Require Import STLCNew LibLN.
Require Import Coq.Program.Tactics.

(**** ****)

Inductive STValue : SExp -> Prop :=
  | STValue_Lam :
      forall t1, STTerm (STLam t1) -> STValue (STLam t1)
  | STValue_Lit : forall n, STValue (STLit n)
  | STValue_Unit : STValue STUnit
  | STValue_Pair : forall v1 v2, STValue v1 -> STValue v2 -> STValue (STPair v1 v2).

Definition body (t : SExp) :=
  exists L, forall (x : var), x \notin L -> STTerm (open t (STFVar x)).

(* ********************************************************************** *)
(** ** Terms are stable through substitutions *)

(** Terms are stable by substitution *)

Lemma subst_term : forall t z u,
  STTerm u -> STTerm t -> STTerm (subst z u t).
Proof.
  induction 2; simpls*.
  case_var*.
  apply_fresh STTerm_Lam as y. rewrite* subst_open_var.
Qed.

Hint Resolve subst_term.

(* ********************************************************************** *)
(** ** Terms are stable through open *)

(** Conversion from locally closed abstractions and bodies *)

Lemma term_abs_to_body : forall t1, 
  STTerm (STLam t1) -> body t1.
Proof.
  intros. unfold body. inversion* H.
Qed.

Lemma body_to_term_abs : forall t1, 
  body t1 -> STTerm (STLam t1).
Proof.
  intros. inversion* H.
Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

(** ** Opening a body with a term gives a term *)

Lemma open_term : forall t u,
  body t -> STTerm u -> STTerm (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y. rewrite* (@subst_intro y).
Qed.

Hint Resolve open_term.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** A typing relation holds only if the environment has no
   duplicated keys and the pre-term is locally-closed. *)

Lemma typing_regular : forall E e T,
  has_type_st E e T -> ok E /\ STTerm e.
Proof.
  introv H.
  split; induction H; autos*.
  Unshelve. apply 0.
  (* pick_fresh y. forward~ (H0 y) as K. inversions* K. *)
Qed.

(** The value predicate only holds on locally-closed terms. *)

Lemma value_regular : forall e,
  STValue e -> STTerm e.
Proof.
  induction 1; autos*.
Qed.

Hint Resolve value_regular.

Definition relation := SExp -> SExp -> Prop.

(** Call-by-value **)
Inductive STred : relation :=
  | red_beta : forall t1 t2,
      STTerm (STLam t1) ->
      STValue t2 ->
      STred (STApp (STLam t1) t2) (t1 ^^ t2)
  | red_app_1 : forall t1 t1' t2,
      STTerm t2 ->
      STred t1 t1' ->
      STred (STApp t1 t2) (STApp t1' t2)
  | red_app_2 : forall t1 t2 t2',
      STValue t1 ->
      STred t2 t2' ->
      STred (STApp t1 t2) (STApp t1 t2')
  | red_pair_1 : forall t1 t1' t2,
      STTerm t2 ->
      STred t1 t1' ->
      STred (STPair t1 t2) (STPair t1' t2)
  | red_pair_2 : forall t1 t2 t2',
      STValue t1 ->
      STred t2 t2' ->
      STred (STPair t1 t2) (STPair t1 t2')
  | red_proj1_1 : forall t1 t1',
      STred t1 t1' ->
      STred (STProj1 t1) (STProj1 t1')
  | red_proj1_2 : forall t1 t2,
      STValue (STPair t1 t2) ->
      STred (STProj1 (STPair t1 t2)) t1
  | red_proj2_1 : forall t1 t1',
      STred t1 t1' ->
      STred (STProj2 t1) (STProj2 t1')
  | red_proj2_2 : forall t1 t2,
      STValue (STPair t1 t2) ->
      STred (STProj2 (STPair t1 t2)) t2.

(** Full reduction **)
Inductive fullred : relation :=
  | fullred_beta : forall t1 t2,
      body t1 ->
      STTerm t2 ->           
      fullred (STApp (STLam t1) t2) (t1 ^^ t2)
  | fullred_abs : forall L t1 t1', 
      (forall x, x \notin L -> fullred (open t1 (STFVar x)) (open t1' (STFVar x))) ->
      fullred (STLam t1) (STLam t1')
  | fullred_app_1 : forall t1 t1' t2,
      STTerm t2 ->
      fullred t1 t1' ->
      fullred (STApp t1 t2) (STApp t1' t2)
  | fullred_app_2 : forall t1 t2 t2',
      STTerm t1 ->
      fullred t2 t2' ->
      fullred (STApp t1 t2) (STApp t1 t2')
  | fullred_pair_1 : forall t1 t1' t2,
      STTerm t2 ->
      fullred t1 t1' ->
      fullred (STPair t1 t2) (STPair t1' t2)
  | fullred_pair_2 : forall t1 t2 t2',
      STTerm t1 ->
      fullred t2 t2' ->
      fullred (STPair t1 t2) (STPair t1 t2')
  | fullred_proj1_1 : forall t1 t1',
      fullred t1 t1' ->
      fullred (STProj1 t1) (STProj1 t1')
  | fullred_proj1_2 : forall t1 t2,
      STTerm (STPair t1 t2) ->
      fullred (STProj1 (STPair t1 t2)) t1
  | fullred_proj2_1 : forall t1 t1',
      fullred t1 t1' ->
      fullred (STProj2 t1) (STProj2 t1')
  | fullred_proj2_2 : forall t1 t2,
      STTerm (STPair t1 t2) ->
      fullred (STProj2 (STPair t1 t2)) t2.

Hint Constructors STred fullred STTerm.

Notation "t -->> t'" := (fullred t t') (at level 68).

(* ********************************************************************** *)
(** * Infrastructure *)

Lemma fullred_regular : forall e e',
  fullred e e' -> STTerm e /\ STTerm e'.
Proof.
  induction 1; destruct_conjs; split; eauto; try inverts* H;
  apply_fresh STTerm_Lam as x; forwards* H2 : H0 x.
Qed.

Hint Extern 1 (STTerm ?t) =>
  match goal with
  | H: fullred t _ |- _ => apply (proj1 (fullred_regular H))
  | H: fullred _ t |- _ => apply (proj2 (fullred_regular H))
  end.

Hint Constructors has_type_st STred STValue.

(* ********************************************************************** *)
(** * Proofs *)

(** Call-by-value STLC with Pairs: Safety and Progress **)

Definition preservation_statement_stlc := forall E t t' T,
  has_type_st E t T ->
  STred t t' ->
  has_type_st E t' T.

Definition progress_statement_stlc := forall t T, 
  has_type_st empty t T -> STValue t \/ exists t', STred t t'.

Lemma preservation_result_stlc : preservation_statement_stlc.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inverts* Red.
  inversions Typ1. pick_fresh x. rewrite* (@subst_intro x).
    apply_empty* typing_subst.
  inverts* Typ.
  inverts* Typ.
Qed.

Lemma progress_result_stlc : progress_statement_stlc.
Proof.
  introv Typ. gen_eq E: (empty:ctx). lets Typ': Typ.
  induction Typ; intros; substs*.
  - false* binds_empty_inv.
  - right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
    inverts* Typ1; inverts* Val1.
    + exists* (STApp t1 t2'). 
    + exists* (STApp t1' t2).
  - destruct~ IHTyp1 as [Val1 | [t1' Red1]];
    destruct~ IHTyp2 as [Val2 | [t2' Red2]]; autos*.
  - destruct~ IHTyp as [Val | [t' Red]]; autos*.
    right.
    inverts* Typ; [ false* binds_empty_inv | | | ]; inverts* Val.
  - destruct~ IHTyp as [Val | [t' Red]]; autos*.
    right.
    inverts* Typ; [ false* binds_empty_inv | | | ]; inverts* Val.
Qed.

Lemma preservation_for_full_reduction : forall E t t' T,
  has_type_st E t T ->
  t -->> t' ->
  has_type_st E t' T.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red; eauto.
  apply_fresh* STTyLam as x.
  inversions Typ1. pick_fresh x.
    rewrite* (@subst_intro x). apply_empty* typing_subst.
  inverts* Typ.
  inverts* Typ.
Qed.


(* ********************************************************************** *)
(** Definition of the reflexive-symmetric-transitive closure of a relation *)

Inductive equiv_ (R : relation) : relation :=
  | equiv_refl : forall t,
      STTerm t ->
      equiv_ R t t
  | equiv_sym: forall t t',
      equiv_ R t t' ->
      equiv_ R t' t
  | equiv_trans : forall t2 t1 t3, 
      equiv_ R t1 t2 -> equiv_ R t2 t3 -> equiv_ R t1 t3
  | equiv_step : forall t t',
      R t t' -> equiv_ R t t'.

Notation "R 'equiv'" := (equiv_ R) (at level 69).

(* ********************************************************************** *)
(** Definition of the reflexive-transitive closure of a relation *)

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      STTerm t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

(* ********************************************************************** *)
(** Definition of confluence and of the Church-Rosser property
 (Our goal is to prove the Church-Rosser Property for beta relation) *)

Definition confluence (R : relation) := 
  forall M S T, R M S -> R M T -> 
  exists P, R S P /\ R T P. 

Definition church_rosser (R : relation) :=
  forall t1 t2, (R equiv) t1 t2 -> 
  exists t, (R star) t1 t /\ (R star) t2 t.


