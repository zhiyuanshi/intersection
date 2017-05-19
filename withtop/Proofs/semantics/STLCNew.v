
Set Implicit Arguments.

Require Import LibLN.
Require Import LibTactics.

Inductive STyp :=
  | STUnitT : STyp
  | STInt : STyp
  | STFun : STyp -> STyp -> STyp
  | STTuple : STyp -> STyp -> STyp.

Inductive SExp :=
  | STFVar  : var -> SExp
  | STBVar  : nat -> SExp
  | STUnit  : SExp
  | STLit   : nat -> SExp
  | STLam  : SExp -> SExp
  | STApp   : SExp -> SExp -> SExp
  | STPair  : SExp -> SExp -> SExp
  | STProj1 : SExp -> SExp
  | STProj2 : SExp -> SExp.

(** Target language **)
Fixpoint fv (sExp : SExp) : vars :=
  match sExp with
    | STFVar v => singleton v
    | STBVar _ => \{}
    | STUnit => \{}
    | STLit _ => \{}
    | STLam t => fv t
    | STApp t1 t2 => (fv t1) \u (fv t2)
    | STPair t1 t2 => (fv t1) \u (fv t2)
    | STProj1 t => fv t
    | STProj2 t => fv t
  end.

Fixpoint open_rec (k : nat) (u : SExp) (t : SExp) {struct t} : SExp :=
  match t with
  | STBVar i => If k = i then u else (STBVar i)
  | STFVar x => STFVar x
  | STUnit => STUnit
  | STLit x => STLit x
  | STLam t1 => STLam (open_rec (S k) u t1)    
  | STApp t1 t2 => STApp (open_rec k u t1) (open_rec k u t2)
  | STPair t1 t2 => STPair (open_rec k u t1) (open_rec k u t2)
  | STProj1 t => STProj1 (open_rec k u t)
  | STProj2 t => STProj2 (open_rec k u t)
  end.

Definition open (t : SExp) u := open_rec 0 u t.

(* Notation "[ z ~> u ] t" := (subst z u t) (at level 68). *)
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^ x" := (open t (STFVar var x)).
Notation "t ^^ u" := (open t u) (at level 67).

Lemma fv_distr :
  forall t1 t2 x n, x \in (fv (open_rec n t2 t1)) ->
               x \in (union (fv t1) (fv t2)).
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

Inductive STTerm : SExp -> Prop :=
  | STTerm_Var : forall x,
      STTerm (STFVar x)
  | STTerm_Unit : STTerm STUnit
  | STTerm_Lit : forall n,
      STTerm (STLit n)
  | STTerm_Lam : forall L t1,
      (forall x, x \notin L -> STTerm (open t1 (STFVar x))) ->
      STTerm (STLam t1)
  | STTerm_App : forall t1 t2,
      STTerm t1 -> 
      STTerm t2 -> 
      STTerm (STApp t1 t2)
  | STTerm_Pair : forall t1 t2,
      STTerm t1 ->
      STTerm t2 ->
      STTerm (STPair t1 t2)
  | STTerm_Proj1 : forall t,
      STTerm t ->
      STTerm (STProj1 t)
  | STTerm_Proj2 : forall t,
      STTerm t ->
      STTerm (STProj2 t).

Hint Constructors STTerm.

(* Tactics dealing with fresh variables, taken from STLC_Tutorial *)

Definition ctx := env STyp.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  (*let C := gather_vars_with (fun (x : context PTyp) => dom x) in *)
  let D := gather_vars_with (fun (x : ctx) => dom x) in
  (*let E := gather_vars_with (fun x : PExp => fv_source x) in *)
  let F := gather_vars_with (fun (x : SExp) => fv x) in
  constr:(A \u (B \u (D \u F))).

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

Lemma open_rec_term_core :forall t j v i u, i <> j ->
  { j ~> v }t = { i ~> u }({ j ~> v }t) -> t = { i ~> u }t.
Proof.
  induction t; introv Neq Equ; simpls; inversion* Equ; fequals*.
  case_nat*. case_nat*.  
Qed.

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term : forall t u,
  STTerm  t -> forall k, t =  { k ~> u }t.
Proof.
  induction 1; intros; simpls; fequals*;
  pick_fresh x; apply* (@open_rec_term_core t1 0 (STFVar x)).
Qed.

Hint Resolve open_rec_term.

Lemma open_app_eq : forall x E n F,
  (x \notin (fv E)) ->
  (x \notin (fv F)) ->
  (open_rec n (STFVar x) E) = (open_rec n (STFVar x) F) ->
  E = F.
Proof.
  intros x E.
  induction E; introv HNotE HNotF HEqOpen; simpls;
  try (induction F; inverts* HEqOpen; simpls; [ case_nat* | fequals* ]).
  - induction F; inverts* HEqOpen.
    case_nat*.
    assert (Ha1 : x = v) by fequals*; substs.
    assert (Ha2 : v <> v) by autos*; tryfalse.
  - induction F; case_nat*; inverts* HEqOpen; try now case_nat*.
    assert (Ha : v <> v) by autos*; tryfalse.
  - induction F; inverts* HEqOpen; case_nat*.
  - induction F; inverts* HEqOpen; case_nat*.
Qed.

Lemma fv_distr2 : forall z n t1 t2,
                    z \notin (fv t1) ->
                    z \notin (fv t2) ->
                    z \notin (fv (open_rec n t2 t1)).
Proof.
  introv H1 H2; gen n t2; induction t1; intros; simpls*; case_nat*.
Qed.

(* Typing rules *)

(* Typing rules of STLC, inspired by STLC_Tutorial *)

Inductive has_type_st : ctx -> SExp -> STyp -> Prop :=
  | STTyVar : forall Gamma x ty,
                ok Gamma -> binds x ty Gamma -> has_type_st Gamma (STFVar x) ty
  | STTyUnit : forall Gamma, ok Gamma -> has_type_st Gamma STUnit STUnitT
  | STTyLit : forall Gamma n, ok Gamma -> has_type_st Gamma (STLit n) STInt       
  | STTyLam : forall L Gamma t A B,
                (forall x, x \notin L -> 
                      has_type_st (Gamma & x ~ A) (open t (STFVar x)) B) ->
                has_type_st Gamma (STLam t) (STFun A B)
  | STTyApp : forall Gamma A B t1 t2, has_type_st Gamma t1 (STFun A B) ->
                             has_type_st Gamma t2 A -> has_type_st Gamma (STApp t1 t2) B
  | STTyPair : forall Gamma A B t1 t2, has_type_st Gamma t1 A ->
                              has_type_st Gamma t2 B ->
                              has_type_st Gamma (STPair t1 t2) (STTuple A B)
  | STTyProj1 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj1 t) A
  | STTyProj2 : forall Gamma t A B, has_type_st Gamma t (STTuple A B) ->
                           has_type_st Gamma (STProj2 t) B.

Hint Constructors has_type_st.

(* Typing lemmas *)

Lemma typing_ok_env : forall Gamma E ty, has_type_st Gamma E ty -> ok Gamma.
Proof.
  introv H1; induction H1; simpls*;
  pick_fresh x; assert (Ha : x \notin L) by autos*; lets* H1 : H0 x.
Qed.
  
Lemma typing_gives_terms : forall Gamma E ty, has_type_st Gamma E ty -> STTerm E.
Proof. introv H1; induction H1; simpls*. Qed.

Hint Resolve typing_ok_env typing_gives_terms.

Lemma typing_weaken : forall G E F t T,
   has_type_st (E & G) t T -> 
   ok (E & F & G) ->
   has_type_st (E & F & G) t T.
Proof.
  introv Typ. gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; substs*.
  apply* STTyVar. apply* binds_weaken.
  apply_fresh* STTyLam as y. apply_ih_bind* H0.
Qed.

Lemma typing_strengthen : forall z U E F t T,
  z \notin (fv t) ->
  has_type_st (E & z ~ U & F) t T ->
  has_type_st (E & F) t T.
Proof.
  intros.
  remember (E & z ~ U & F).
  gen Heqe. gen F. 
  induction H0; intros; substs*; simpls*.
  - apply* STTyVar; simpls*; apply* binds_remove.
  - apply_fresh* STTyLam as x.
    apply_ih_bind* H1; apply* fv_distr2; simpls*.
Qed.

Lemma typing_weaken_extend : forall x E t T A,
   has_type_st E t T -> 
   x \notin (dom E) ->
   has_type_st (E & x ~ A) t T.
Proof.
  introv Typ H.
  rewrite <- concat_empty_r with (E := x ~ A).
  rewrite concat_assoc.
  apply typing_weaken.
  rewrite* concat_empty_r.
  rewrite* concat_empty_r.
Qed.


(***** Substitution *****)

Fixpoint subst (z : var) (u : SExp) (t : SExp) {struct t} : SExp :=
  match t with
    | STBVar i     => STBVar i
    | STFVar x     => If x = z then u else (STFVar x)
    | STLit i      => STLit i
    | STLam t1     => STLam (subst z u t1)
    | STApp t1 t2  => STApp (subst z u t1) (subst z u t2)
    | STPair t1 t2 => STPair (subst z u t1) (subst z u t2)
    | STProj1 t    => STProj1 (subst z u t)
    | STProj2 t    => STProj2 (subst z u t)
    | STUnit       => STUnit
  end.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t ->  subst x u t = t.
Proof. intros. induction t; simpls; fequals*. case_var*. Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, STTerm u -> 
  subst x u (t1 ^^ t2) = (subst x u t1) ^^ (subst x u t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; fequals*.
  case_var*. case_nat*.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u t, y <> x -> STTerm u ->
  (subst x u t) ^^ (STFVar y) = subst x u (t ^^ (STFVar y)).
Proof. introv Neq Wu. rewrite* subst_open. simpl. case_var*. Qed.

(** Opening up an abstraction of body [t] with a term [u] is the same as opening
  up the abstraction with a fresh name [x] and then substituting [u] for [x]. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> STTerm u ->
  t ^^ u = subst x u (t ^^ (STFVar x)).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

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
(** ** More properties of typing *)

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

Lemma typing_subst : forall F E t T z u U,
  has_type_st (E & z ~ U & F) t T ->
  has_type_st E u U ->
  has_type_st (E & F) (subst z u t) T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpls*.
  - case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* STTyVar.
  - apply_fresh STTyLam as y.
    rewrite* subst_open_var. apply_ih_bind* H0.
Qed.
