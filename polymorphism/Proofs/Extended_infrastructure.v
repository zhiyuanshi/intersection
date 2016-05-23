Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.EqualitiesFacts.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended_definitions.

Module Infrastructure
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).


Module Definitions := Definitions(VarTyp)(set).
Export Definitions.

(** ok properties **)

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
  change (map (fun p : var * TyEnvSource => (fst p, ptyp2styp_tyenv (snd p))) E) with (mapctx ptyp2styp_tyenv E).
  erewrite <- dom_map_id.
  assumption.
Qed.

Lemma in_persists :
  forall x ty Gamma, List.In (x, ty) Gamma -> List.In (x, ptyp2styp_tyenv ty) (∥ Gamma ∥).
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

Hint Resolve ok_map in_persists.

Module MDec := PairDecidableType(VarTypDecidable)(PTypDecidable).

Lemma ok_unique_type : forall {T : Type} (Gamma: context T) x A B,
  ok Gamma ->
  List.In (x, A) Gamma /\ List.In (x, B) Gamma ->
  sumbool (A = B) (not (A = B)) ->
  A = B.
Proof.
  intros.
  
  induction H.
  inversion H0.
  inversion H.

  assert (Ha := VarTyp.eq_dec x v).
  inversion Ha; inversion H1; subst.
  - reflexivity.
  - inversion H0.
    inversion H3; inversion H5.
    + inversion H6; inversion H7; subst; assumption.    
    + rewrite app_nil_l in H7; apply list_impl_m in H7; contradiction.
    + rewrite app_nil_l in H6; apply list_impl_m in H6; contradiction.
    + rewrite app_nil_l in H6; apply list_impl_m in H6; contradiction.
  - reflexivity.
  - inversion H0; clear H0.
    inversion H5; inversion H6.
    inversion H0; inversion H7; subst.
    exfalso; now apply H3.
    inversion H0; exfalso; now apply H3.
    inversion H7; exfalso; now apply H3.
    apply IHok.
    rewrite app_nil_l in *; split; auto.
Qed. 

(** WFEnv properties **)

Lemma wfenv_to_ok : forall Gamma, WFEnv Gamma -> ok Gamma.
Proof.
  intros; induction H; auto.
Qed.

Hint Resolve wfenv_to_ok.

Lemma wfenv_app_l : forall (E F : context TyEnvSource), WFEnv (E ++ F) -> WFEnv E.
Proof.
  intros E; induction E; intros; auto.
  inversion H;
  subst.
  apply WFPushV; auto.
  now apply IHE with (F := F).
  not_in_L v.
  apply WFPushT; auto.
  now apply IHE with (F := F).
  not_in_L v.
Qed.  
  
Lemma wfenv_app_r : forall (E F : context TyEnvSource), WFEnv (E ++ F) -> WFEnv F.
Proof.
  intros E.
  induction E; intros.
  - rewrite app_nil_l in H.
    auto.
  - inversion H; subst;
    apply (IHE _ H2).    
Qed.

Lemma wfenv_remove : forall (E F G : context TyEnvSource),
                    WFEnv (E ++ G ++ F) -> WFEnv (E ++ F).
Proof.
  intros.
  induction E using env_ind.
  rewrite app_nil_l in *.
  now apply wfenv_app_r in H.
  unfold extend; rewrite <- app_assoc.
  destruct v.
  - admit.
  - apply WFPushT.
    apply IHE.
    unfold extend in H; rewrite <- app_assoc in H.
    inversion H; subst.
    assumption.
    unfold extend in H.
    inversion H; subst.
    rewrite dom_union in *.
    rewrite union_spec in *.
    unfold not; intros.
    apply H4.
    inversion H0.
    auto.
    right.
    rewrite dom_union; rewrite union_spec.
    auto.
Admitted.

(** Free variable properties **)

(* fv_source distributes over the open_source operator *)

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
  - destruct H.
    rewrite union_spec; auto.
    rewrite <- union_spec.
    repeat rewrite union_spec.
    rewrite or_assoc.
    right.
    rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite union_spec.
    inversion H.
    assert (Ha : In x (union (fv_source t1) (fv_source t2))).
    eapply IHt1. apply H0.
    rewrite union_spec in Ha.
    inversion Ha. auto. auto. auto.
Qed.

(* fv_typ_source distributes over the open_typ_source operator *)
Lemma fv_open_rec_typ_source :
  forall t1 t2 x n, In x (fv_ptyp (open_rec_typ_source n t2 t1)) ->
               In x (union (fv_ptyp t1) (fv_ptyp t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; rewrite union_spec in *; auto.
  - rewrite union_spec.
    inversion H as [H1 | H1].
    apply IHt1_1 in H1; rewrite union_spec in H1; inversion H1; auto.
    apply IHt1_2 in H1; rewrite union_spec in H1; inversion H1; auto.
  - rewrite union_spec.
    inversion H as [H1 | H1].
    apply IHt1_1 in H1; rewrite union_spec in H1; inversion H1; auto.
    apply IHt1_2 in H1; rewrite union_spec in H1; inversion H1; auto.
  - destruct (Nat.eqb n0 n); auto. 
  - destruct H; rewrite union_spec in *.
    rewrite or_comm. rewrite <- or_assoc. left.
    rewrite or_comm; rewrite <- union_spec; eapply IHt1_1; apply H.
    rewrite or_assoc; right; rewrite <- union_spec; eapply IHt1_2; apply H.
Qed.

(* fv_source distributes over the open_typ_term_source operator *)
Lemma fv_open_rec_typ_term_source :
  forall t1 t2 x n, In x (fv_source (open_rec_typ_term_source n t2 t1)) ->
               In x (union (fv_source t1) (fv_ptyp t2)).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent n.
  induction t1; intros; simpl in *; try (now rewrite union_spec; auto).
  - eapply IHt1; apply H.
  - repeat rewrite union_spec. 
    rewrite union_spec in H.
    destruct H as [H | H].
    apply IHt1_1 in H; rewrite union_spec in H; inversion H; auto.
    apply IHt1_2 in H; rewrite union_spec in H; inversion H; auto.
  - repeat rewrite union_spec. 
    rewrite union_spec in H.
    destruct H as [H | H].
    apply IHt1_1 in H; rewrite union_spec in H; inversion H; auto.
    apply IHt1_2 in H; rewrite union_spec in H; inversion H; auto.
  - apply (IHt1 _ _ H).
  - repeat rewrite union_spec.
    rewrite union_spec in H.
    destruct H.
    auto.
    rewrite or_assoc.
    right.
    rewrite <- union_spec.
    apply (IHt1 _ _ H).
  - rewrite union_spec in H.
    repeat rewrite union_spec.
    inversion H.
    apply IHt1 in H0; rewrite union_spec in H0; inversion H0; auto.
    apply fv_open_rec_typ_source in H0.
    rewrite union_spec in H0.
    inversion H0; auto.
Qed.

(** Opening lemmas **)

(** "Ugly" lemma for open_rec_typ_source and open_rec_source **)
Lemma open_rec_typ_source_core :
  forall t j v i u,
    i <> j ->
    open_rec_typ_source j v t = open_rec_typ_source i u (open_rec_typ_source j v t) ->
    t = open_rec_typ_source i u t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in H0; inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - simpl in H0; inversion H0.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H.
    apply H3.
    apply H.
    apply H2.
  - simpl in *.
    case_eq (Nat.eqb j n); intros.
    case_eq (Nat.eqb i n); intros.
    exfalso. apply H. apply Nat.eqb_eq in H1.
    apply Nat.eqb_eq in H2. rewrite H1, H2.
    reflexivity.
    reflexivity.
    rewrite H1 in H0.
    apply H0.
  - simpl in H0; inversion H0.
    apply IHt1 in H2.
    apply IHt2 in H3.
    rewrite H2 at 1; rewrite H3 at 1.
    reflexivity.
    apply not_eq_S.
    apply H.
    apply H.
Qed.

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
    erewrite <- IHt.
    reflexivity.
    apply H.
    apply H2. 
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].
  - inversion H0; erewrite <- IHt; [ reflexivity | apply H | apply H2 ].   
Qed.

Lemma open_rec_type_term_source_core :
  forall t j v i u,
    open_rec_typ_term_source j v t = open_rec_source i u (open_rec_typ_term_source j v t) ->
    t = open_rec_source i u t.
Proof.
  intro t; induction t; intros; simpl; auto.
  - simpl in *.
    inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H2.
    apply H1.
  - inversion H.
    erewrite <- IHt1.
    erewrite <- IHt2.
    reflexivity.
    apply H2. 
    apply H1.
  - inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H.
    erewrite <- IHt.
    reflexivity.
    apply H1.
  - inversion H; erewrite <- IHt; [ reflexivity | apply H1 ].  
Qed.

(** Opening a locally-closed term/type leaves it unchanged **)

Lemma open_rec_type_source : forall t u,
  PType  t -> forall k, t =  open_rec_typ_source k u t.
Proof.
  intros t u H.
  induction H; intros; simpl; auto.
  - rewrite <- IHPType1; rewrite <- IHPType2; reflexivity.
  - rewrite <- IHPType1; rewrite <- IHPType2; reflexivity.
  - pick_fresh x.
    assert (Ha1 : not (In x L)) by not_in_L x.
    apply H1 with (k := S k) in Ha1.
    apply open_rec_typ_source_core in Ha1.
    rewrite <- Ha1.
    rewrite <- IHPType; reflexivity.
    auto.
Qed.

Lemma open_rec_source_term : forall t u,
  PTerm t -> forall k, t =  open_rec_source k u t.
Proof.
  induction 1; intros; simpl; auto.
  - pick_fresh x.
    rewrite <- open_rec_term_source_core with (j := 0) (v := PFVar x).
    reflexivity.
    auto.
    simpl.
    unfold open_source in *.
    rewrite <- H0.
    reflexivity.
    not_in_L x.
  - rewrite <- IHPTerm1.
    rewrite <- IHPTerm2.
    reflexivity.
  - rewrite <- IHPTerm1.
    rewrite <- IHPTerm2.
    reflexivity.
  - rewrite <- IHPTerm.
    reflexivity.
  - pick_fresh x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (k := k) in Ha.
    simpl; apply f_equal.
    now apply open_rec_type_term_source_core in Ha.
  - simpl; rewrite <- IHPTerm; reflexivity.
Qed.


(** Ortho environment properties **)

Lemma ortho_weaken :
  forall G E F t1 t2, Ortho (E ++ G) t1 t2 ->
                 WFEnv (E ++ F ++ G) ->
                 Ortho (E ++ F ++ G) t1 t2.
Proof.
  intros.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto; subst.
  - apply_fresh OForAll as x.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    rewrite <- app_comm_cons.
    apply WFPushV.
    auto.
    not_in_L x.
    not_in_L x. 
    rewrite dom_union in H2.
    exfalso.
    apply MSetProperties.Dec.F.union_1 in H2.
    inversion H2; contradiction.
    unfold extend; simpl; reflexivity.
  - apply OVar with (A := A); auto.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app.
    auto.
    apply in_or_app; right; apply in_or_app; auto.
  - apply OVarSym with (A := A); auto.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app.
    auto.
    apply in_or_app; right; apply in_or_app; auto.    
Qed.

Hint Resolve ortho_weaken.

(** Well-formedness of types **)

Lemma wf_weaken_source : forall G E F ty,
   WFTyp (E ++ G) ty -> 
   WFEnv (E ++ F ++ G) ->
   WFTyp (E ++ F ++ G) ty.
Proof.
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.  
  - subst; apply WFAnd.
    apply IHWFTyp1; auto.
    apply IHWFTyp2; auto.
    apply ortho_weaken; auto.
  (* Var *)
  - subst.
    apply WFVar with (ty := ty).
    apply in_app_or in H.
    inversion H.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.  
    assumption.
  (* ForAll *)
  - apply_fresh WFForAll as x.
    intros.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0 with (ty := ty).
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply WFPushV.
    apply H1.
    admit. (* not_in_L x. *)
    not_in_L x.
    rewrite dom_union in H7.
    rewrite union_spec in H7.
    inversion H7; contradiction.
Admitted.

Lemma wf_strengthen_source : forall z U E F ty,
  not (In z (fv_ptyp ty)) ->
  WFTyp (E ++ ((z,U) :: nil) ++ F) ty ->
  WFTyp (E ++ F) ty.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - apply WFInt.
    subst.
    admit. (* now apply ok_remove in H0. *)
  - eapply WFFun.
    subst.
    apply IHWFTyp1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFTyp2; simpl in *; not_in_L z; reflexivity.
  - eapply WFAnd.
    subst.
    apply IHWFTyp1; simpl in *; not_in_L z; reflexivity.
    subst.
    apply IHWFTyp2; simpl in *; not_in_L z; reflexivity.
    admit. (* assumption. *)
  - subst; eapply WFVar.
    apply in_or_app.
    repeat apply in_app_or in H0.
    inversion H0.
    left; apply H2.
    apply in_app_or in H2.
    inversion H2.
    inversion H3.
    inversion H4.
    subst.
    exfalso; apply H; simpl.
    left; reflexivity.
    inversion H4.
    auto.
    admit. (* now apply ok_remove in H1. *)
  - subst.
    apply_fresh WFForAll as x.
    unfold extend in *; simpl in *; intros.
    rewrite app_comm_cons.
    eapply H1.
    not_in_L x.
    not_in_L z.
    apply fv_open_rec_typ_source in H.
    rewrite union_spec in H.
    inversion H.
    auto.
    assert (NeqXZ : not (In x (singleton z))) by (not_in_L x).
    simpl in H5.
    exfalso; apply NeqXZ.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in H5.
    symmetry; assumption.
    rewrite app_comm_cons.
    reflexivity.
Admitted.

Lemma wf_env_comm_source : forall E F G H ty,
              WFTyp (E ++ F ++ G ++ H) ty ->
              WFTyp (E ++ G ++ F ++ H) ty.
Proof.
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply WFInt.
    admit. (* now apply ok_middle_comm. *)
  - apply WFAnd; auto.
    admit. (* ortho_middle_comm? *)
  - eapply WFVar.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; apply H2.
    apply in_or_app; right.
    apply in_app_or in H2.
    inversion H2.
    apply in_or_app.
    right; apply in_or_app; left.
    assumption.
    apply in_app_or in H3.
    inversion H3.
    apply in_or_app; auto.
    apply in_or_app; right; apply in_or_app; auto.
    admit. (* now apply ok_middle_comm. *)
  - apply_fresh WFForAll as x.
    unfold extend.
    intros.
    simpl.
    admit. (* should be possible through H1 *)
Admitted.

Lemma wf_env_comm_extend_source : forall Gamma x y v1 v2 ty,
              WFTyp (extend x v1 (extend y v2 Gamma)) ty ->
              WFTyp (extend y v2 (extend x v1 Gamma)) ty.
Proof.
  unfold extend.
  intros.
  rewrite <- app_nil_l with (l := ((x, v1) :: nil) ++ ((y, v2) :: nil) ++ Gamma) in H.
  apply wf_env_comm_source in H.
  now rewrite app_nil_l in H.
Qed. 

Lemma wf_weaken_extend_source : forall ty x v Gamma,
   WFTyp Gamma ty ->
   not (M.In x (dom Gamma)) ->                            
   WFTyp ((x,v) :: Gamma) ty.
Proof.
  intros.
  induction H; eauto.
  - apply WFInt.
    destruct v; auto.
    apply WFPushV; auto. admit. (* needs new assumption here *)
    apply WFPushT; auto.
  - apply WFAnd; auto.
    admit. (* needs ortho *)
  - eapply WFVar.
    apply in_cons; apply H.
    admit. (* needs new assumption here *)
  - apply_fresh WFForAll as x; cbn.
    unfold extend in H1.
    intros.
    apply wf_env_comm_extend_source.
    apply H1.
    not_in_L x0.
    not_in_L x.
    not_in_L x0.
Admitted.

Lemma wf_gives_types_source : forall Gamma ty, WFTyp Gamma ty -> PType ty.
Proof.
  intros.
  induction H; auto.
  - apply_fresh PType_ForAll as x.
    admit.
    apply H0.
    admit.
    not_in_L x.
Admitted.


(* Substitution (at type-level) lemmas *)

Lemma subst_typ_source_fresh : forall x t u, 
  not (In x (fv_ptyp t)) -> subst_typ_source x u t = t.
Proof.
  intros; induction t0; simpl in *; auto.
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - rewrite IHt0_1; [ rewrite IHt0_2 | not_in_L x ]; [ reflexivity | not_in_L x ].
  - case_eq (eqb v x); intros.
    exfalso; apply H; simpl; apply MSetProperties.Dec.F.singleton_2;
    now apply eqb_eq in H0.
    auto.
  - rewrite IHt0_1. rewrite IHt0_2. auto.
    not_in_L x.
    not_in_L x.
Qed.

Lemma subst_typ_source_open_source : forall x u t1 t2, PType u -> 
  subst_typ_source x u (open_typ_source t1 t2) = open_typ_source (subst_typ_source x u t1) (subst_typ_source x u t2).
Proof.
  intros. unfold open_typ_source. generalize 0.
  induction t1; intros; simpl; auto; try (apply f_equal; auto).
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - rewrite IHt1_1; rewrite IHt1_2; auto.
  - case_eq (Nat.eqb n0 n); intros; auto.
  - case_eq (eqb v x); intros; [ rewrite <- open_rec_type_source | ]; auto.
  - rewrite IHt1_1; rewrite IHt1_2; reflexivity.
Qed.

Lemma subst_typ_source_open_source_var :
  forall x y u t, y <> x -> PType u ->
             open_typ_source (subst_typ_source x u t) (PFVarT y) =
             subst_typ_source x u (open_typ_source t (PFVarT y)).
Proof.
  intros Neq Wu. intros. rewrite subst_typ_source_open_source; auto. simpl.
  case_eq (VarTyp.eqb Wu Neq); intros; auto.
  exfalso; apply H.
  now apply eqb_eq in H1.
Qed.

Lemma subst_typ_source_intro : forall x t u, 
  not (In x (fv_ptyp t)) -> PType u ->
  open_typ_source t u = subst_typ_source x u (open_typ_source t (PFVarT x)).
Proof.
  intros Fr Wu.
  intros.
  rewrite subst_typ_source_open_source.
  rewrite subst_typ_source_fresh.
  simpl.
  case_eq (eqb Fr Fr); intros; auto.
  apply EqFacts.eqb_neq in H1; exfalso; apply H1; reflexivity.
  auto. auto.
Qed.

Lemma subst_source_wf_typ : forall t z u Gamma,
  WFTyp Gamma u -> WFTyp Gamma t -> WFTyp Gamma (subst_typ_source z u t).
Proof.
  induction 2; simpl; auto.
  - apply WFAnd.
    apply IHWFTyp1; auto.
    apply IHWFTyp2; auto.

    assert (HH1 := H).
    assert (HH2 := H).
    apply IHWFTyp1 in HH1; apply IHWFTyp2 in HH2.
    clear IHWFTyp1 IHWFTyp2.

    (* generalize dependent Gamma. *)
    induction H0; intros.
    + simpl in *.
      inversion H0_; subst.
      inversion HH1; subst.
      apply OAnd1.
      apply IHOrtho1; auto.
      apply IHOrtho2; auto.
    + simpl in *.
      inversion H0_0; subst.
      inversion HH2; subst.   
      apply OAnd2.
      apply IHOrtho1; auto.
      apply IHOrtho2; auto.
    + simpl in *.
      inversion HH2; inversion HH1; inversion H0_; inversion H0_0; subst.
      apply OFun.
      apply IHOrtho; auto.
    + inversion H0_; inversion H0_0; subst.
      simpl in HH1; inversion HH1; simpl in HH2; inversion HH2; subst.
      simpl; apply_fresh OForAll as x.
      repeat rewrite subst_typ_source_open_source_var.
      admit. (*
      apply H1.
      apply H0 with (Gamma := (extend x (TyVar PTyp) Gamma)). *)
      not_in_L x.
      admit.
      (* apply wf_weaken_extend_source; auto. *)
      not_in_L x.
      admit.
      (*
      apply H4.
      not_in_L x.
      apply H7; auto.
      not_in_L x.      
      rewrite <- subst_typ_source_open_source_var.
      apply H5.
      not_in_L x.
      not_in_L x.
      now apply wf_gives_types_source in H1.
      rewrite <- subst_typ_source_open_source_var.
      apply H9.
      not_in_L x.
      not_in_L x.
      now apply wf_gives_types_source in H1.
      not_in_L x.
      now apply wf_gives_types_source in H1.
      not_in_L x.
      now apply wf_gives_types_source in H1. *)
    + admit. (*
      destruct t1; destruct t2; simpl in *; try now inversion H;
      try now (apply OAx; auto).
      now (inversion H as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).      
      now (inversion H as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).  *)
    + admit.
    + destruct t1; destruct t2; simpl in *; try now inversion H;
      try now (apply OAx; auto).
      now (inversion H0 as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
      inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).      
      now (inversion H0 as [H1 [H2 H3]]; inversion H1; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
      now (inversion H0 as [H1 [H2 H3]]; inversion H2; subst; inversion H5; subst;
           inversion H6; subst; inversion H7).
  - case_eq (VarTyp.eqb x z); intros; auto.
    apply WFVar with (ty := ty); auto.
  - apply_fresh WFForAll as x.
    intros.
    rewrite subst_typ_source_open_source_var.
    apply H1.
    not_in_L x.
    apply wf_weaken_extend_source.
    auto.
    not_in_L x.
    not_in_L x.
    now apply wf_gives_types_source in H.
Admitted.

Definition body_wf_typ t d Gamma :=
  exists L, forall x, not (In x L) -> WFEnv (extend x (TyDis d) Gamma) ->
            WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x)).

Lemma forall_to_body_wf_typ : forall d t1 Gamma, 
  WFTyp Gamma (ForAll d t1) -> body_wf_typ t1 d Gamma.
Proof. intros. unfold body_wf_typ. inversion H. subst. eauto. Qed.

Lemma open_body_wf_type : forall t d u Gamma,
  body_wf_typ t d Gamma -> WFTyp Gamma u -> WFTyp Gamma (open_typ_source t u).
Proof.
  intros. destruct H. pick_fresh y.

  assert (Ha : not (In y x)) by not_in_L y.
  apply H in Ha.
  rewrite <- app_nil_l with (l := Gamma).
  apply wf_strengthen_source with (z := y) (U := TyDis d).
  unfold not; intros HH.
  apply fv_open_rec_typ_source in HH.
  rewrite union_spec in HH.
  destruct HH; not_in_L y.
  rewrite app_nil_l.
  rewrite subst_typ_source_intro with (x := y).
  apply subst_source_wf_typ.
  apply wf_weaken_extend_source; auto.
  not_in_L y.
  unfold extend in H; apply H.
  not_in_L y.
  apply WFPushV.
  admit.
  (* now apply wf_gives_ok_env_source in H0. *)
  not_in_L y.
  not_in_L y.
  not_in_L y.
  admit.
  admit.
Admitted.

(** More properties on open **)

Lemma open_comm_open_typ_term :
  forall y x c n m, open_rec_typ_term n (STFVarT y) (open_rec m (STFVar elt x) c) =
               open_rec m (STFVar elt x) (open_rec_typ_term n (STFVarT y) c).
Proof.
  intros y x c.
  induction c; intros; simpl; auto.
  - case_eq (m =? n); intros; reflexivity.
  - apply f_equal; apply IHc.
  - rewrite IHc1; rewrite IHc2; reflexivity.
  - rewrite IHc1; rewrite IHc2; reflexivity.
  - rewrite IHc; reflexivity.
  - rewrite IHc; reflexivity.
  - apply f_equal; apply IHc.
  - rewrite IHc; reflexivity.
Qed.    

Lemma open_rec_typ_eq_source :
  forall ty n A, | open_rec_typ_source n A ty | = open_rec_typ n (| A |) (| ty |).
Proof.
  intro t.
  induction t; intros; auto.
  - simpl; rewrite IHt1; rewrite IHt2; auto.
  - simpl; rewrite IHt1; rewrite IHt2; auto.
  - simpl; case_eq (n0 =? n); intros; simpl; auto.
  - simpl; rewrite IHt2; auto.
Qed.


Lemma WFTyp_to_WFType : forall Gamma ty, WFTyp Gamma ty -> WFType (∥ Gamma ∥) (| ty |).
Proof.
  intros Gamma ty H.
  induction H; simpl; auto.
  - apply wfenv_to_ok in H0.
    apply WFType_Var; auto.
    now apply in_persists in H.
  - apply_fresh WFType_ForAll as x.
    simpl in *.
    assert (Ha : not (In x L)) by (not_in_L x).
    apply H0 in Ha.
    unfold extend; simpl.
    unfold open_typ_source in Ha.
    now rewrite open_rec_typ_eq_source in Ha.
    auto.
Qed.

Hint Resolve WFTyp_to_WFType.

End Infrastructure.