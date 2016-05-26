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
  eapply WFPushV; auto.
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
  - inversion H; subst.
    apply WFPushV; auto.
    not_in_L x.
  - inversion H; subst.
    apply WFPushT; auto.
    not_in_L x.
Qed.


Lemma wfenv_extend_comm : forall (E F : context TyEnvSource) x v,
               WFEnv (F ++ E ++ (x, v) :: nil) ->
               WFEnv (F ++ (x, v) :: nil ++ E).
Proof.
  intros E F x v HWFEnv.  
  generalize dependent E.
  
  induction F using env_ind; intros.
  - unfold extend; simpl.
    rewrite app_nil_l in HWFEnv.
    destruct v.
    + apply WFPushV.
      now apply wfenv_app_l in HWFEnv.
      rewrite <- app_nil_l in HWFEnv.
      apply wfenv_remove in HWFEnv.
      simpl in *; now inversion HWFEnv.
      induction E.
      simpl in *; inversion HWFEnv.
      not_in_L x.
      simpl in *.
      destruct a; simpl in *.
      unfold not; intros H; apply MSetProperties.Dec.F.add_iff in H.
      destruct H.
      subst.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst; apply IHE; auto.
    + apply WFPushT.
      now apply wfenv_app_l in HWFEnv.
      induction E.
      simpl in *; inversion HWFEnv.
      not_in_L x.
      simpl in *.
      destruct a; simpl in *.
      unfold not; intros H; apply MSetProperties.Dec.F.add_iff in H.
      destruct H.
      subst.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst.
      apply IHE; auto.
      not_in_L x.
      exfalso; apply H0.
      now apply MSetProperties.Dec.F.singleton_2.
      inversion HWFEnv; subst; apply IHE; auto.
  - destruct v0.
    unfold extend.
    simpl in *.
    inversion HWFEnv; subst.
    apply WFPushV.
    apply IHF; auto.
    not_in_L x0.
    not_in_L x0.
    unfold not; intros; apply H4; now apply MSetProperties.Dec.F.singleton_2.
    simpl in *.
    inversion HWFEnv; subst.
    apply WFPushT.
    apply IHF; auto.
    not_in_L x0.
    unfold not; intros; apply H3; now apply MSetProperties.Dec.F.singleton_2.
Qed.

Lemma wfenv_app_comm : forall (E F : context TyEnvSource), WFEnv (F ++ E) -> WFEnv (E ++ F).
Proof.
  intros.
  generalize dependent H.
  generalize dependent F.
  dependent induction E using (@env_ind).
  - intros.
    rewrite app_nil_r in H.
    now simpl.
  - intros.
    unfold extend in *.
    rewrite <- app_assoc.
    destruct v.
    apply WFPushV.
    apply IHE.
    apply wfenv_remove in H.
    assumption.
    apply wfenv_app_r in H.
    apply wfenv_app_l in H.
    now inversion H.
    not_in_L x.
    apply wfenv_app_r in H.
    now inversion H.
    rewrite app_assoc in H.
    apply IHE in H.
    apply wfenv_app_r in H.
    rewrite <- app_nil_l in H.
    apply wfenv_extend_comm in H.
    simpl in H; now inversion H.
    apply WFPushT.
    apply IHE.
    now apply wfenv_remove in H.    
    not_in_L x.
    unfold not; intros HH.
    apply wfenv_app_r in H.
    now inversion H.
    rewrite app_assoc in H.
    apply IHE in H.
    apply wfenv_app_r in H.
    rewrite <- app_nil_l in H.
    apply wfenv_extend_comm in H.
    simpl in H; now inversion H.
Qed.

Lemma wfenv_extend_comm' : forall (E F : context TyEnvSource) x v,
     WFEnv (F ++ (x, v) :: nil ++ E) ->
     WFEnv (F ++ E ++ (x, v) :: nil).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros.
  - simpl in *.
    inversion H; subst; apply wfenv_app_comm; now simpl.
  - simpl in *.
    inversion H; subst.
    apply WFPushV; auto.
    admit. (* provable *)
    apply WFPushT; auto.
    admit. (* provable *)
Admitted.
    
Lemma wfenv_middle_comm : forall E F G H,
              WFEnv (E ++ F ++ G ++ H) ->
              WFEnv (E ++ G ++ F ++ H).
Proof.
  intros E.
  induction E; intros.
  - simpl in *.
    apply wfenv_app_comm.
    rewrite <- app_assoc.
    induction F.
    + simpl in *; now apply wfenv_app_comm.
    + inversion H0; subst; simpl in *.
      inversion H0; subst.
      apply WFPushV.
      apply IHF; auto.
      not_in_L v.
      not_in_L v.
      simpl in H10; rewrite dom_union in H10;
      apply MSetProperties.Dec.F.union_1 in H10; destruct H10;
      [ auto | contradiction ].
      inversion H0; subst.
      apply WFPushT.
      apply IHF; auto.
      not_in_L v.
      simpl in H8; rewrite dom_union in H8;
      apply MSetProperties.Dec.F.union_1 in H8; destruct H8;
      [ auto | contradiction ].
  - destruct a; destruct t0; simpl in *.
    inversion H0; subst.
    apply WFPushV; auto.
    not_in_L v.
    simpl in H6; rewrite dom_union in H6.
    apply MSetProperties.Dec.F.union_1 in H6; destruct H6.
    contradiction.
    simpl in H6; rewrite dom_union in H6.
    apply MSetProperties.Dec.F.union_1 in H6; destruct H6; contradiction.
    inversion H0; subst.
    apply WFPushT; auto.
    not_in_L v.
    simpl in H5; rewrite dom_union in H5.
    apply MSetProperties.Dec.F.union_1 in H5; destruct H5.
    contradiction.
    simpl in H6; rewrite dom_union in H5.
    apply MSetProperties.Dec.F.union_1 in H5; destruct H5; contradiction.
Qed.


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

Lemma ortho_strengthen : forall z U E F ty1 ty2,
  not (In z (union (fv_ptyp ty1) (fv_ptyp ty2))) ->
  Ortho (E ++ ((z,U) :: nil) ++ F) ty1 ty2 ->
  Ortho (E ++ F) ty1 ty2.
Proof.
  intros.
  remember (E ++ ((z,U) :: nil) ++ F).
  
  generalize dependent Heql.
  generalize dependent E.
  
  induction H0; intros; auto.
  - apply OAnd1; [ apply IHOrtho1 | apply IHOrtho2 ];
    simpl in H; not_in_L z; apply Heql.
  - apply OAnd2; [ apply IHOrtho1 | apply IHOrtho2 ];
    simpl in H; not_in_L z; apply Heql.
  - apply OFun;
    apply IHOrtho; simpl in H; not_in_L z; auto.
  - apply_fresh OForAll as x.
    subst; unfold extend; simpl.
    rewrite app_comm_cons.
    eapply H1.
    not_in_L x.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.union_1 in HH.
    destruct HH as [HH | HH]; apply fv_open_rec_typ_source in HH.
    apply MSetProperties.Dec.F.union_1 in HH; simpl in HH; simpl in H.
    destruct HH as [HH | HH].
    apply H.
    apply MSetProperties.Dec.F.union_2.
    apply MSetProperties.Dec.F.union_3.
    assumption.
    not_in_L x.
    apply H11.
    not_in_L z.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in HH.
    now symmetry.
    apply MSetProperties.Dec.F.union_1 in HH; simpl in HH; simpl in H.
    destruct HH as [HH | HH].
    apply H.
    apply MSetProperties.Dec.F.union_3.
    apply MSetProperties.Dec.F.union_3.
    assumption.
    not_in_L x.
    apply H11.
    not_in_L z.
    apply MSetProperties.Dec.F.singleton_2.
    apply MSetProperties.Dec.F.singleton_1 in HH.
    now symmetry.
    unfold extend; now simpl.
  - subst.
    apply OVar with (A := A); auto.
    now apply wfenv_remove in H0.
    apply in_or_app.
    apply in_app_or in H1.
    destruct H1; auto.
    destruct H1; auto.
    inversion H1; subst; simpl in H.
    not_in_L x.
    exfalso; apply H3.
    now apply MSetProperties.Dec.F.singleton_2.
  - subst.
    apply OVarSym with (A := A); auto.
    now apply wfenv_remove in H0.
    apply in_or_app.
    apply in_app_or in H1.
    destruct H1; auto.
    destruct H1; auto.
    inversion H1; subst; simpl in H.
    not_in_L x.
    exfalso; apply H4.
    now apply MSetProperties.Dec.F.singleton_2.
  - subst; apply OAx; auto.
    now apply wfenv_remove in H0.
Qed.

Hint Resolve ortho_weaken ortho_strengthen.

Lemma ortho_extend_comm :
  forall F E x v ty1 ty2,
    Ortho (F ++ E ++ (x, v) :: nil) ty1 ty2 ->
    Ortho (F ++ (x, v) :: nil ++ E) ty1 ty2.
Proof.
  intros F E x v ty1 ty2 HOrtho.
  remember (F ++ E ++ (x, v) :: nil).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    change ((y, TyDis d) :: F ++ (x, v) :: E) with
           (((y, TyDis d) :: F) ++ ((x, v) :: nil) ++ E).
    apply H0.
    not_in_L y.
    unfold extend; now simpl.
  - apply OVar with (A := A).
    now apply wfenv_extend_comm.
    admit. (* provable *)
    auto.
  - apply OVarSym with (A := A).
    now apply wfenv_extend_comm.
    admit. (* provable *)
    auto.
  - apply wfenv_extend_comm in H.
    now apply OAx. 
Admitted.

Lemma ortho_extend_comm' :
  forall F E x v ty1 ty2,
    Ortho (F ++ (x, v) :: nil ++ E) ty1 ty2 ->
    Ortho (F ++ E ++ (x, v) :: nil) ty1 ty2.
Proof.
  intros F E x v ty1 ty2 HOrtho.
  remember (F ++ (x, v) :: nil ++ E).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    change ((y, TyDis d) :: F ++ E ++ (x, v) :: nil) with
           (((y, TyDis d) :: F) ++ E ++ (x, v) :: nil).
    apply H0.
    not_in_L y.
    unfold extend; now simpl.
  - apply OVar with (A := A).
    now apply wfenv_extend_comm'.
    admit. (* provable *)
    auto.
  - apply OVarSym with (A := A).
    now apply wfenv_extend_comm'.
    admit. (* provable *)
    auto.
  - apply wfenv_extend_comm' in H.
    now apply OAx.
Admitted.
    
Lemma ortho_app_comm :
  forall E F ty1 ty2, Ortho (F ++ E) ty1 ty2 -> Ortho (E ++ F) ty1 ty2.
Proof.
  intros E F ty1 ty2 HOrtho.
  remember (F ++ E).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  dependent induction HOrtho; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H0 with (F0 := extend x (TyDis d) F) (E0 := E) in Ha.
    apply ortho_extend_comm' in Ha.
    change ((x, TyDis d) :: E ++ F) with (nil ++ (x, TyDis d) :: E ++ F).
    apply ortho_extend_comm with (E := E ++ F).
    simpl in *.
    rewrite <- app_assoc.
    apply Ha.
    unfold extend; now simpl.
  - apply OVar with (A := A).
    now apply wfenv_app_comm.
    admit. (* provable *)
    auto.
  - apply OVarSym with (A := A).
    now apply wfenv_app_comm.
    admit. (* provable *)
    auto.
  - apply OAx; auto.
    now apply wfenv_app_comm.
Admitted.

Lemma ortho_middle_comm : forall H E F G ty1 ty2,
              Ortho (E ++ F ++ G ++ H) ty1 ty2 ->
              Ortho (E ++ G ++ F ++ H) ty1 ty2.
Proof.
  induction H; intros.
  - rewrite app_nil_r in *.
    rewrite app_assoc.
    apply ortho_app_comm.
    generalize dependent E.
    generalize dependent F.
    induction G; intros.
    + intros; rewrite app_nil_r in *; now apply ortho_app_comm.
    + intros.
      change (F ++ E ++ a :: G) with (F ++ E ++ (a :: nil) ++ G).
      destruct a.
      assert ((F ++ E ++ ((v, t0) :: nil) ++ G) = (F ++ (E ++ ((v, t0) :: nil)) ++ G))
             by now rewrite <- app_assoc.
      rewrite H0; clear H0.
      apply IHG.
      rewrite <- app_assoc.
      apply ortho_extend_comm.
      change (E ++ F ++ (v, t0) :: G) with (E ++ F ++ ((v, t0) :: nil) ++ G) in H.
      rewrite app_assoc in H.
      apply ortho_extend_comm' in H.
      now rewrite <- app_assoc in *.
  - change (E ++ G ++ F ++ a :: H) with (E ++ G ++ F ++ (a :: nil) ++ H).
    destruct a.
    assert ((E ++ G ++ F ++ ((v, t0) :: nil) ++ H) =
            (E ++ G ++ (F ++ ((v, t0) :: nil)) ++ H)) by
    now rewrite <- app_assoc.
    rewrite H1; clear H1.
    apply IHlist.
    rewrite <- app_assoc.
    rewrite app_assoc.
    apply ortho_extend_comm.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite app_assoc in H0.
    rewrite app_assoc in H0.
    change (((E ++ F) ++ G) ++ (v, t0) :: H) with
           (((E ++ F) ++ G) ++ ((v, t0) :: nil) ++ H).
    apply ortho_extend_comm' in H0.
    repeat rewrite <- app_assoc in H0.
    apply H0.
Qed.     

Lemma ortho_gives_wfenv : forall Gamma t1 t2, Ortho Gamma t1 t2 -> WFEnv Gamma.
Proof.
  intros.
  induction H; auto.
  - rewrite <- app_nil_l.
    pick_fresh x.
    apply wfenv_remove with ((x,TyDis d) :: nil).
    simpl.
    apply H0.
    not_in_L x.
Qed.

Hint Resolve ortho_gives_wfenv.

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
    intros.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    apply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply WFPushV.
    apply H2.
    not_in_L x.
    not_in_L x.
    rewrite dom_union in H8.
    rewrite union_spec in H8.
    inversion H8; contradiction.
    apply IHWFTyp; auto.
Qed.    
    
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
    now apply wfenv_remove in H0.
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
    subst; eauto.
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
    now apply wfenv_remove in H1.
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
    apply IHWFTyp.
    simpl in H; not_in_L z.
    reflexivity.
Qed.

(*
Lemma in_app : forall List.In (x, TyDis A) (E ++ F ++ G ++ H) ->
                 List.In (x, TyDis A) (E ++ G ++ F ++ H)
*)

Hint Resolve in_or_app.
Hint Resolve in_app_or.

Lemma ortho_env_comm :
  forall E F G H ty1 ty2, Ortho (E ++ F ++ G ++ H) ty1 ty2 ->
                     Ortho (E ++ G ++ F ++ H) ty1 ty2.
Proof.  
  intros.
  remember (E ++ F ++ G ++ H).
  generalize dependent Heql.
  generalize dependent E.
  generalize dependent F.
  generalize dependent G.
  dependent induction H0; intros; subst; auto.
  - apply_fresh OForAll as x.
    unfold extend; simpl; rewrite app_comm_cons; apply H1.
    not_in_L x.
    reflexivity.
  - apply wfenv_middle_comm in H0.
    apply OVar with (A := A); auto.
    repeat (apply in_app_or in H1; destruct H1); auto 10.
  - apply wfenv_middle_comm in H0.
    apply OVarSym with (A := A); auto.
    repeat (apply in_app_or in H1; destruct H1); auto 10.
  - apply OAx; auto.
    now apply wfenv_middle_comm.
Qed.  

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
    now apply wfenv_middle_comm.
  - apply WFAnd; auto.
    now apply ortho_middle_comm.
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
    now apply wfenv_middle_comm.
  - apply_fresh WFForAll as x.
    unfold extend.
    intros.
    simpl.
    rewrite app_comm_cons.
    apply H1.
    not_in_L x.
    unfold extend; now simpl.
    now apply IHWFTyp.
Qed.

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
   not (M.In x (union (dom Gamma) (fv_ptyp v))) ->                            
   WFTyp ((x,TyDis v) :: Gamma) ty.
Proof.
  intros.
  induction H; eauto.
  - apply WFInt.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
  - apply WFAnd; auto.
    rewrite <- app_nil_l with (l := ((x, TyDis v) :: Gamma)).
    change ((x, TyDis v) :: Gamma) with (((x, TyDis v) :: nil) ++ Gamma).
    apply ortho_weaken.
    now rewrite app_nil_l.
    apply ortho_gives_wfenv in H2.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
  - eapply WFVar.
    apply in_cons; apply H.
    apply WFPushV; auto.
    not_in_L x.
    not_in_L x.
  - apply_fresh WFForAll as x; cbn.
    unfold extend in H1.
    intros.
    apply wf_env_comm_extend_source.
    apply H1.
    not_in_L y.
    simpl; not_in_L x.
    apply MSetProperties.Dec.F.add_iff in H0.
    destruct H0.
    not_in_L y.
    not_in_L x.
    apply IHWFTyp.
    not_in_L x.
Qed.

Lemma wf_gives_types_source : forall Gamma ty, WFTyp Gamma ty -> PType ty.
Proof.
  intros.
  induction H; auto.
  - apply_fresh PType_ForAll as x.
    auto.
    apply H0.
    not_in_L x.
Qed.

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

(* TODO: looks like we need to apply a substitution to environments *)
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
      simpl.
      apply_fresh OForAll as x.
      repeat rewrite subst_typ_source_open_source_var.
      admit. (*
      apply H1.
      apply H0 with (Gamma := (extend x (TyVar PTyp) Gamma)). *)
      not_in_L x.
      now apply wf_gives_types_source in H.
      not_in_L x.
      now apply wf_gives_types_source in H.
    + simpl in *.
      destruct (eqb x z).
      admit.
      apply OVar with (A := A); auto.
      admit.
    + admit.
    + destruct t1; destruct t2; simpl in *; try now inversion H;
      try (now (apply OAx; auto)); try orthoax_inv_r; try orthoax_inv_l.
  - case_eq (VarTyp.eqb x z); intros; auto.
    apply WFVar with (ty := ty); auto.
  - apply_fresh WFForAll as x.
    intros.
    rewrite subst_typ_source_open_source_var.
    admit. (* apply H1. *)
    not_in_L x.
    now apply wf_gives_types_source in H.
    now apply IHWFTyp.
Admitted.

Definition body_wf_typ t d Gamma :=
  exists L, forall x, not (In x L) -> WFTyp Gamma d ->
            WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x)).

Lemma forall_to_body_wf_typ : forall d t1 Gamma, 
  WFTyp Gamma (ForAll d t1) -> body_wf_typ t1 d Gamma.
Proof. intros. unfold body_wf_typ. inversion H. subst. eauto. Qed.

Lemma open_body_wf_type : forall t d u Gamma,
  body_wf_typ t d Gamma -> WFTyp Gamma d -> WFTyp Gamma u -> WFTyp Gamma (open_typ_source t u).
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
  auto.
  not_in_L y.
  now apply wf_gives_types_source in H1.
  auto.
Qed.

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
Qed.

Hint Resolve WFTyp_to_WFType.

End Infrastructure.