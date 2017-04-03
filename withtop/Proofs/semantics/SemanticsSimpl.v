Require Import String.
Require Import CoherenceBasicBD.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

Module Semantics
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module CBD := CoherenceBasicBiDi(VarTyp)(set).
Import CBD.

Inductive typing : ST.context PTyp -> PExp -> PTyp -> Prop :=
  | TyVar' : forall Gamma x ty,
               ST.ok Gamma ->
               List.In (x, ty) Gamma ->
               WFTyp ty ->
               typing Gamma (PFVar x) ty
  | TyLit' : forall Gamma i,
               ST.ok Gamma ->
               typing Gamma (PLit i) PInt
  | TyLam' : forall L Gamma t A B,
               (forall x, ~ ST.M.In x L ->
                     typing (ST.extend x A Gamma) (open_source t (PFVar x)) B) ->
               WFTyp A ->
               typing Gamma (PLam t) (Fun A B)
  | TyApp' : forall Gamma A B t1 t2,
               typing Gamma t1 (Fun A B) ->
               typing Gamma t2 A ->
               typing Gamma (PApp t1 t2) B
  | TyMerge' : forall Gamma A B t1 t2,
                 typing Gamma t1 A ->
                 typing Gamma t2 B ->
                 OrthoS A B ->
                 typing Gamma (PMerge t1 t2) (And A B)
  | TySub' : forall Gamma t A B,
               typing Gamma t A ->
               Sub A B ->
               WFTyp B ->
               typing Gamma t B.

Inductive In : PExp -> PTyp -> Prop :=
  | InInt : forall n, In (PAnn CT (PLit n) PInt) PInt
  | InFun : forall e A B, In (PAnn CT (PLam e) (Fun A B)) (Fun A B)
  | InAnd : forall v1 v2 A B, In v1 A ->
                         In v2 B ->
                         OrthoS A B ->
                         In (PMerge v1 v2) (And A B).

Inductive bidityping : ST.context PTyp -> PExp -> Dir -> PTyp -> Prop :=
  | ATyVar' : forall (Gamma : ST.context PTyp) (x : ST.var) (ty : PTyp),
                ST.ok Gamma ->
                List.In (x, ty) Gamma ->
                WFTyp ty ->
                bidityping Gamma (PFVar x) Inf ty
  | ATyLit' : forall (Gamma : ST.context PTyp) (x : nat),
                ST.ok Gamma ->
                bidityping Gamma (PLit x) Inf PInt
  | ATyApp' : forall (Gamma : ST.context PTyp) (A B : PTyp) (t1 t2 : PExp),
                bidityping Gamma t1 Inf (Fun A B) ->
                bidityping Gamma t2 Chk A ->
                bidityping Gamma (PApp t1 t2) Inf B
  | ATyMerge' : forall (Gamma : ST.context PTyp) (A B : PTyp) (t1 t2 : PExp),
                  bidityping Gamma t1 Inf A ->
                  bidityping Gamma t2 Inf B ->
                  OrthoS A B ->
                  bidityping Gamma (PMerge t1 t2) Inf (And A B)
  | ATyAnnCT' : forall (Gamma : ST.context PTyp) (t1 : PExp) (A : PTyp),
                  bidityping Gamma t1 Chk A ->
                  bidityping Gamma (PAnn CT t1 A) Inf A
  | ATyAnnRT' : forall (Gamma : ST.context PTyp) (t1 : PExp) (A : PTyp),
                  bidityping Gamma t1 Chk A ->
                  bidityping Gamma (PAnn RT t1 A) Inf A
  | ATyLam' : forall (L : ST.M.t) (Gamma : ST.context PTyp) 
                (t : PExp) (A B : PTyp),
                (forall x : ST.M.elt,
                   ~ ST.M.In x L ->
                   bidityping (ST.extend x A Gamma) (open_source t (PFVar x)) Chk B) ->
                WFTyp A ->
                bidityping Gamma (PLam t) Chk (Fun A B)
  | ATySub' : forall (Gamma : ST.context PTyp) (t : PExp) 
                (A B : PTyp) (C : ST.Exp),
                bidityping Gamma t Inf A ->
                sub A B C ->
                WFTyp B ->
                bidityping Gamma t Chk B.

Inductive red : PExp -> PExp -> Prop :=
  | Red_Int : forall n, red (PLit n) (PAnn CT (PLit n) PInt)
  | Red_App1 : forall e1 e2 e3,
                 red e1 e3 ->
                 red (PApp e1 e2) (PApp e3 e2)
  | Red_App2 : forall e1 e2 v A B,
                 ~ (In e1 A) ->
                 In v (Fun A B) ->
                 red (PAnn CT e1 A) (PAnn CT e2 A) ->
                 red (PApp v e1) (PApp v e2)
  | Red_App3 : forall A B e v,
                 In v A -> 
                 red (PApp (PAnn CT (PLam e) (Fun A B)) v)
                     (PAnn CT (open_source e v) B)
  | Red_Merge1 : forall e1 e2 e3,
                   red e1 e3 ->
                   red (PMerge e1 e2) (PMerge e3 e2)
  | Red_Merge2 : forall e1 e2 v A B,
                   In v (And A B) ->
                   red e1 e2 ->
                   red (PMerge v e1) (PMerge v e2)
  | Red_Ann1 : forall e1 e2 A,
                 ~ (In (PAnn CT e1 A) A) ->
                 ~ In e1 A ->
                 red e1 e2 ->
                 red (PAnn CT e1 A) (PAnn CT e2 A)
  | Red_Ann2 : forall A v,
                 In v A ->
                 red (PAnn CT v A) v
  | Red_Ann3Abs :
      forall e A B C D,
        Fun A B <> Fun C D ->
        red (PAnn CT (PAnn CT (PLam e) (Fun A B)) (Fun C D))
            (PAnn CT (PLam (PAnn CT (PApp (PAnn CT (PLam e) (Fun A B))
                                          (PAnn CT (PBVar 0) A)) D))
                  (Fun C D))
  | Red_Ann4 : forall v1 v2 A B C,
                    Sub B A ->
                    Atomic A ->
                    In (PMerge v1 v2) (And B C) ->
                    red (PAnn CT (PMerge v1 v2) A)
                        (PAnn CT v1 A)
  | Red_Ann5 : forall v1 v2 A B C,
                 Sub C A ->
                 Atomic A ->
                 In (PMerge v1 v2) (And B C) ->
                 red (PAnn CT (PMerge v1 v2) A)
                     (PAnn CT v2 A)
  | Red_Ann6 : forall v A B C D,
                 In v (And C D) ->
                 (And C D) <> (And A B) ->
                 red (PAnn CT v (And A B))
                     (PMerge (PAnn CT v A) (PAnn CT v B)).

Hint Constructors typing bidityping In WFTyp red.

(** Soundness and Completeness wrt to the elaborating biditypecheker **)

Theorem has_type_source_alg_rename :
  forall L Gamma A B t1 c m y,
    has_type_source_alg (ST.extend y A Gamma) (open_source t1 (PFVar y)) B m 
                        (ST.open c (ST.STFVar _ y)) ->
    (forall x, ~ ST.M.In x L ->
          has_type_source_alg (ST.extend x A Gamma) (open_source t1 (PFVar x)) B m
                              (ST.open c (ST.STFVar _ x))).
Proof.
  intros.
  (* subst_typ_source_intro *)
Admitted.
  
Theorem soundness : forall Gamma e A m, bidityping Gamma e A m -> has_ty Gamma e A m.
Proof.
  intros Gamma e A m H; unfold has_ty.
  induction H; destruct_conjs; eauto.
  - ST.pick_fresh x.
    destruct (H0 _ Fr) as [c H2].
    exists (ST.STLam' _ c).
    apply_fresh ATyLam as z; auto.
    apply has_type_source_alg_rename with (L := L) (y := x).
    admit. (* missing the good old renaming lemma... *)
    ST.not_in_L z.
Admitted.
    
Theorem completeness :
  forall Gamma A m d e, has_type_source_alg Gamma e A m d -> bidityping Gamma e A m.
Proof. intros Gamma A m d e H; induction H; eauto; destruct m; auto. Qed.

Hint Resolve soundness completeness.

(** Some necessary properties about bidityping, which are lifted from 
    the elaborated version **)

Theorem bityping_ok : forall Gamma t A m, bidityping Gamma t m A -> ST.ok Gamma.
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
  forall G E F t T dir, bidityping (E ++ G) t dir T ->
                   ST.ok (E ++ F ++ G) ->
                   bidityping (E ++ F ++ G) t dir T.
Proof.
  intros; apply soundness in H as [c H].
  assert (Ha := typing_weaken_alg _ _ _ _ _ _ _ H H0); eauto.
Qed.

Theorem bityping_strengthen:
  forall z U E F e dir A,
    not (ST.M.In z (fv_source e)) ->
    bidityping (E ++ ((z,U) :: nil) ++ F) e dir A ->
    bidityping (E ++ F) e dir A.
Proof.
  intros z U E F e dir A H1 H2; apply soundness in H2 as [c H2].
  assert (Ha := typing_strengthen_alg _ _ _ _ _ _ _ _ H1 H2); eauto.
Qed.

(* We didn't prove this before?! See: Pfenning *)
Theorem sub_trans : forall A B, Sub A B -> forall C, Sub B C -> Sub A C. Admitted.

Hint Resolve bityping_ok bityping_wf bityping_term bityping_weaken
     reflex sub_trans.
Hint Unfold Sub.

(*
Theorem bityping_ann_sub :
  forall Gamma t A B m1 m2, bidityping Gamma (PAnn m1 t A) m2 B -> Sub A B.
Proof. intros Gamma t A B m1 m2 Htyping; dependent induction Htyping; eauto. Qed.

Theorem bityping_ann :
  forall Gamma t A B m1 m2, bidityping Gamma (PAnn m1 t A) B m2 -> bidityping Gamma t Chk A.
Proof. intros Gamma t A B m1 m2 Htyping; dependent induction Htyping; eauto. Qed.
*)

(** Properties mixing "Sub", "In" and the type-system. **)

Theorem In_Ann_inv : forall v A B, In (PAnn CT v A) B -> A = B.
Proof. intros v A B H1; dependent induction H1; auto. Qed.

(*Hint Resolve bityping_ann_sub bityping_ann.*)
Hint Resolve In_Ann_inv.
Hint Unfold erase.

Theorem In_bityping_sub :
  forall A v, In v A -> forall B Gamma, bidityping Gamma v Inf B -> Sub A B.
Proof.
  intros A v HIn.
  induction HIn; eauto 3.
  - intros; inversion H; subst; eauto.
  - intros; inversion H; subst; eauto.
  - intros; dependent induction H0.
    clear IHbidityping1 IHbidityping2.
    apply IHHIn1 in H0_.
    apply IHHIn2 in H0_0.
    auto.
Qed.

Hint Resolve In_bityping_sub.

Theorem In_bityping :
  forall Gamma A B e, In e A -> bidityping Gamma e Inf B -> bidityping Gamma e Inf A.
Proof.
  intros Gamma A B e HIn Htyping.
  assert (HSub : Sub A B) by eauto.
  generalize dependent A.
  induction Htyping; intros; try now inversion HIn.
  - apply invAndS1 in HSub. destruct HSub.
    inversion HIn; subst.
    assert (Ha1 : Sub A1 A) by eauto.
    assert (Ha2 : Sub B0 B) by eauto.
    assert (Ha3 : bidityping Gamma t1 Inf A1) by auto.
    assert (Ha4 : bidityping Gamma t2 Inf B0) by auto.
    auto. (* since Value implies disjointness *)
  - inversion HIn; subst; eauto.
  - assert (Ha1 : Sub A0 A) by eauto.
    assert (Ha2 : bidityping Gamma t0 Inf A0) by auto.
    assert (Ha3 : Sub A0 A0) by apply reflex.
    destruct Ha3; eauto.
Qed.  

Hint Resolve In_bityping.

Theorem bityping_inf_chk :
  forall Gamma e A,
    bidityping Gamma e Inf A -> bidityping Gamma e Chk A.
Proof.
  intros Gamma e A Htyping.
  assert (Ha : Sub A A) by eauto; destruct Ha.
  eapply ATySub' with (A := A); eauto.
Qed.

Hint Resolve bityping_inf_chk.

(** Defining body. (getting ready for subject reduction) **)

Definition body_bityping Gamma t A B m :=
  exists L, forall x, not (ST.M.In x L) ->
            bidityping (ST.extend x A Gamma) (open_source t (PFVar x)) m B.

Hint Unfold body_bityping.

Lemma abs_to_body_bityping : forall A B e Gamma m, 
  bidityping Gamma (PLam e) m (Fun A B) -> body_bityping Gamma e A B m.
Proof. intros; inversion H; subst; eauto; inversion H0. Qed.

Lemma bityping_subst : forall Gamma A B e u m x,
                         List.In (x,B) Gamma ->
                         bidityping Gamma e m A ->
                         bidityping Gamma u Inf B ->
                         bidityping Gamma (subst_source x u e) m A.
Proof.
  intros Gamma A B e u m x HIn H1 H2.
  induction H1; simpl; eauto.
  - remember (eqb x0 x) as Heq; destruct Heq; auto.
    symmetry in HeqHeq; apply eqb_eq in HeqHeq; subst.
    assert (Ha : B = ty) by (eapply ok_unique_type; eauto); now subst.
  - apply_fresh ATyLam' as x; auto.
    rewrite subst_source_open_var; eauto.
    apply H0.
    ST.not_in_L y.
    right; simpl; assumption.
    rewrite <- app_nil_l with (l := (ST.extend y A Gamma)).
    apply bityping_weaken; simpl; auto.
    apply ST.Ok_push; eauto.
    ST.not_in_L y.
    ST.not_in_L y.
    ST.not_in_L x.
Qed.

Lemma open_body_bityping :
  forall e A B u Gamma m, body_bityping Gamma e A B m -> bidityping Gamma u Inf A ->
                 bidityping Gamma (open_source e u) m B.
Proof.
  intros e A B u Gamma m H1 H2; destruct H1. pick_fresh y.
  assert (Ha : not (ST.M.In y x)) by ST.not_in_L y; apply H in Ha.
  rewrite <- app_nil_l with (l := Gamma).
  eapply bityping_strengthen with (z := y) (U := A).
  ST.not_in_L y; apply fv_source_distr in H3; apply MSetProperties.Dec.F.union_1 in H3.
  inversion H3; contradiction.
  rewrite subst_source_intro with (x := y).
  apply bityping_subst with (B := A).
  simpl; left; auto.
  rewrite app_nil_l; auto.
  apply bityping_weaken; simpl; auto.
  apply ST.Ok_push; eauto.
  ST.not_in_L y.
  ST.not_in_L y.
  eauto.
Qed.


(** Theorem 1. Subject reduction **)

Theorem subject_reduction :
  forall Gamma e1 A m, bidityping Gamma e1 m A ->
              forall e2, red e1 e2 ->
                    bidityping Gamma e2 m A.
Proof.
  intros Gamma e1 A m Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma; generalize dependent m.
  induction Hred; intros; try now (dependent induction Htyping; subst; eauto).
  - (* R_App2 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping1 IHHtyping2.
    inversion H0; subst; inversion Htyping1; subst.
    apply ATyApp' with (A := A0); auto.
    assert (Ha : bidityping Gamma (PAnn CT e1 A0) Inf A0) by eauto.
    apply IHHred in Ha; inversion Ha; now subst.
  - (* R_App3 *)
    dependent induction Htyping; subst; eauto.
    clear IHHtyping1 IHHtyping2.
    inversion Htyping1; subst.
    apply ATyAnnCT'; clear Htyping1.
    apply open_body_bityping with (A := A0); eauto.
    inversion H4; subst; eauto.
    inversion H0.
    dependent induction Htyping2; subst; eauto.
    inversion H2.
  - (* R_Ann2 *)
    dependent induction Htyping; eauto; subst; clear IHHtyping.
    dependent induction Htyping; eauto.
    inversion H2. 
  - (* R_AnnAbs *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H0; subst.
    inversion H2; subst.
    apply ATyAnnCT'.     
    apply_fresh ATyLam' as x; auto.
    unfold open_source; simpl.
    assert (Ha : Sub D D) by apply reflex; destruct Ha.
    assert (Ha : WFTyp A) by
        (now assert (Ha := bityping_wf _ _ _ _ H0); inversion Ha).
    eapply ATySub' with (A := D); eauto 2.
    apply ATyAnnCT'.
    inversion H1; subst; clear H1.
    eapply ATySub' with (A := B); eauto 2.
    eapply ATyApp' with (A := A).
    + apply ATyAnnCT'.
      change (PLam (open_rec_source 1 (PFVar x) e)) with
             ((open_rec_source 0 (PFVar x) (PLam e))).
      rewrite <- open_rec_source_term; eauto 3.
      rewrite <- app_nil_l with (l := (ST.extend x C Gamma)).
      apply bityping_weaken; simpl; auto.
      apply ST.Ok_push; eauto.
      ST.not_in_L x.
    + assert (Ha1 : Sub A A) by apply reflex; destruct Ha1.
      eapply ATySub' with (A := A); eauto 2.
      apply ATyAnnCT'.
      eapply ATySub' with (A := C); eauto 2.
      apply ATyVar'; auto. 
      apply ST.Ok_push; eauto.
      ST.not_in_L x.
      now left.
  - (* R_Ann4 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    destruct H.
    inversion Htyping; subst.
    inversion H2; inversion H1; subst; eauto.
  - (* R_Ann5 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    destruct H.
    inversion Htyping; subst.
    inversion H2; inversion H1; subst; eauto.
  - (* R_Ann6 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H2; subst; try now inversion H5.
    assert (Ha : WFTyp (And A B)) by eauto; inversion Ha; subst.
    assert (Ha2 : Sub A0 A) by eauto.
    assert (Ha3 : Sub A0 B) by eauto.
    destruct Ha2, Ha3.
    apply ATyMerge'; eauto.
Qed.

(** Theorem 2. Reduction is deterministic **)

Hint Extern 1 =>
  match goal with
    | [ H : red (PLam ?e2) ?e1 |- _ ] => inversion H
    | [ H : In (PLam ?e) ?A |- _ ] => inversion H
    | [ H : In (PInt ?e) ?A |- _ ] => inversion H
  end. 

Lemma value_not_red : forall e1 e2 A, In e1 A -> red e1 e2 -> False.
Proof.
  intros e1 e2 A Hin Hred. generalize dependent A.
  induction Hred; intros; inversion Hin; subst; eauto; inversion H.
Qed.

Hint Extern 1 =>
  match goal with
    | [ H1 : In ?e1 ?A,
        H2 : red ?e1 ?e2 |- _ ] => exfalso; apply (value_not_red _ _ _ H1 H2)
  end. 

Lemma In_unique : forall v A B, In v A -> In v B -> A = B.
Proof.
  intros v A B HIn1 HIn2. generalize dependent B.
  induction HIn1; intros; inversion HIn2; subst; auto.
  apply IHHIn1_1 in H2.
  apply IHHIn1_2 in H3.
  now subst.
Qed.

Hint Rewrite In_unique.
    
Lemma value_ann_red_id :
  forall v A e, In v A -> red (PAnn CT v A) e -> v = e.
Proof.
  intros v A e Hin Hred.
  dependent induction Hred; eauto.
  - inversion Hin; subst; exfalso; now apply H.
  - inversion Hin; subst; inversion H0.
  - inversion Hin; subst; inversion H0.
  - inversion Hin; subst.
    assert (Ha : And C D = And A0 B) by (eapply In_unique; eauto).
    inversion Ha; subst; contradiction.
Qed.

Hint Rewrite value_ann_red_id.

Theorem red_unique :
  forall e1 e2, red e1 e2 -> forall e3, red e1 e3 -> e2 = e3.
Proof.
  intros e1 e2 Hred.
  induction Hred; intros.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
    + apply IHHred in H3; now subst.
    + inversion Hred; subst; auto.
  - inversion H0; subst.
    inversion H1; subst; auto.
    + assert (Ha : Fun A B = Fun A0 B0) by eauto; inversion Ha; subst.
      apply IHHred in H7; inversion H7; now subst.
    + contradiction.
  - inversion H0; subst; auto.
    + inversion H4; subst; auto. 
    + inversion H4; subst; contradiction.
  - inversion H; subst; auto.
    + apply IHHred in H3; now subst.
  - inversion H; subst.
    inversion H; inversion H0; subst; auto.
    apply IHHred in H15; now subst.
  - inversion H1; subst; auto; try now (inversion Hred; subst; auto).
    + apply IHHred in H7; now subst.
  - inversion H0; subst; auto.
    assert ((Fun A0 B) = (Fun C D)) by eauto; contradiction.
    inversion H; subst; inversion H4.
    inversion H; subst; inversion H4.
    assert (Ha : And C D = And A0 B) by (eapply In_unique; eauto); inversion Ha; subst.
    exfalso; now apply H5.
  - inversion H0; subst; auto.
    inversion H6; subst; auto.
    assert ((Fun A B) = (Fun C D)) by eauto; contradiction.
  - inversion H1; subst.
    dependent induction H2; subst; auto.
    inversion H2; subst; inversion H0.
    assert (Ha : And B C = And B0 C0) by (eapply In_unique; eauto); inversion Ha; subst.
    assert (Ha1 : ~ (Sub C0 A /\ Sub B0 A)) by eauto.
    exfalso; apply Ha1; split; assumption.
    inversion H0.
  - inversion H1; subst.
    dependent induction H2; subst; auto.
    inversion H2; subst; inversion H0.
    assert (Ha : And B C = And B0 C0) by (eapply In_unique; eauto); inversion Ha; subst.
    assert (Ha1 : ~ (Sub C0 A /\ Sub B0 A)) by eauto.
    exfalso; apply Ha1; split; assumption.
    inversion H0.
  - inversion H; subst.
    inversion H1; subst; auto.
    assert (Ha : And C D = And A B) by (eapply In_unique; eauto); inversion Ha; subst. 
    exfalso; now apply H0.
    inversion H10.
    inversion H10.    
Qed.
      
(** Theorem 3. All typeable terms can reduce **)


Theorem typeable_terms_reduce :
  forall e1 A m, bidityping nil e1 m A -> (exists e2, red e1 e2) \/ In e1 A.
Proof.  
  intros e1 A m H.
  dependent induction H; eauto.
  - inversion H0.
  - left.
    assert (Ha1 : (exists e2 : PExp, red t1 e2) \/ In t1 (Fun A B)) by eauto.
    destruct Ha1.
    destruct H1; eauto.
    assert (Ha2 : (exists e2, red t2 e2) \/ In t2 A) by eauto.
    destruct Ha2.
    destruct H2.
    inversion H1; subst.
    assert (Ha : red ( 
    admit. (* *)
    eauto.
    admit.
Admitted.

End Semantics.







