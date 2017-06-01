
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import STLCNew.
Require Import CoherenceBasicBDNew.
Require Import STLCred.

Inductive VChk : PExp -> PTyp -> Prop :=
  | VLam : forall A B t, VChk (PLam t) (Fun A B).

Inductive VInf : PExp -> PTyp -> Prop :=
  | VInt : forall n, VInf (PLit n) PInt
  | VMerge : forall v1 v2 A B, VInf v1 A ->
                          VInf v2 B ->
                          VInf (PMerge v1 v2) (And A B)
  | VAnn : forall v A, VChk v A -> VInf (PAnn v A) A. 

Hint Constructors VChk VInf.

Definition value (v : PExp) := exists A, VInf v A.

Inductive subred : PExp -> PExp -> PTyp -> Prop :=
  | SRed_Fun :
      forall v A B C D,
        VInf v (Fun A B) ->
        subred v (PAnn (PLam (PAnn (PApp v (PBVar 0)) D)) (Fun C D)) (Fun C D)
  | SRed_AndR : forall v A B, value v ->
                         subred v (PMerge (PAnn v A) (PAnn v B)) (And A B)
  | SRed_AndL1 : forall v1 v2 A B, VInf v1 B ->
                              value v2 ->
                              Atomic A ->
                              Sub B A ->
                              subred (PMerge v1 v2) v1 A
  | SRed_AndL2 : forall v1 v2 A C, value v1 ->
                              VInf v2 C ->
                              Atomic A ->
                              Sub C A ->
                              subred (PMerge v1 v2) v2 A.

Inductive bired : PExp -> PExp -> Prop :=
  | Red_App1 : forall e1 e2 e3,
                 bired e1 e3 ->
                 bired (PApp e1 e2) (PApp e3 e2)
  | Red_App2 : forall e1 e2 v,
                 value v ->
                 bired e1 e2 ->
                 bired (PApp v e1) (PApp v e2)
  | Red_App3 : forall A B C v1 v2 e,
                 VInf v1 (Fun A B) ->
                 VInf v2 C ->
                 A <> C ->
                 subred v2 e A ->
                 bired (PApp v1 v2) (PApp v1 e)
  | Red_App4 : forall A B e v,
                 VChk v A ->
                 bired (PApp (PAnn (PLam e) (Fun A B)) v)
                       (PAnn (open_source e (PAnn v A)) B)
  | Red_App5 : forall A B e v,
                 VInf v A -> 
                 bired (PApp (PAnn (PLam e) (Fun A B)) v)
                       (PAnn (open_source e v) B)
  | Red_Merge1 : forall e1 e2 e3,
                   bired e1 e3 ->
                   bired (PMerge e1 e2) (PMerge e3 e2)
  | Red_Merge2 : forall e1 e2 v,
                   value v ->
                   bired e1 e2 ->
                   bired (PMerge v e1) (PMerge v e2)
  | Red_Ann1 : forall e1 e2 A,
                 bired e1 e2 ->
                 bired (PAnn e1 A) (PAnn e2 A)
  | Red_Ann2 : forall v e A B,
                 VInf v B ->
                 A <> B ->
                 subred v e A ->
                 bired (PAnn v A) (PAnn e A)
  | Red_Ann3 : forall v A, VInf v A ->
                      bired (PAnn v A) v.

Hint Constructors WFTyp subred bired.

(* We didn't prove this before?! See: Pfenning *)
Theorem sub_trans : forall A B, Sub A B -> forall C, Sub B C -> Sub A C. Admitted.

Hint Resolve reflex sub_trans.
Hint Unfold Sub.

Hint Unfold erase.

Theorem VInf_bityping_eq :
  forall A v, VInf v A -> forall B Gamma, bidityping Gamma v Inf B -> A = B.
Proof.
  intros A v HIn.
  induction HIn; eauto 3.
  - intros; inversion H; subst; eauto.
  - intros; inversion H; subst.
    erewrite IHHIn1; erewrite IHHIn2; eauto.
  - intros; now inversion H0; subst.
Qed.

Hint Resolve VInf_bityping_eq.

Theorem VInf_bityping_sub :
  forall A v, VInf v A -> forall B Gamma m, bidityping Gamma v m B -> Sub A B.
Proof.
  intros A v HIn.
  induction HIn. 
  - intros; inversion H; subst; auto.
    inversion H0; subst; eauto.
  - intros; dependent induction H; [ clear IHbidityping1 IHbidityping2 | eauto 5 ].
    apply sand1; [ apply sand2 | apply sand3 ]; eauto.
  - intros; inversion H; subst; auto.
    inversion H0; subst; eauto.
    inversion H1; subst; eauto.
Qed.

Hint Resolve VInf_bityping_sub.

Theorem bityping_inf_chk :
  forall Gamma e A,
    bidityping Gamma e Inf A -> bidityping Gamma e Chk A.
Proof.
  intros Gamma e A Htyping.
  assert (Ha : Sub A A) by eauto; destruct Ha.
  eapply ATySub' with (A := A); eauto.
Qed.

Hint Resolve bityping_inf_chk.

(** Theorem 1. Subject reduction **)

Theorem subject_reduction_sub' :
  forall Gamma v A, bidityping Gamma v Inf A ->
           forall e B, subred v e B ->
                  Sub A B ->
                  WFTyp B ->
                  bidityping Gamma e Inf B.
Proof.
  intros Gamma v A Htyping e B Hred HTyp.
  generalize dependent Gamma.
  induction Hred; intros. 
  - inverts H. dependent induction Htyping; subst; eauto; clear IHHtyping.
    inverts H0.
    assert (Ha1 : Sub (Fun C D) (Fun C D)). eauto. destruct Ha1.
    apply ATyAnnCT'.
    assert (Ha : WFTyp (Fun A0 B)) by
        (now assert (Ha := bityping_wf Htyping); inversion Ha).
    inverts Ha.
    apply_fresh ATyLam' as x; auto.
    unfold open_source; simpl.
    case_nat*.
    assert (Ha2 : Sub D D) by eauto; destruct Ha2.
    eapply ATySub' with (A := D); eauto 2.
    apply ATyAnnCT'.
    inverts HTyp; inverts H2.
    eapply ATySub' with (A := B); eauto 2.
    eapply ATyApp' with (A := A0).
    + apply ATyAnnCT'.
      rewrite <- open_rec_source_term; eauto 3.
      rewrite <- concat_empty_r with (E := Gamma & y ~ C).
      apply bityping_weaken; rewrite concat_empty_r; autos*.
    + assert (Ha1 : Sub C C) by apply reflex; destruct Ha1.
      eapply ATySub' with (A := C); eauto 2.
      apply* ATyVar'.
  - inverts H.
    inverts HTyp. inverts H; try now inversion H3.
    inverts H0.
    assert (Ha : Sub (And A0 B) (And A0 B)) by eauto.
    destruct Ha.
    apply* ATyMerge'.
  - dependent induction Htyping; subst; eauto. clear IHHtyping1 IHHtyping2.
    assert (B = A) by eauto; subst. admit.
  - dependent induction Htyping; subst; eauto. clear IHHtyping1 IHHtyping2.
    assert (C = B) by eauto; subst. admit.
Admitted.  

Theorem subject_reduction_sub :
  forall Gamma v A, bidityping Gamma v Inf A ->
           forall e B, subred v e B ->
                  Sub A B ->
                  WFTyp B ->
                  bidityping Gamma e Chk B.
Proof.
  intros Gamma v A Htyping e B Hred HTyp.
  generalize dependent Gamma.
  induction Hred; intros. 
  - inverts H. dependent induction Htyping; subst; eauto; clear IHHtyping.
    inverts H0.
    assert (Ha1 : Sub (Fun C D) (Fun C D)). eauto. destruct Ha1.
    apply ATySub' with (A := Fun C D) (C := x); eauto.
    apply ATyAnnCT'.
    assert (Ha : WFTyp (Fun A0 B)) by
        (now assert (Ha := bityping_wf Htyping); inversion Ha).
    inverts Ha.
    apply_fresh ATyLam' as x; auto.
    unfold open_source; simpl.
    case_nat*.
    assert (Ha2 : Sub D D) by eauto; destruct Ha2.
    eapply ATySub' with (A := D); eauto 2.
    apply ATyAnnCT'.
    inverts HTyp; inverts H2.
    eapply ATySub' with (A := B); eauto 2.
    eapply ATyApp' with (A := A0).
    + apply ATyAnnCT'.
      rewrite <- open_rec_source_term; eauto 3.
      rewrite <- concat_empty_r with (E := Gamma & y ~ C).
      apply bityping_weaken; rewrite concat_empty_r; autos*.
    + assert (Ha1 : Sub C C) by apply reflex; destruct Ha1.
      eapply ATySub' with (A := C); eauto 2.
      apply* ATyVar'.
  - inverts H.
    inverts HTyp. inverts H; try now inversion H3.
    inverts H0.
    assert (Ha : Sub (And A0 B) (And A0 B)) by eauto.
    destruct Ha.
    apply* ATySub'.
    apply* ATyMerge'.
  - dependent induction Htyping; subst; eauto. clear IHHtyping1 IHHtyping2.
    assert (B = A) by eauto; subst. destruct H2; apply* ATySub'.
  - dependent induction Htyping; subst; eauto. clear IHHtyping1 IHHtyping2.
    assert (C = B) by eauto; subst. destruct H2; apply* ATySub'.
Qed.  
      
Theorem subject_reduction :
  forall Gamma e1 A m, bidityping Gamma e1 m A ->
              forall e2, bired e1 e2 ->
                    bidityping Gamma e2 m A.
Proof.
  intros Gamma e1 A m Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma; generalize dependent m.
  induction Hred; intros; try now (dependent induction Htyping; subst; eauto).
  - (* R_App3 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping1 IHHtyping2.
    inversion H; subst; inversion Htyping1; subst.
    apply ATyApp' with (A := A0); auto.
    inverts Htyping2. inverts H0.
    assert (Ha : C = A) by eauto; subst.
    apply* subject_reduction_sub.
  - (* R_App4 *)
    dependent induction Htyping; eauto; clear IHHtyping1 IHHtyping2.
    inverts* Htyping1.
    apply ATyAnnCT'. inverts H.
    inverts H4.
    eapply open_body_bityping; eauto.
    inverts H.
  - (* R_App5 *)
    dependent induction Htyping; subst; eauto.
    clear IHHtyping1 IHHtyping2.
    inversion Htyping1; subst.
    apply ATyAnnCT'; clear Htyping1.
    apply open_body_bityping with (A := A0); eauto.
    inversion H4; subst; eauto.
    inversion H0.
    dependent induction Htyping2; subst; eauto.
    inversion H2.
    assert (B = A) by eauto; now subst.
  - (* R_Ann2 *)
    dependent induction Htyping; eauto; subst; clear IHHtyping.
    inverts Htyping. inverts H.
    apply ATyAnnCT'; apply* subject_reduction_sub.
  - (* R_Ann3 *)
    dependent induction Htyping; eauto; clear IHHtyping.
    inverts Htyping. inverts H.
    assert (A = A0) by eauto; now subst.
Qed.

(** Theorem 2. Reduction is deterministic **)

Hint Extern 1 =>
  match goal with
    | [ H : bired (PLam ?e2) ?e1 |- _ ] => inversion H
    | [ H : VInf (PLam ?e) ?A |- _ ] => inversion H
    | [ H : VInf (PInt ?e) ?A |- _ ] => inversion H
  end. 

Lemma value_inf_chk_false : forall v A B, VChk v A -> VInf v B -> False.
Proof.
  introv H1 H2; inverts H1; inverts H2.
Qed.

Hint Resolve value_inf_chk_false.

Lemma value_not_red : forall e1 e2 A, VInf e1 A -> bired e1 e2 -> False.
Proof.
  intros e1 e2 A Hin Hred. generalize dependent A.
  induction Hred; intros; try now inversion Hin; subst; eauto.
  inverts Hin. inverts H2. inverts Hred.
Qed.

Hint Extern 1 =>
  match goal with
    | [ H1 : VInf ?e1 ?A,
        H2 : bired ?e1 ?e2 |- _ ] => exfalso; apply (value_not_red _ _ _ H1 H2)
    | [ H1 : value ?v,
        H2 : bired ?e1 ?e2 |- _ ] => destruct H1 as [HHH1 HHH2]; exfalso;
                                    apply (value_not_red _ _ _ HHH1 H2)
  end. 

Lemma VInf_unique : forall v A B, VInf v A -> VInf v B -> A = B.
Proof.
  intros v A B HIn1 HIn2. generalize dependent B.
  induction HIn1; intros; inversion HIn2; subst; auto.
  apply IHHIn1_1 in H1; apply IHHIn1_2 in H3; now subst.
Qed.

Hint Rewrite VInf_unique.
Hint Resolve value_not_red.

Hint Extern 1 =>
  match goal with
    | [ H : VInf (PLam ?e) ?A |- _ ] => inverts H
    | [ H : bired (PLam ?e1) ?e2 |- _ ] => inverts H
  end. 

Theorem subred_unique : forall v e1 A, subred v e1 A -> forall e2 Gamma, subred v e2 A ->
                                                          bidityping Gamma v Chk A -> e1 = e2.
Proof.
  introv Hred1.
  induction Hred1; introv Hred2 Typ.
  - inverts H. inverts* Hred2.
  - inverts* Hred2. inverts H2. inverts H2.
  - inverts* Hred2. inverts H3. inverts H1.
    inverts Typ. inverts H3.
    assert (Ha1 : B = A1) by eauto.
    assert (Ha2 : C = B0) by eauto. substs.
    assert (Ha3 : Sub (And A1 B0) A) by eauto.
    lets* Ha4 : uniquesub H15 Ha3.
  - inverts* Hred2. inverts H3. inverts H1.
    inverts Typ. inverts H3.
    assert (Ha1 : B = A1) by eauto.
    assert (Ha2 : C = B0) by eauto. substs.
    assert (Ha3 : Sub (And A1 B0) A) by eauto.
    lets* Ha4 : uniquesub H15 Ha3.
Qed.
    
Theorem bired_unique :
  forall e1 e2, bired e1 e2 -> forall e3, bired e1 e3 -> forall Gamma A m,
                                               bidityping Gamma e1 m A -> e2 = e3.
Proof.
  introv Hred.
  induction Hred; intros.
  - dependent induction H0; eauto; clear IHbidityping1 IHbidityping2.
    inverts* H.
    + forwards* Ha : IHHred; substs*.
    + destruct H2; tryfalse*.
    + inverts H0_; inverts* Hred.
    + inverts* Hred.
  - dependent induction H1; eauto; clear IHbidityping1.
    inverts* H0.
    + destruct* H.
    + forwards* Ha : IHHred; substs*.
    + inverts* H4.
  - dependent induction H4; eauto; clear IHbidityping1 IHbidityping2.
    inverts* H3.
    + assert (Ha1 : Fun A1 B1 = Fun A B). apply VInf_unique with (v := v1); auto.
      assert (Ha2 : Fun A1 B1 = Fun A0 B0) by eauto.
      inverts Ha1; inverts Ha2.
      lets* Ha : subred_unique H2 H10 H4_0; substs*.
    + tryfalse*.
    + inverts H. assert (C = A) by apply* VInf_unique. substs*.
  - dependent induction H1; eauto; clear IHbidityping1 IHbidityping2.
    inverts H1_. inverts H0; tryfalse*. auto.
  - dependent induction H1; eauto; clear IHbidityping1 IHbidityping2.
    inverts* H0.
    + inverts* H4.
    + inverts H3. assert (C = A1) by apply* VInf_unique. substs*.
    + tryfalse*.
  - dependent induction H0; eauto; clear IHbidityping1 IHbidityping2.
    inverts H.
    forwards* Ha : IHHred. substs*.
    destruct H3.
    tryfalse*.
  - dependent induction H1; eauto; clear IHbidityping1 IHbidityping2.
    inverts H0. destruct* H. forwards* Ha : IHHred. substs*.
  - dependent induction H0; eauto.
    inverts* H.
    forwards* Ha : IHHred; substs*.
  - dependent induction H3; eauto; clear IHbidityping.
    inverts* H2.
    lets* Ha : subred_unique H1 H9 H3; substs*.
    assert (A = B) by apply* VInf_unique. substs*.
  - dependent induction H1; eauto; clear IHbidityping.
    inverts* H0.
    assert (A = B) by apply* VInf_unique. substs*.
Qed.

(** Theorem 3. Reduction is complete **)

(*
Lemma value_ann_red_id :
  forall v A e, In v A -> red (PAnn CT v A) e -> v = e.
Proof.
  intros v A e Hin Hred.
  dependent induction Hred; eauto.
  - inversion Hin; subst; exfalso. now apply H.
  - inversion Hin; subst; inversion H0.
  - inversion Hin; subst; inversion H0.
  - inversion Hin; subst.
    assert (Ha : And C D = And A0 B) by (eapply In_unique; eauto).
    inversion Ha; subst; contradiction.
Qed.

Hint Rewrite value_ann_red_id.
 *)

Hint Constructors equiv_.
Hint Resolve fullred_regular.

Lemma fullred_equiv_regular :
  forall e1 e2, equiv_ fullred e1 e2 -> STTerm e1 /\ STTerm e2.
Proof. introv H; induction* H. Qed.

Lemma fullred_equiv_regular_l :
  forall e1 e2, equiv_ fullred e1 e2 -> STTerm e1.
Proof. introv H; forwards* Ha : fullred_equiv_regular e1 e2. Qed.

Lemma fullred_equiv_regular_r :
  forall e1 e2, equiv_ fullred e1 e2 -> STTerm e2.
Proof. introv H; forwards* Ha : fullred_equiv_regular e1 e2. Qed.

Hint Resolve fullred_equiv_regular_l fullred_equiv_regular_r.

Lemma fullred_equiv_app_l :
  forall e1 e2, equiv_ fullred e1 e2 ->
           forall e3, STTerm e3 ->
                 equiv_ fullred (STApp e1 e3) (STApp e2 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Lemma fullred_equiv_app_r :
  forall e2 e3, equiv_ fullred e2 e3 ->
           forall e1, STTerm e1 ->
                 equiv_ fullred (STApp e1 e2) (STApp e1 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Hint Resolve fullred_equiv_app_l fullred_equiv_app_r.

Lemma fullred_equiv_pair_l :
  forall e1 e2, equiv_ fullred e1 e2 ->
           forall e3, STTerm e3 ->
                 equiv_ fullred (STPair e1 e3) (STPair e2 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Lemma fullred_equiv_pair_r :
  forall e2 e3, equiv_ fullred e2 e3 ->
           forall e1, STTerm e1 ->
                 equiv_ fullred (STPair e1 e2) (STPair e1 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Lemma fullred_equiv_pair :
  forall e1 e3, equiv_ fullred e1 e3 ->
           forall e2 e4, equiv_ fullred e2 e4 ->
                 equiv_ fullred (STPair e1 e2) (STPair e3 e4).
Proof.
  introv H1 H2.
  apply equiv_trans with (t2 := (STPair e3 e2)). 
  apply* fullred_equiv_pair_l.
  apply* fullred_equiv_pair_r.
Qed.

Hint Resolve fullred_equiv_pair_l fullred_equiv_pair_r fullred_equiv_pair.

Lemma subred_equiv : forall v t A,
              subred v t A ->
              forall E1 E2, 
                has_type_source_alg empty v Chk A E1 ->
                has_type_source_alg empty t Chk A E2 ->
                equiv_ fullred E1 E2.
Proof.
  introv Subred.
  induction Subred; introv Typ1 Typ2.
  - inverts H; inverts H0.
    inverts Typ1; inverts Typ2.
    inverts H.
    inverts H2.
    inverts H3.
    inverts H0.
    inverts H6; inverts H7; try now inverts H.
    admit.
  - inverts Typ1. inverts Typ2.
    inverts H3.
    inverts H1; try now inverts H6.
    inverts H4; try now inverts H14.
    inverts H.
    inverts H8. inverts H10.
    assert (x = A0) by eauto. substs.
    inverts* H4. inverts* H6.
    assert (A0 = A) by eauto. substs.
    assert (A = A1) by eauto. symmetry in H6; substs.
    assert (C0 = c2). apply @sub_coherent with (A := A) (B := B0); eauto.
    assert (C = c1). apply @sub_coherent with (A := A) (B := A2); eauto. substs.
    assert (E1 = E) by apply* typ_coherence.
    assert (E0 = E) by apply* typ_coherence. substs.
    clear H2 H5 H9 H10 H0 H4.
    admit.
  - inverts Typ1; inverts Typ2.
    inverts H.
    assert (B = A1) by eauto. substs.
    inverts H3.
    assert (A1 = A2) by eauto. substs.
    assert (E1 = E0). eapply typ_coherence; eauto. substs.
    inverts H4.
    inverts H1.
    assert (Ha : WFTyp A2) by eauto.
    assert (c = C0). eapply sub_coherent. apply Ha. apply H5. auto. auto. substs.
    admit. (* seems provable *)
    assert (Ha : Sub (And A2 B) A) by eauto.
    lets Ha1 : uniquesub H14 Ha.
    destruct Ha1; unfold Sub; split; eauto.
  - inverts Typ1; inverts Typ2.
    inverts H0.
    assert (C = A1) by eauto. substs.
    inverts H3.
    assert (A1 = B) by eauto. substs.
    assert (E2 = E0). eapply typ_coherence; eauto. substs.
    inverts H4.
    inverts H1.
    assert (Ha : Sub (And A2 B) A) by eauto.
    lets Ha1 : uniquesub H14 Ha.
    destruct Ha1; unfold Sub; split; eauto.
    assert (Ha : WFTyp B) by eauto.
    assert (c = C1). eapply sub_coherent. apply Ha. apply H5. auto. auto. substs.
    admit. (* seems provable *)
Admitted.    

Definition id := STLam (STBVar 0).
Definition idType a := STFun a a.

Definition app := STLam (STLam (STApp (STBVar 1) (STBVar 0))).
Definition appType a b := STFun (STFun a b) (STFun a b).

Lemma app_id :
  forall A B,
    has_type_st empty app (appType A B) ->
    forall f, has_type_st empty f (STFun A B) ->
         STValue f ->
         equiv_ fullred (STApp app f) f.
Proof.
  introv Typ1 Typ2 Value.
  inverts Value; inverts Typ2.
  unfold app.
  apply* equiv_trans.
  unfold open; simpls; repeat case_nat.
  
Admitted.  

Lemma consistency_fullred :
  forall e A c1 m, has_type_source_alg empty e m A c1 ->
              forall e', bired e e' ->
                    forall c2, has_type_source_alg empty e' m A c2 ->
                         equiv_ fullred c1 c2.
Proof.
  introv Typ.
  gen_eq E: (empty:env PTyp). lets Typ': Typ.
  induction* Typ; intros; substs.
  - inverts* H3.
  - inverts* H2; inverts H1.
  - inverts* H0.
    + inverts* H1.
      assert (HH : exists c, has_type_source_alg empty e3 Inf (Fun A B) c).
      apply soundness; apply completeness in Typ1; lets* Ha : subject_reduction Typ1.
      destruct HH.
      assert (Ha : Fun A0 B = Fun A B) by (eapply typ_inf_unique; eauto); inverts Ha; clear H.
      assert (E2 = E3) by apply* typ_coherence; subst.
      lets* Ha1 : IHTyp1 Typ1 H4 H3. 
    + inverts H3; inverts H. inverts H1. inverts Typ1.
      inverts H1.
      inverts H6.
      inverts H1.
      inverts H4.
      inverts Typ1.
      lets* Ha1 : IHTyp2 Typ2 H5 H6.
      assert (E0 = E1) by apply* typ_coherence; subst.
      lets Ha2 : type_preservation H6.
      unfold conv_context in Ha2; rewrite map_empty in Ha2. eauto. 
    + inverts H3.
      inverts Typ1.
      inverts H.
      inverts H1.
      inverts H3.
      clear IHTyp1 IHTyp2.
      assert (E1 = E0) by (eapply typ_coherence; eauto).
      subst.
      apply* fullred_equiv_app_r.

      inverts Typ2. inverts H4. 
      assert (Ha : exists E4, has_type_source_alg empty e Inf A E4). admit.
      destruct Ha.
      inverts H6.
      inverts H2.
      forwards* Ha : typ_unique H2 H3. destruct Ha.
      assert (x = E1). apply* typ_coherence. substs.
      assert (C1 = C0). apply @sub_coherent with (A := A) (B := A0); eauto. substs.
      
      admit. (* property about subred ? *)
    + clear IHTyp1 IHTyp2.
      inverts Typ1.
      inverts H1; clear H5.
      inverts H4.
      admit. (* beta reduction *)
    + clear IHTyp1 IHTyp2.
      inverts Typ1.
      admit. (* beta reduction *)
  - inverts H1; inverts H2.
    + lets* Ha1 : IHTyp1 Typ1 ___ H7.
      assert (E2 = E3) by apply* typ_coherence; substs*. 
    + lets* Ha1 : IHTyp2 Typ2 ___ H9.
      assert (E1 = E0) by apply* typ_coherence; substs*.
  - inverts H0.
    + inverts H1; forwards* Ha : IHTyp Typ.
    + inverts H1.
      admit. (* property about subred ? *)
    + inverts Typ.
      inverts H1.
      clear IHTyp.
      inverts Typ'; clear H8.
      assert (Ha : A = A0) by eauto. symmetry in Ha; subst.
      assert (c2 = E0). eapply typ_coherence; eauto. subst; clear H1.
      admit. (* induction H0 and discharge cases using H4? *)
  - lets* Ha : IHTyp Typ H2.
    inverts H3.
    inverts* H2.
    assert (A = A0).
    lets* Ha1 : completeness Typ.
    lets* Ha2 : subject_reduction Ha1 H2.
    apply soundness in Ha2; destruct Ha2; eapply typ_inf_unique; eauto.
    subst.
    lets* Ha3 : Ha H1.
    assert (C0 = C).
    eapply @sub_coherent with (B := B) (A := A0); auto; apply* typing_wf_source_alg.
    subst.
    lets* Ha4 : type_correct_coercions H4 ___.
Admitted.
    
