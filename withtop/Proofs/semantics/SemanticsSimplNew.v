
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.
Require Import LibLN.
Require Import STLCNew.
Require Import CoherenceBasicBDNew.


Inductive typing : env PTyp -> PExp -> PTyp -> Prop :=
  | TyVar' : forall Gamma x ty,
               ok Gamma ->
               binds x ty Gamma ->
               WFTyp ty ->
               typing Gamma (PFVar x) ty
  | TyLit' : forall Gamma i,
               ok Gamma ->
               typing Gamma (PLit i) PInt
  | TyLam' : forall L Gamma t A B,
               (forall x, x \notin L ->
                     typing (Gamma & x ~ A) (open_source t (PFVar x)) B) ->
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
  | InInt : forall n, In (PAnn (PLit n) PInt) PInt
  | InFun : forall e A B, In (PAnn (PLam e) (Fun A B)) (Fun A B)
  | InAnd : forall v1 v2 A B, In v1 A ->
                         In v2 B ->
                         In (PMerge v1 v2) (And A B).

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

Inductive red : PExp -> PExp -> Prop :=
  | Red_Int : forall n, red (PLit n) (PAnn (PLit n) PInt)
  | Red_App1 : forall e1 e2 e3,
                 red e1 e3 ->
                 red (PApp e1 e2) (PApp e3 e2)
  | Red_App2 : forall e1 e2 v A B,
                 In v (Fun A B) ->
                 red e1 e2 ->
                 red (PApp v e1) (PApp v e2)
  | Red_App3 : forall A B C v1 v2,
                 In v1 (Fun A B) ->
                 In v2 C ->
                 A <> C ->
                 red (PApp v1 v2) (PApp v1 (PAnn v2 C))
  | Red_App4 : forall A B e v,
                 In v A -> 
                 red (PApp (PAnn (PLam e) (Fun A B)) v)
                     (PAnn (open_source e v) B)
  | Red_Merge1 : forall e1 e2 e3,
                   red e1 e3 ->
                   red (PMerge e1 e2) (PMerge e3 e2)
  | Red_Merge2 : forall e1 e2 v A,
                   In v A ->
                   red e1 e2 ->
                   red (PMerge v e1) (PMerge v e2)
  | Red_Ann1 : forall e1 e2 A,
                 ~ (In (PAnn e1 A) A) ->
                 red e1 e2 ->
                 red (PAnn e1 A) (PAnn e2 A)
  | Red_Ann2 : forall v,
                 In v PInt ->
                 red (PAnn v PInt) v
  | Red_Ann3 :
      forall e A B C D,
        red (PAnn (PAnn (PLam e) (Fun A B)) (Fun C D))
            (PAnn (PLam (PAnn (PApp (PAnn (PLam e) (Fun A B))
                                          (PAnn (PBVar 0) A)) D))
                  (Fun C D))
  | Red_Ann4 : forall v1 v2 A B C,
                    Sub B A ->
                    Atomic A ->
                    In (PMerge v1 v2) (And B C) ->
                    red (PAnn (PMerge v1 v2) A)
                        (PAnn v1 A)
  | Red_Ann5 : forall v1 v2 A B C,
                 Sub C A ->
                 Atomic A ->
                 In (PMerge v1 v2) (And B C) ->
                 red (PAnn (PMerge v1 v2) A)
                     (PAnn v2 A)
  | Red_Ann6 : forall v A B C D,
                 In v (And C D) ->
                 red (PAnn v (And A B))
                     (PMerge (PAnn v A) (PAnn v B)).

Hint Constructors typing bidityping In WFTyp red.

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
    exists (STLam' c).
    apply_fresh ATyLam as z; auto.
    apply has_type_source_alg_rename with (L := L) (y := x).
    admit. (* missing the good old renaming lemma... *)
    autos*.
Admitted.
    
Theorem completeness :
  forall Gamma A m d e, has_type_source_alg Gamma e A m d -> bidityping Gamma e A m.
Proof. intros Gamma A m d e H; induction H; eauto; destruct m; auto. Qed.

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

Theorem bityping_strengthen:
  forall z U E F e dir A,
    z \notin (fv_source e) ->
    bidityping (E & z ~ U & F) e dir A ->
    bidityping (E & F) e dir A.
Proof.
  intros z U E F e dir A H1 H2; apply soundness in H2 as [c H2].
  lets* Ha : typing_strengthen_alg H1 H2.
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

Theorem In_Ann_inv : forall v A B, In (PAnn v A) B -> A = B.
Proof. intros v A B H1. inverts* H1. Qed.

(*Hint Resolve bityping_ann_sub bityping_ann.*)
Hint Resolve In_Ann_inv.
Hint Unfold erase.

Theorem In_bityping_eq :
  forall A v, In v A -> forall B Gamma, bidityping Gamma v Inf B -> A = B.
Proof.
  intros A v HIn.
  induction HIn; eauto 3.
  - intros; inversion H; subst; eauto.
  - intros; inversion H; subst; eauto.
  - intros.
    inverts* H.
    apply IHHIn1 in H2.
    apply IHHIn2 in H4.
    now subst.
Qed.

Hint Resolve In_bityping_eq.

Theorem In_bityping_sub :
  forall A v, In v A -> forall B Gamma m, bidityping Gamma v m B -> Sub A B.
Proof.
  intros A v HIn.
  induction HIn. 
  - intros; inversion H; subst; auto.
    inversion H0; subst; eauto.
  - intros; inversion H; subst; auto.
    inversion H0; subst; eauto.
  - intros; dependent induction H; [ clear IHbidityping1 IHbidityping2 | eauto 5 ].
    apply sand1; [ apply sand2 | apply sand3 ]; eauto.
Qed.

Hint Resolve In_bityping_sub.

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


(** Theorem 1. Subject reduction **)

Theorem subject_reduction :
  forall Gamma e1 A m, bidityping Gamma e1 m A ->
              forall e2, red e1 e2 ->
                    bidityping Gamma e2 m A.
Proof.
  intros Gamma e1 A m Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma; generalize dependent m.
  induction Hred; intros; try now (dependent induction Htyping; subst; eauto).
  - (* R_App3 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping1 IHHtyping2.
    inversion H; subst; inversion Htyping1; subst.
    apply ATyApp' with (A := A0); auto.
    inversion Htyping2; subst.
    inversion H0.
    assert (Ha : C = A) by eauto; subst.
    eapply ATySub' with (A := A); eauto.
  - (* R_App4 *)
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
    dependent induction Htyping; eauto.
    inversion H1; subst; eauto.
  - (* R_AnnAbs *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H; subst.
    inversion H1; subst.
    apply ATyAnnCT'.     
    apply_fresh ATyLam' as x; auto.
    unfold open_source; simpl.
    assert (Ha : Sub D D) by apply reflex; destruct Ha.
    assert (Ha : WFTyp A) by
        (now assert (Ha := bityping_wf _ _ _ _ H); inversion Ha).
    eapply ATySub' with (A := D); eauto 2.
    apply ATyAnnCT'.
    inversion H0; subst; clear H0.
    eapply ATySub' with (A := B); eauto 2.
    eapply ATyApp' with (A := A).
    + apply ATyAnnCT'.
      change (PLam (open_rec_source 1 (PFVar x) e)) with
             ((open_rec_source 0 (PFVar x) (PLam e))).
      rewrite <- open_rec_source_term; eauto 3.
      rewrite <- concat_empty_r with (E := Gamma & x ~ C).
      apply bityping_weaken; rewrite concat_empty_r; autos*.
    + assert (Ha1 : Sub A A) by apply reflex; destruct Ha1.
      eapply ATySub' with (A := A); eauto 2.
      apply ATyAnnCT'.
      eapply ATySub' with (A := C); eauto 2.
      case_nat*.
  - (* R_Ann4 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    destruct H.
    inversion Htyping; subst.
    inversion H2; inversion H1; subst.
    assert (B = A1) by eauto; subst; eauto.    
  - (* R_Ann5 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    destruct H.
    inversion Htyping; subst.
    inversion H2; inversion H1; subst.
    assert (C = B0) by eauto; subst; eauto.
  - (* R_Ann6 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H1; subst; try now inversion H4.
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
  apply IHHIn1_1 in H1; apply IHHIn1_2 in H3; now subst.
Qed.

Hint Rewrite In_unique.

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

Theorem red_unique :
  forall e1 e2, red e1 e2 -> forall e3, red e1 e3 -> forall Gamma A m, bidityping Gamma e1 m A -> e2 = e3.
Proof.
  intros e1 e2 Hred.
  induction Hred; intros.
  - inversion H; subst; auto.
  - inversion H; subst; auto.
    + dependent induction H0; subst; eauto; clear IHbidityping1 IHbidityping2.
      eapply IHHred in H4; subst; eauto.
    + inversion Hred; subst; auto.
  - inversion H0; subst.
    inversion H1; subst; auto.
    + dependent induction H1; eauto. clear IHbidityping1 IHbidityping2.
      eapply IHHred in H6; subst; eauto.
    + dependent induction H1; eauto.
    + dependent induction H1; eauto.
  - inversion H2; subst; auto.
    + assert (Ha : C = C0) by (eapply In_unique; eauto); subst; auto.
    + assert (Ha : Fun A1 B0 = Fun A B) by (eapply In_unique; eauto).
      inversion Ha; subst.
      assert (Ha1 : A = C) by (eapply In_unique; eauto); subst.
      exfalso; apply H1; auto.
  - inversion H0; subst; auto.
    + inversion H5; subst; auto. 
    + inversion H4; subst.
      assert (Ha1 : A1 = C) by (eapply In_unique; eauto); subst.
      exfalso; apply H7; auto.
  - inversion H; subst; auto.
    + dependent induction H0; eauto; clear IHbidityping1 IHbidityping2.
      eapply IHHred in H4; subst; eauto.
  - dependent induction H0; eauto; clear IHred.
    dependent induction H2; eauto; clear IHbidityping1 IHbidityping2.
    eapply IHHred in H0; subst; eauto.
  - dependent induction H0; eauto.
    clear IHred.
    dependent induction H2; eauto 3; clear IHbidityping.
    eapply IHHred in H0; subst; eauto.
    inversion H1; subst; inversion Hred; subst; auto.
  - inversion H0; subst; auto; inversion H.
  - dependent induction H; eauto.
    assert (Ha : In (PAnn (PLam e) (Fun A B)) (Fun A B)) by auto.
    apply (value_not_red _ _ _ Ha) in H0; exfalso; auto.
  - inversion H1; subst.
    dependent induction H2; subst; auto.
    inversion H2; subst; inversion H0.
    dependent induction H5; subst; eauto 3; clear IHbidityping.
    assert (Ha : And B C = And B0 C0) by (eapply In_unique; eauto); inversion Ha; subst.
    inversion H5; subst.
    assert (Ha1 : A0 = And B0 C0) by (symmetry; eauto); subst.
    inversion H6; subst.
    assert (Ha1 : ~ (Sub C0 A /\ Sub B0 A)) by eauto.
    exfalso; apply Ha1; split; assumption.
    inversion H0.
  - inversion H1; subst.
    dependent induction H2; subst; auto.
    inversion H2; subst; inversion H0.
    dependent induction H5; subst; eauto 3; clear IHbidityping.
    assert (Ha : And B C = And B0 C0) by (eapply In_unique; eauto); inversion Ha; subst.
    inversion H5; subst.
    assert (Ha1 : A0 = And B0 C0) by (symmetry; eauto); subst.
    inversion H6; subst.
    assert (Ha1 : ~ (Sub C0 A /\ Sub B0 A)) by eauto.
    exfalso; apply Ha1; split; assumption.
    inversion H0.
  - inversion H0; subst.
    inversion H0; subst; auto.
    inversion H5.
    inversion H5.
    reflexivity.
Qed.

(** Call-by-value lambda calculus **)

Inductive STValue : SExp -> Prop :=
  | STValue_Lam' :
      forall t1, STTerm (STLam' t1) -> STValue (STLam' t1)
  | STValue_Lam :
      forall t1 A, STTerm (STLam A t1) -> STValue (STLam A t1)
  | STValue_Lit : forall n, STValue (STLit n)
  | STValue_Unit : STValue STUnit
  | STValue_Pair : forall v1 v2, STValue v1 -> STValue v2 -> STValue (STPair v1 v2).


Inductive STred : SExp -> SExp -> Prop :=
  | red_beta' : forall t1 t2,
      STTerm (STLam' t1) ->
      STValue t2 ->
      STred (STApp (STLam' t1) t2) (t1 ^^ t2)
  | red_beta : forall t1 t2 A,
      STTerm (STLam A t1) ->
      STValue t2 ->
      STred (STApp (STLam A t1) t2) (t1 ^^ t2)
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

Hint Constructors STValue STred.

Lemma value_regular : forall e,
  STValue e -> STTerm e.
Proof. induction 1; autos*. Qed.

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
  - apply_fresh STTyLam' as y.
    rewrite* subst_open_var. apply_ih_bind* H0.
Qed.


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

(** Theorem 3. Progress: all typeable terms can reduce. **)

Theorem typeable_terms_reduce_chk :
  forall t A, bidityping empty t Chk A ->
         (exists B, In (PAnn t B) B) \/ (exists t', red (PAnn t A) t').
Proof.
  introv Typ.
  dependent induction Typ.
  - left*.
  - destruct (decidability_types A B).
    subst.
    admit.
    admit.
Admitted.

Theorem typeable_terms_reduce_inf :
  forall t A m, bidityping empty t m A -> (exists B, In t B) \/ (exists t', red t t').
Proof.  
  introv Typ. gen_eq E: (empty:env PTyp). lets Typ': Typ.
  induction Typ; intros; substs*.
  - false* binds_empty_inv.
  - right. destruct~ IHTyp1 as [[C v1] | [t1' Red1]];
    destruct~ IHTyp2 as [[D v2] | [t2' Red2]]; autos*.
    admit.
    admit.
  - destruct~ IHTyp1 as [[C v1] | [t1' Red1]];
    destruct~ IHTyp2 as [[D v2] | [t2' Red2]]; autos*.
  - destruct~ IHTyp as [[C v] | [t' Red]].
    assert (Ha : Sub C A) by eauto.
    admit. (* maybe a separate lemma for this? *)
    admit. (* split proof whether (PAnn t1 A) is a value or not? *)
  - admit. (* stuck... *)
Admitted.

(** Theorem 4. Direct semantics are equivalent to elaboration semantics. **)

Definition relation := SExp -> SExp -> Prop.

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t,
      STTerm t ->
      star_ R t t
  | star_trans : forall t2 t1 t3,
      star_ R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3
  | star_step : forall t t',
      R t t' -> star_ R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

Definition relation_source := PExp -> PExp -> Prop.

Inductive star_source (R : relation_source) : relation_source :=
  | star_refl_src : forall t,
      PTerm t ->
      star_source R t t
  | star_trans_src : forall t2 t1 t3,
      star_source R t1 t2 -> star_source R t2 t3 -> star_source R t1 t3
  | star_step_src : forall t t',
      R t t' -> star_source R t t'.

Notation "R 'star'" := (star_ R) (at level 69).

Theorem red_equiv :
  forall Gamma e A c, has_type_source_alg Gamma e Inf A c ->
             forall v, star_ STred c v -> STValue v ->
                  forall B v', star_source red e v' -> In v' B ->
                          forall c', has_type_source_alg Gamma v' Inf A c' ->
                                c' = v.
Proof.
Admitted.

