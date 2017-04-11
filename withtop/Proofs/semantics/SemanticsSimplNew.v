
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
                 red (PApp v1 v2) (PApp v1 (PAnn v2 A))
  | Red_App4 : forall A B v e,
                 In v (Fun A B) ->
                 red (PApp v (PLam e)) (PApp v (PAnn (PLam e) A))
  | Red_App5 : forall A B e v,
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
  | Red_Ann6 : forall v A B C,
                 In v C ->
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
  - (* R_App4 *)
    dependent induction Htyping; eauto; clear IHHtyping1 IHHtyping2.
    inverts* H; inverts* Htyping1.
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
    + dependent induction H1; eauto.
  - inverts* H2.
    + assert (Ha : Fun A B = Fun A1 B0) by (eapply In_unique; eauto); subst; auto.
      inverts* Ha.
    + assert (Ha : Fun A1 B0 = Fun A B) by (eapply In_unique; eauto).
      inversion Ha; subst.
      assert (Ha1 : A = C) by (eapply In_unique; eauto); subst.
      exfalso; apply H1; auto.
  - dependent induction H0; eauto.
    assert (Ha : Fun A B = Fun A0 B0) by (eapply In_unique; eauto).
    inverts* Ha.
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
  - inverts* H0; inverts* H5.
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

Hint Resolve value_regular.

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

Lemma In_dec : forall t, (exists B, In t B) \/ (~ exists B, In t B).
Proof.
  intro t; induction t;
  try now (right; unfold not; intros [H1 H2]; inversion H2).
  - destruct IHt1 as [[B H1] | H1]; destruct IHt2 as [[C H2] | H2]; autos*;
    right; unfold not; intros [H3 H4]; inverts* H4.
  - destruct IHt as [[B H] | H].
    right; unfold not; intros [H3 H4]; inverts* H4.
    inverts H.
    destruct t; try (now right; unfold not; intros [H3 H4]; inverts* H4).
    destruct (decidability_types p PInt); subst*.
    right; unfold not; intros [H3 H4]; inverts* H4.
    destruct p; autos*.
    right*; unfold not; intros [H3 H4]; inverts* H4.
    right*; unfold not; intros [H3 H4]; inverts* H4.
Qed.    

Lemma value_ann_red : forall A B t, Sub A B ->
                     In t A ->
                     exists t', red (PAnn t B) t'.
Proof.
  introv HSub HIn.
  gen B.
  induction HIn; intros.
  - destruct HSub; inverts* H.
  - destruct HSub; inverts* H.
  - destruct HSub; inverts H.
    autos*.
    eexists; eapply Red_Ann4 with (B := A); eauto.
    eexists; eapply Red_Ann5 with (C := B); eauto.
Qed.

Hint Resolve value_ann_red.

Theorem typeable_terms_reduce :
  forall t A m, bidityping empty t m A ->
           ((m = Inf -> In t A \/ (exists t', red t t')) /\
            (m = Chk -> In (PAnn t A) A \/ (exists t', red (PAnn t A) t'))).
Proof.
  introv Typ.
  gen_eq E: (empty:env PTyp). lets Typ': Typ.
  induction Typ; intros; substs; split; introv HH; try now inversion HH.
  - false* binds_empty_inv.
  - autos*.
  - right.
    forwards* [H1 _] : IHTyp1 Typ1.
    forwards* [_ H2] : IHTyp2 Typ2.
    assert (Ha : Chk = Chk) by auto.
    destruct (H1 HH) as [ HIn1 | [t1' Hred1]];
      destruct (H2 Ha) as [ HIn2 | [t2' Hred2]]; autos*.
    inverts* HIn1.
    inverts* HIn2.
    inverts* HIn1.
    destruct (In_dec t2).
    destruct H as [C H]; destruct (decidability_types C A); substs*.
    clear IHTyp1 IHTyp2.
    inverts* Hred2; tryfalse*.
  - forwards* [H1 _] : IHTyp1 Typ1.
    forwards* [H2 _] : IHTyp2 Typ2.
    destruct (H1 HH) as [ HIn1 | [t1' Hred1]];
    destruct (H2 HH) as [ HIn2 | [t2' Hred2]]; autos*.
  - forwards* [_ H1] : IHTyp Typ.
  - inverts* Typ'.
  - forwards* [H1 _] : IHTyp Typ.
    assert (Ha : Inf = Inf) by auto.
    destruct (H1 Ha) as [ HIn | [t' Hred] ].
    right; clear IHTyp Ha HH H1.
    autos*.
    destruct (In_dec (PAnn t B)).    
    destruct H2; inverts* H2.
    right; eexists; eauto.
Qed.
    
(******
    lambda-calculus reduction properties 
    (deterministic, similar to Dunfield's formalization).
*******)

Definition relation := SExp -> SExp -> Prop.

Inductive star_ (R : relation) : relation :=
  | star_refl : forall t, STTerm t -> star_ R t t
  | star_trans : forall t2 t1 t3,
      R t1 t2 -> star_ R t2 t3 -> star_ R t1 t3.

Notation "R *" := (star_ R) (at level 69).

Hint Constructors star_.

Lemma stred_regular1 : forall e1 e2, STred e1 e2 -> STTerm e1.
Proof. introv H; induction* H. Qed.

Lemma stred_regular2 : forall e1 e2, STred e1 e2 -> STTerm e2.
Proof. introv H; induction* H. admit. admit. inverts* H. inverts* H. Qed.

Hint Resolve stred_regular1 stred_regular2.

Lemma red_star_regular1 : forall e1 e2, star_ STred e1 e2 -> STTerm e1.
Proof. introv H; induction* H. Qed.

Lemma red_star_regular2 : forall e1 e2, star_ STred e1 e2 -> STTerm e2.
Proof. introv H; induction* H. Qed.

Hint Resolve red_star_regular1 red_star_regular1.

Hint Extern 1 => match goal with
                  | [ HH : STred (STLam' ?t) _ |- _ ] => inversion HH
                  | [ HH : STred (STLit ?t) _ |- _ ] => inversion HH
                  | [ HH : STred STUnit _ |- _ ] => inversion HH
                  | [ HH : STred (STLam ?A ?t) _ |- _ ] => inversion HH
                 end.

Lemma stvalue_not_red : forall v, STValue v -> forall e1, STred v e1 -> False.
Proof. introv H; induction* H; intros; inverts* H1. Qed.

Hint Resolve stvalue_not_red.

Lemma stred_unique : forall c e1, STred c e1 -> 
                             forall e2, STred c e2 ->
                                   e1 = e2.
Proof.
  introv H1.
  induction H1; intros.
  - dependent induction H1; autos*; tryfalse*.   
  - dependent induction H1; autos*; tryfalse*.
  - dependent induction H0; autos*; tryfalse*.
    assert (t1' = t1'0); eauto; substs*.
  - dependent induction H0; autos*; tryfalse*.
    assert (t2' = t2'0); eauto; substs*.
  - dependent induction H0; autos*; tryfalse*.
    assert (t1' = t1'0); eauto; substs*.
  - dependent induction H0; autos*; tryfalse*.
    assert (t2' = t2'0); eauto; substs*.
  - dependent induction H; autos*; tryfalse*.
    assert (t1' = t1'0); eauto; substs*.
  - dependent induction H0; autos*; tryfalse*.
  - dependent induction H; autos*; tryfalse*.
    assert (t1' = t1'0); eauto; substs*.
  - dependent induction H0; autos*; tryfalse*.
Qed.

Hint Resolve stred_unique.

(* TODO move this elsewhere *)
Lemma elaboration_regular :
  forall Gamma e A m E, has_type_source_alg Gamma e m A E -> STTerm E.
Proof.
  introv Typ. apply type_preservation in Typ. apply* typing_gives_terms.
Qed.

Hint Resolve elaboration_regular.

Lemma stvalue_redstar_refl : forall v, STValue v -> forall v', star_ STred v v' -> v = v'.
Proof.
  introv H1 H2.
  induction* H2.
  tryfalse*.
Qed.

Hint Resolve stvalue_redstar_refl.

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

Hint Constructors equiv_.

Lemma star_trans' : forall t1 t2, star_ STred t1 t2 ->
                     forall t3, star_ STred t2 t3 -> star_ STred t1 t3.
Proof. introv H; induction H; intros; autos*. Qed.

Lemma progress_star :
  forall t T, has_type_st empty t T -> (exists t', star_ STred t t' /\ STValue t').
Proof.
  introv Typ.
  lets* Ha : progress_result_stlc Typ.
Admitted.

Lemma prod_star_l :
  forall t1 t2, star_ STred t1 t2 ->
           forall t, STTerm t -> star_ STred (STPair t1 t) (STPair t2 t).
Proof. introv H; induction H; intros; substs*. Qed. 

Lemma prod_star_r :
  forall t1 t2, star_ STred t1 t2 ->
           forall t, STValue t -> star_ STred (STPair t t1) (STPair t t2).
Proof. introv H; induction H; intros; substs*. Qed. 

Lemma app_star_l :
  forall t1 t2, star_ STred t1 t2 ->
           forall t, STTerm t -> star_ STred (STApp t1 t) (STApp t2 t).
Proof. introv H; induction H; intros; substs*. Qed. 

Lemma app_star_r :
  forall t1 t2, star_ STred t1 t2 ->
           forall t, STValue t -> star_ STred (STApp t t1) (STApp t t2).
Proof. introv H; induction H; intros; substs*. Qed. 

Lemma star_equiv_l : forall e1 e2, star_ STred e1 e2 -> equiv_ STred e1 e2.
Proof. introv Star; induction* Star. Qed.

Lemma star_equiv_r : forall e1 e2, star_ STred e2 e1 -> equiv_ STred e1 e2.
Proof. introv Star; induction* Star. Qed.

Hint Resolve star_equiv_l star_equiv_r.

Lemma equiv_app_l : forall e1 e2, equiv_ STred e1 e2 -> forall e3, STTerm e3 -> equiv_ STred (STApp e1 e3) (STApp e2 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Lemma equiv_app_val : forall e2 e3, equiv_ STred e2 e3 -> forall e1, STValue e1 -> equiv_ STred (STApp e1 e2) (STApp e1 e3).
Proof. introv Equiv; induction* Equiv. Qed.  

Lemma equiv_app_r : forall e2 e3, equiv_ STred e2 e3 -> forall e1 A, has_type_st empty e1 A -> equiv_ STred (STApp e1 e2) (STApp e1 e3).
Proof.
  introv Equiv; induction* Equiv; intros.
  lets* [e2 [Hred Hval]] : progress_star H0.
  apply equiv_trans with (t2 := STApp e2 t).
  apply* equiv_app_l.
  apply equiv_trans with (t2 := STApp e2 t').
  apply* equiv_app_val.
  apply* equiv_app_l.
Qed.

Lemma equiv_pair_l : forall e1 e2, equiv_ STred e1 e2 -> forall e3, STTerm e3 -> equiv_ STred (STPair e1 e3) (STPair e2 e3).
Proof. introv Equiv; induction* Equiv. Qed.

Lemma equiv_pair_val : forall e2 e3, equiv_ STred e2 e3 -> forall e1, STValue e1 -> equiv_ STred (STPair e1 e2) (STPair e1 e3).
Proof. introv Equiv; induction* Equiv. Qed.  

Lemma equiv_pair_r : forall e2 e3, equiv_ STred e2 e3 -> forall e1 A, has_type_st empty e1 A -> equiv_ STred (STPair e1 e2) (STPair e1 e3).
Proof.
  introv Equiv; induction* Equiv; intros.
  lets* [e2 [Hred Hval]] : progress_star H0.
  apply equiv_trans with (t2 := STPair e2 t).
  apply* equiv_pair_l.
  apply equiv_trans with (t2 := STPair e2 t').
  apply* equiv_pair_val.
  apply* equiv_pair_l.
Qed.

Lemma consistency :
  forall e A c1 m, has_type_source_alg empty e m A c1 ->
              forall e', red e e' ->
                    forall c2, has_type_source_alg empty e' m A c2 ->
                         equiv_ STred c1 c2.
Proof.
  introv Typ.
  gen_eq E: (empty:env PTyp). lets Typ': Typ.
  induction* Typ; intros; substs.
  - inverts* H3.
  - inverts* H1. inverts* H2. inverts* H3. inverts* H0. inverts* H1.
    apply star_equiv_r; apply* star_trans; unfold open; simpl; case_nat*.
  - inverts H0.
    + inverts* H1.
      assert (HH : exists c, has_type_source_alg empty e3 Inf (Fun A B) c).
      apply soundness; apply completeness in Typ1; lets* Ha : subject_reduction Typ1.
      destruct HH.
      assert (Ha : Fun A0 B = Fun A B) by (eapply typ_inf_unique; eauto); inverts Ha; clear H.
      assert (E2 = E3) by apply* typ_coherence; subst.
      lets* Ha1 : IHTyp1 Typ1 H4 H3.
      apply* equiv_app_l.
    + inverts* H3. inverts* H1. inverts Typ1. inverts* H3.
      lets* Ha1 : IHTyp2 Typ2 H5 H4.
      assert (E0 = E1) by apply* typ_coherence; subst.
      lets Ha2 : type_preservation H6.
      unfold conv_context in Ha2; rewrite map_empty in Ha2; apply* equiv_app_r.
    + inverts H3. inverts Typ1. inverts H1. inverts H3.
      assert (E0 = E1) by apply* typ_coherence; subst.
      inverts H7.
      lets Ha2 : type_preservation H8; unfold conv_context in Ha2; rewrite map_empty in Ha2.
      apply* equiv_app_r.
      inverts H5; inverts H.
      admit. (* show E3 ~> E2 *)
      inverts H.
    + inverts* H4. inverts H1. inverts H4. inverts H3. inverts* Typ1.
      assert (E1 = E0) by apply* typ_coherence; subst.
      inverts H. inverts H9.
      assert (E = E2) by apply* typ_coherence; subst.
      lets Ha2 : type_preservation H6; unfold conv_context in Ha2; rewrite map_empty in Ha2.
      apply* equiv_app_r.       
      admit. (* show C ~> id *)
      inverts H.
    + inverts H1. inverts Typ1. inverts* Typ'. inverts* H8.
      clear H6 H9. clear IHTyp1 IHTyp2.
      admit. (* hard case: app. use body property on H2? *)
  - inverts* H2; inverts* H1.
    + lets* Ha1 : IHTyp1 Typ1 ___ H2.
      assert (E2 = E3) by apply* typ_coherence; subst.
      apply* equiv_pair_l.
    + lets* Ha1 : IHTyp2 Typ2 ___ H9.
      assert (E1 = E0) by apply* typ_coherence; subst.
      assert (A0 = A) by apply* In_bityping_eq; subst.
      lets Ha2 : type_preservation Typ1; unfold conv_context in Ha2; rewrite map_empty in Ha2.
      apply* equiv_pair_r.
  - (* there must be a better way of proving this subgoal, by exploiting the connection between the 
       Ann reduction and the subtyping rules *) 
    lets Ha : In_dec t1.
    destruct Ha as [ [ B HIn ] | Ha ].
    inverts Typ. inverts HIn. clear IHTyp.
    assert (A0 = B) by (symmetry; autos*). subst.
    gen t1 e'.
    induction H2; intros.
    + inverts H0; try now inversion HIn. tryfalse*.
      inverts HIn. inverts H. inverts H1.
      assert (E0 = c2) by apply* typ_coherence; subst.
      admit. (* looks easy *)
    + inverts H0; try now inversion HIn. tryfalse*.
      inverts HIn. inverts H. inverts H1. inverts H2; try now inverts H.
      clear IHsub1 IHsub2.
      pick_fresh x.
      lets* Ha : H6 x ___. clear H6.
      unfold open_source in Ha; simpls; case_nat; clear C.
      inverts Ha. inverts H0. inverts H8. inverts H0. inverts H11.
      assert (Ha1 : WFTyp A0). admit.
      assert (c0 = C0). eapply sub_coherent. apply Ha1. apply H5. auto. auto. subst; clear H2_0.
      admit.
    + inverts H0; try now inversion HIn. tryfalse*.
      assert (t = C) by apply* In_unique. subst. clear H7. clear IHsub1 IHsub2.
      inverts H1. inverts H7. inverts H2. inverts HIn.
      assert (C = A) by autos*. subst.
      assert (E0 = E) by apply* typ_coherence. substs.
      assert (Ha : WFTyp A) by autos*.
      inverts H3.
      assert (C0 = c1). eapply sub_coherent. apply Ha. apply H7. auto. auto. subst.
      inverts H8. inverts H6. inverts HIn.
      assert (A0 = A) by (symmetry; autos*). subst.
      assert (E0 = E) by apply* typ_coherence. substs.
      assert (c0 = C). eapply sub_coherent. apply Ha. apply H9. auto. auto. subst.
      admit. (* looks easy *)
    + inverts H0; try now inversion HIn.
      inverts HIn. clear IHsub.
      inverts H1; try now inversion H9.
      inverts H4. inverts H5. inverts H13.
      inverts H13; inverts* H0.
      inverts H15.
      assert (B = t1) by autos*.
      assert (C = t2) by autos*. substs. clear H8 H16.
      inverts H4. inverts H5. inverts H6.
      assert (t1 = A) by autos*. substs.
      assert (HWF : WFTyp A) by autos*.
      assert (C = c). eapply sub_coherent. apply HWF. apply H3. auto. auto. substs.
      assert (E1 = E) by apply* typ_coherence. substs.
      admit. (* looks easy *)
      inverts H15.
      assert (C = t2) by apply* In_unique. substs.
      destruct H9.
      assert (HSub : Sub (And t1 t2) t) by eauto.
      lets* Ha : uniquesub H11 HSub.
      exfalso; apply Ha; split*.
    + admit. (* similar to above *)
      
    + clear Typ'. assert (HH : WFTyp A) by autos*.
      gen E c2 Ha. gen_eq Exp: (PAnn t1 A:PExp). lets H0': H0.
      induction H0; intros; substs; try now inversion H.
      * inverts H2. inverts H1.
        lets* Ha2 : IHTyp Typ H0.
      * inverts H0; tryfalse*.
      * inverts H; tryfalse*.
      * inverts H1. inverts H2. tryfalse*.
      * inverts H1. inverts H2. tryfalse*.
      * inverts H0. tryfalse*. 
    (*
    clear Typ'. assert (HH : WFTyp A) by autos*.
    gen E c2. gen_eq Exp: (PAnn t1 A:PExp). lets H0': H0.
    induction H0; intros; substs; try now inversion H.
    + inverts H2. inverts H1.
      lets* Ha : IHTyp Typ H0.
    + clear IHTyp.
      inverts H0. inverts* H0'. clear H3. inverts H2. inverts* Typ.
      inverts H0. inverts* H2. inverts H1.
      assert (E0 = c2) by apply* typ_coherence; subst.
      asserts_rewrite (c2 = open (STBVar 0) c2). unfold open; simpls*; case_nat*.
      unfold open at 1; simpls*; case_nat.
      admit. (* looks easy *)
    + clear IHTyp. inverts H. inverts Typ. inverts H. inverts H0.
      inverts H5; try now inversion H.
      inverts H1. inverts H3; try now inversion H.
      inverts H0'. inverts H4.
      pick_fresh x.
      lets* Ha : H5 x ___.
      unfold open_source in Ha; simpls.
      inverts Ha; case_nat.
      inverts H0.
      inverts H12.
      inverts H0.
      inverts H15; inverts H16.
      inverts H0.
      inverts H16. inverts H19. inverts HH.
      assert (Ha : WFTyp A1). admit.
      assert (C2 = c0). eapply sub_coherent. apply Ha. apply H19. auto. auto. subst.
      assert (A2 = C). inverts H0; apply* binds_push_eq_inv. subst.
      assert (C4 = c1). eapply sub_coherent. apply H18. apply H22. auto. auto. subst.
      clear H14 H9.
      admit.
      inverts H16.
    + inverts H2. inverts H1. inverts Typ. inverts H1. inverts H3. clear H13.
      assert (B = A1) by autos*; subst.
      assert (C = B0) by autos*; subst.
      inverts* H2. inverts H0. clear IHTyp.
      inverts H7. inverts H6.
      assert (A1 = A0). eapply typ_inf_unique; eauto. subst.
      assert (E1 = E) by apply* typ_coherence; subst.
      assert (Ha : WFTyp A0) by autos*.
      assert (C = c). eapply sub_coherent. apply Ha. apply H4. auto. auto. subst.
      lets* Ha4 : type_correct_coercions H2 ___.
      apply equiv_trans with (t2 := (STApp c (STProj1 (STPair E E2)))).
      admit.
      apply* equiv_app_r.
      admit.
      admit. (* contradiction!! *)
    + admit. (* similar case to above *)
    + inverts H0. inverts H0'. inverts H1. inverts H7. inverts H8. clear H5 H7.
      assert (C0 = C) by apply* In_unique; subst; clear H2. clear IHTyp.
      inverts Typ; inverts H1; try now inversion H6.
      inverts H3. inverts H. inverts H4. inverts H.
      assert (A2 = A). eapply typ_inf_unique; eauto.
      assert (A1 = A). eapply typ_inf_unique; eauto. subst.
      assert (E0 = E) by apply* typ_coherence; subst.
      assert (E1 = E) by apply* typ_coherence; subst. clear H0 H3.
      assert (Ha : WFTyp A) by autos*.
      assert (C0 = c1). eapply sub_coherent. apply Ha. apply H6. auto. auto.
      assert (C1 = c2). eapply sub_coherent. apply Ha. apply H9. auto. auto.
      subst. clear H7 H5.
      admit. (* seems reasonable *)
  *)
  - lets* Ha : IHTyp Typ H2.
    inverts* H3.
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
    apply* equiv_app_r.
Admitted.


(***** Old and broken stuff *****)


Lemma consistency2 :
  forall e A c1 m, has_type_source_alg empty e m A c1 ->
              forall e', red e e' ->
                    forall c2, has_type_source_alg empty e' m A c2 ->
                         equiv_ STred c1 c2.
Proof.
  introv Typ Hred.
  gen A m c1.
  induction Hred; intros.
  - inverts Typ. inverts H. inverts H3. inverts H. inverts H0. admit.
    inverts H0. inverts H. inverts H0. inverts H7. inverts H.
Admitted.

Hint Extern 1 => match goal with
                  | H : Inf = Chk |- _ => inversion H
                  | H : Chk = Inf |- _ => inversion H
                end.

Lemma consistency_chk_stvalue :
  forall Gamma e A c, has_type_source_alg Gamma e Chk A c -> STValue c -> In (PAnn e A) A.
Proof.
  introv Typ.
  gen_eq E: (Chk:Dir). lets Typ': Typ.
  induction* Typ; intros; inverts* H2.
Qed.

Lemma consistency_inf_stvalue :
  forall Gamma e A c, has_type_source_alg Gamma e Inf A c -> STValue c ->
             exists e', star_source red e e' /\ In e' A /\
                   forall c', has_type_source_alg Gamma e' Inf A c' -> star_ STred c' c.
Proof.
  introv Typ.
  gen_eq E: (Inf:Dir). lets Typ': Typ.
  induction* Typ; intros; substs.
  - inverts* H3.
  - exists (PAnn (PLit x) PInt); repeat split*.
    introv H2. inverts* H2. inverts* H5. inverts* H2.
    inverts* H3.
    apply* star_trans; unfold open; simpl; case_nat*.
  - inverts* H0.
  - inverts H1.
    lets* [t3 [Ha1 [Ha2 Ha3]]] : IHTyp1 Typ1 H4. 
    lets* [t4 [Ha4 [Ha5 Ha6]]] : IHTyp2 Typ2 H5.
    exists (PMerge t3 t4).
    repeat split*.
    apply star_trans_source with (t2 := PMerge t3 t2). 
    apply* merge_star_l.
    apply* merge_star_r.
    introv HTyp2; inverts* HTyp2.
    lets* Ha7 : Ha6 H9.
    lets* Ha8 : Ha3 H8.
    apply star_trans' with (t2 := STPair E1 E3).
    apply* prod_star_l.
    apply* prod_star_r.
  - clear IHTyp.
    assert (In (PAnn t1 A) A) by apply* consistency_chk_stvalue.
    exists (PAnn t1 A).
    repeat split*.
    introv HTyp2.
    assert (E = c') by apply* typ_coherence; substs*.
Qed.    
    
Lemma consistency_inf_stvalue2 :
  forall Gamma e A c, has_type_source_alg Gamma e Inf A c -> STValue c ->
             exists e', star_source red e e' /\ In e' A.
Proof.
  introv Typ.
  gen_eq E: (Inf:Dir). lets Typ': Typ.
  induction* Typ; intros; substs.
  - inverts H3.
  - inverts H0.
  - inverts* H1.
    lets* [t3 [Ha1 Ha2]] : IHTyp1 Typ1 H4. 
    lets* [t4 [Ha3 Ha4]] : IHTyp2 Typ2 H5.
    exists (PMerge t3 t4).
    split*.
    apply star_trans_source with (t2 := PMerge t3 t2). 
    apply* merge_star_l.
    apply* merge_star_r.
  - inverts* Typ.
    inverts* H0.
Qed.  

Lemma consistency_value : forall Gamma e A E, has_type_source_alg Gamma e Inf A E -> In e A ->
                          exists E', star_ STred E E' /\ STValue E'.
Proof.
  introv Typ.
  gen_eq D: (Inf:Dir). lets Typ': Typ.
  induction* Typ; intros; substs.
  - inverts* H3.
  - inverts* H0.
  - inverts* H1.
    lets* [E3 [Ha1 Ha2]] : IHTyp1 Typ1 ___.
    lets* [E4 [Ha3 Ha4]] : IHTyp2 Typ2 ___.
    exists (STPair E3 E4). split*.
    apply star_trans' with (t2 := STPair E3 E2).
    apply* prod_star_l.
    apply* prod_star_r.    
  - inverts* H0. inverts* Typ. inverts* H0. inverts* H1.
    exists (STLit n). split*. apply* star_trans. unfold open; simpl; case_nat*.
    inverts Typ; try now inverts H0.
    exists* (STLam' E0).
Qed.
    
Theorem red_equiv :
  forall Gamma e A c, has_type_source_alg Gamma e Inf A c ->
             forall v, star_ STred c v -> STValue v ->
                  forall B v', star_source red e v' -> In v' B ->
                          forall c', has_type_source_alg Gamma v' Inf A c' ->
                                c' = v.
Proof.
  introv H1 H2 H3 H4 H5 H6.  
Admitted.

