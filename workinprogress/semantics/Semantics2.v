Require Import String.
Require Import CoherenceBasicBD.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Tactics.

Module Semantics
       (Import VarTyp : BooleanDecidableType')
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

Inductive AExp : PExp -> Prop :=
  | ALit : forall n, AExp (PLit n)
  | ALam : forall t, AExp (PLam t).

Inductive Value : PExp -> Prop :=
  | VAnn : forall a A, AExp a -> Value (PAnn RT a A)
  | VMerge : forall v1 v2, Value v1 -> Value v2 -> Value (PMerge v1 v2).

Inductive In : PExp -> PTyp -> Prop :=
  | InInt : forall n, In (PAnn RT (PLit n) PInt) PInt
  | InFun : forall e A B, In (PAnn RT (PLam e) (Fun A B)) (Fun A B)
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
  | Red_Int : forall n, red (PLit n) (PAnn RT (PLit n) PInt)
  | Red_Abs : forall e A B,
                red (PAnn CT (PLam e) (Fun A B))
                    (PAnn RT (PLam e) (Fun A B))
  | Red_App1 : forall e1 e2 e3,
                 red e1 e3 ->
                 red (PApp e1 e2) (PApp e3 e2)
  | Red_App2 : forall e1 e2 v,
                 Value v ->
                 red e1 e2 ->
                 red (PApp v e1) (PApp v e2)
  | Red_App3 : forall A B v1 v2,
                 Value v1 ->
                 Value v2 ->
                 In v1 (Fun A B) ->
                 not (In v2 A) ->
                 red (PApp v1 v2) (PApp v1 (PAnn CT v2 A))
  | Red_App4 : forall A B e v,
                 Value v ->
                 In v A -> 
                 red (PApp (PAnn RT (PLam e) (Fun A B)) v)
                     (PAnn CT (open_source e v) B)
  | Red_Merge1 : forall e1 e2 e3,
                   red e1 e3 ->
                   red (PMerge e1 e2) (PMerge e3 e2)
  | Red_Merge2 : forall e1 e2 v,
                   Value v ->
                   red e1 e2 ->
                   red (PMerge v e1) (PMerge v e2)
  | Red_Ann : forall e1 e2 A,
                red e1 e2 ->
                red (PAnn CT e1 A) (PAnn CT e2 A)
  | ARed_Int : forall n,
                    red (PAnn CT (PAnn RT (PLit n) PInt) PInt)
                        (PAnn RT (PLit n) PInt)
  | ARed_Fun :
      forall e A B C D,
        red (PAnn CT (PAnn RT (PLam e) (Fun A B)) (Fun C D))
            (PAnn RT (PLam (PAnn CT (PApp (PAnn RT (PLam e) (Fun A B))
                                          (PAnn CT (PBVar 0) A)) D))
                  (Fun C D))
  | ARed_Merge1 : forall v1 v2 A B,
                    Sub A B ->
                    Atomic B ->
                    Value v1 ->
                    Value v2 ->
                    In v1 A ->
                    red (PAnn CT (PMerge v1 v2) B)
                        (PAnn CT v1 B)
  | ARed_Merge2 : forall v1 v2 A B,
                    Sub A B ->
                    Atomic B ->
                    Value v1 ->
                    Value v2 ->
                    In v2 A ->
                    red (PAnn CT (PMerge v1 v2) B)
                        (PAnn CT v2 B)
  | ARed_Merge3 : forall v A B,
                    Value v ->
                    red (PAnn CT v (And A B))
                        (PMerge (PAnn CT v A) (PAnn CT v B)).


Hint Constructors typing bidityping AExp Value In WFTyp red.

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

(* We didn't prove this before?! *)
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

Theorem In_Ann_inv : forall a A B, AExp a -> In (PAnn RT a A) B -> A = B.
Proof. intros v A B H1 H2; dependent induction H2; auto. Qed.

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

Theorem In_sub_bityping :
  forall Gamma B A e, Sub A B ->
             In e A ->
             bidityping Gamma e Inf B ->
             bidityping Gamma e Inf A.
Proof.
  intros Gamma B A e HSub HIn Hbidi.
  generalize dependent A.
  induction Hbidi; intros; try now inversion HIn.
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

Hint Resolve In_sub_bityping.

Theorem In_bityping :
  forall Gamma A B e, In e A -> bidityping Gamma e Inf B -> bidityping Gamma e Inf A.
Proof.
  intros Gamma A B e HIn Htyping.
  assert (Sub A B) by eauto.
  eapply In_sub_bityping; eauto.
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

Definition body_bityping Gamma t A B :=
  exists L, forall x, not (ST.M.In x L) ->
            bidityping (ST.extend x A Gamma) (open_source t (PFVar x)) Chk B.

Hint Unfold body_bityping.

Lemma abs_to_body_bityping : forall A B e Gamma, 
  bidityping Gamma (PLam e) Chk (Fun A B) -> body_bityping Gamma e A B.
Proof. intros; inversion H; subst; eauto; inversion H0. Qed.

Lemma open_body_bityping :
  forall e A B u Gamma, body_bityping Gamma e A B -> WFTyp A ->
               bidityping Gamma (open_source e u) Chk B.
Proof.
  intros e A B u Gamma H1 H2; destruct H1. pick_fresh y.
  assert (Ha : not (ST.M.In y x)) by ST.not_in_L y; apply H in Ha.
  admit. (* needs subst, weakening, etc... *)
Admitted.

Hint Resolve open_body_bityping.

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
    dependent induction Htyping; subst; eauto.
    apply ATyApp' with (A := A); auto; clear IHHtyping1 IHHtyping2.
    + inversion Htyping1; subst; try now inversion H.
      inversion H1; subst.
      eauto.
    + apply bityping_inf_chk.
      apply ATyAnnCT'.
      inversion Htyping2; subst. inversion H0.
      assert (Ha : Sub (Fun A B) (Fun A0 B0)) by eauto.
      destruct Ha; inversion H6; subst.
      assert (Ha1 : Sub A0 A) by eauto.
      assert (Ha2 : Sub A1 A0) by eauto.
      assert (Ha3 : Sub A1 A) by eauto; destruct Ha3.
      eapply ATySub' with (A := A1); eauto 3.
      assert (Ha4 : bidityping Gamma v1 Inf (Fun A B)) by eauto.
      apply bityping_wf in Ha4; now inversion Ha4.
  - (* R_App4 *)
    dependent induction Htyping; subst; eauto.
    clear IHHtyping1 IHHtyping2.
    inversion Htyping1; subst.
    apply ATyAnnCT'; clear Htyping1.
    apply open_body_bityping with (A := A0); eauto.
    inversion H5; subst; eauto.
    inversion H1.
  - (* A_Abs *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H; subst.
    inversion H1; subst.
    apply ATyAnnRT'.     
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
    + apply ATyAnnRT'.
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
  - (* A_Merge1 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H4; subst.
    apply ATyAnnCT'.
    assert (Ha : bidityping Gamma v1 Inf A) by eauto.
    destruct H; eauto.
  - (* A_Merge2 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H4; subst.
    apply ATyAnnCT'.
    assert (Ha : bidityping Gamma v2 Inf B0) by eauto.
    destruct H; eauto.
  - (* A_Merge3 *)
    dependent induction Htyping; subst; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H2; subst.
    assert (HSub : Sub A0 (And A B)) by eauto.
    apply invAndS1 in HSub; destruct HSub; destruct H3; destruct H4.
    apply ATyMerge'; eauto.
Qed.

(** Theorem 2. All typeable terms can reduce **)

Theorem typeable_terms_reduce :
  forall e1 A, bidityping nil e1 Inf A -> exists e2, red e1 e2.
Proof.  
  intros e1 A H.
  dependent induction H; eauto.
  - inversion H0.
  - assert (Ha1 : exists e2 : PExp, red t1 e2) by eauto.
    destruct Ha1; eauto.
  - assert (Ha1 : exists e2 : PExp, red t1 e2) by eauto.
    assert (Ha2 : exists e2 : PExp, red t2 e2) by eauto. 
    destruct Ha1, Ha2; eauto.
  - assert (Ha1 : exists e2  : PExp, red t1 e2) by eauto.
    destruct Ha1; eauto.
  - assert (Ha1 : exists e2  : PExp, red t1 e2) by eauto.
    destruct Ha1.
    admit. (* missing assumption that terms do not contain RT anns? *)
  - admit. (* abs case *)
Admitted.

End Semantics.







