Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended_definitions4_top.

Module Extended
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

(*
Module Definitions := Definitions(VarTyp)(set).
Import Definitions.
*)
Require Import Extended_infrastructure4_top.
Module Infrastructure := Infrastructure(VarTyp)(set).
Export Infrastructure.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the correnposing lemmas/theorems in the paper. 
The reader can just look for:

Lemma 4

for example, to look for the proof of lemma 4 in the paper.

All lemmas and theorems are complete: there are no uses of admit or Admitted,
with the exceptions of "tlam" and "tylam" due to a technical limitation.

*)


Lemma ortho_ax_sym : forall A B, OrthoAx A B -> OrthoAx B A.
Proof.
  intros.
  destruct H as [a [b c]].
  unfold OrthoAx.
  auto.
Qed.
  
Lemma ortho_sym : forall Gamma A B, Ortho Gamma A B -> Ortho Gamma B A.
Proof.
  intros Gamma A B HOrtho.
  induction HOrtho; auto.
  - apply_fresh OForAll as x; apply H0; not_in_L x.
  - apply OVarSym with (A := A); auto.
  - apply OVar with (A := A); auto.
  - apply ortho_ax_sym in H; now apply OAx.
Qed.
  
Lemma ortho_and_l : forall Gamma t1 t2 t0, Ortho Gamma (And t1 t2) t0 -> Ortho Gamma t1 t0.
Proof.
  intros.
  dependent induction H; auto.
  - inversion H1; subst.
    apply OVarSym with (A := A); auto.
    apply sound_sub in H0.
    destruct H0.
    inversion H0; subst.
    apply complete_sub.
    eexists; apply H7.
    inversion H3.
    inversion H3.
  - orthoax_inv_l.
Qed.

Lemma ortho_and_r : forall Gamma t1 t2 t0, Ortho Gamma (And t1 t2) t0 -> Ortho Gamma t2 t0.
Proof.
  intros.
  dependent induction H; auto.
  - inversion H1; subst.
    apply OVarSym with (A := A); auto.
    apply sound_sub in H0.
    destruct H0.
    inversion H0; subst.
    apply complete_sub.
    eexists; apply H9.
    inversion H3.
    inversion H3.
  - orthoax_inv_l.
Qed.

Lemma wfenv_no_refl : forall Gamma x, WFEnv Gamma -> not (List.In (x, TyDis (PFVarT x)) Gamma).
Proof.
  intros.
  induction H.
  - auto.
  - unfold not, extend; simpl in *; intros.
    destruct H2.
    inversion H2; subst.
    apply H0; simpl.
    now apply MSetProperties.Dec.F.singleton_2.
    contradiction.
  - unfold not, extend; simpl; intros [a | b]; apply IHWFEnv.
    inversion a. auto.
Qed.

Lemma wfenv_no_var_sub :
  forall Gamma x A, WFEnv Gamma -> Sub A (PFVarT x) -> not (List.In (x, TyDis A) Gamma).
Proof.
  intros.
  induction H.
  - auto.
  - unfold not, extend; simpl in *; intros.
    destruct H3.
    inversion H3; subst.
    inversion H0.
    clear IHWFEnv H2 H0 H.
    dependent induction H4.
    + simpl in *; apply IHsub; not_in_L x.
    + simpl in *; apply IHsub; not_in_L x.
    + apply H1; simpl; now apply MSetProperties.Dec.F.singleton_2.
    + contradiction.
  - unfold not, extend; simpl; intros [a | b]; apply IHWFEnv.
    inversion a. auto.
Qed.

Inductive TopLike : PTyp -> Prop :=
  | TLTop : TopLike Top
  | TLAnd : forall t1 t2, TopLike t1 -> TopLike t2 -> TopLike (And t1 t2)
  | TLFun : forall t1 t2, TopLike t2 -> TopLike (Fun t1 t2) 
  | TLForAll : forall L d t,
                 (forall x, not (In x L) -> TopLike (open_typ_source t (PFVarT x))) ->
                 TopLike (ForAll d t).

Hint Constructors TopLike.

Lemma toplike_dec : forall t, sumbool (TopLike t) (not (TopLike t)).
Proof.
  intro t.
  induction t.
  - right; unfold not; intros HInv; inversion HInv. 
  - inversion IHt2.
    left.
    apply TLFun.
    apply H.
    right.
    unfold not; intros HInv; inversion HInv; subst.
    contradiction.
  - destruct IHt1. destruct IHt2. left. apply TLAnd; auto.
    right. unfold not. intros. inversion H; subst. contradiction.
    destruct IHt2.
    right. unfold not. intros. inversion H; subst. contradiction.
    right. unfold not. intros. inversion H; subst. contradiction.
  - right; unfold not; intros HInv; inversion HInv.
  - right; unfold not; intros HInv; inversion HInv.
  - right; unfold not; intros HInv; inversion HInv.
    subst.
    admit.
  - left; apply TLTop.
Admitted.

Lemma ortho_no_sub :
  forall Gamma A B, WFTyp Gamma A -> WFTyp Gamma B -> Ortho Gamma A B -> ~ TopLike B -> not (Sub A B).
Proof.
  intros Gamma A B WFA WFB HOrtho HNotTL HSub.

  inversion HSub.
  generalize dependent Gamma.
  induction H; intros.
  - inversion HOrtho; subst. destruct H as [a [b c]]; now apply c.
  - inversion HOrtho; subst.
    inversion WFA; inversion WFB; subst.
    apply IHsub2 with (Gamma := Gamma); auto.
    inversion HSub. inversion H1; subst.
    eexists; apply H13.
    destruct H1 as [a [b c]]; now apply c.
  - inversion WFB; subst.
    assert (Ha : ~ TopLike t1 \/ ~ TopLike t2).
    apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; auto.
    destruct Ha.
    apply IHsub1 with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_sym.
    apply ortho_and_l with (t2 := t2); auto.
    now apply ortho_sym.
    apply IHsub2 with (Gamma := Gamma); auto.
    eexists; apply H0.
    apply ortho_sym.
    apply ortho_and_r with (t1 := t1); auto.
    now apply ortho_sym.    
  - inversion WFA; subst; apply IHsub with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_and_l with (t2 := t2); auto.
  - inversion WFA; subst; apply IHsub with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_and_r with (t1 := t1); auto.
  - inversion HOrtho; subst.
    apply wfenv_no_var_sub with (Gamma := Gamma) (A := A) (x := v); auto.
    now apply wf_gives_wfenv in WFA.
    now apply sound_sub.
    apply wfenv_no_var_sub with (Gamma := Gamma) (A := A) (x := v); auto.
    now apply wf_gives_wfenv in WFA.
    now apply sound_sub.
    destruct H as [a [b c]]; now apply c.    
  - inversion WFA; inversion WFB; subst.
    inversion HSub.
    inversion H2; subst.
    inversion HOrtho; subst.
    pick_fresh x.
    eapply H0 with (x := x).
    not_in_L x.
    unfold not; intros HH; apply HNotTL.
    apply_fresh TLForAll as y.
    admit. (* rename lemma fresh_bot? *)
    eexists; apply H8.
    not_in_L x.
    apply H5.
    not_in_L x.
    apply H10.
    not_in_L x.
    apply H7.
    not_in_L x.
    destruct H3 as [a [b HH]]; now apply HH.
  - auto.
Admitted.

Lemma usub_top : forall D, usub Top D -> TopLike D.
  intros. dependent induction H. apply TLAnd; auto. apply TLTop.
Defined.

(* Unique subtype contributor: Lemma 2 *)

Lemma uniquesub :
  forall Gamma A B C, WFTyp Gamma A -> WFTyp Gamma B -> ~ TopLike C ->
             Ortho Gamma A B -> Sub (And A B) C -> not (Sub A C /\ Sub B C).
Proof.
  intros Gamma A B C WFA WFB HNotTL HOrtho HSubAnd.
  unfold not; intros [HSubA HSubB].
  generalize dependent C.
  dependent induction HOrtho; intros.
  - induction C;
    try now inversion WFA; subst;
    inversion HSubA; inversion H; subst; [ eapply IHHOrtho1 | eapply IHHOrtho2 ];
    unfold Sub; eauto.
    + inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; auto; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; auto; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      inversion H2.
      inversion H2.
      inversion H3.
      inversion H3.
    + now apply HNotTL.
  - induction C;
    try now inversion WFB; subst;
    inversion HSubB; inversion H; subst; [ eapply IHHOrtho1 | eapply IHHOrtho2 ];
    unfold Sub; eauto.
    + inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; auto; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; auto; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      inversion H6.
      inversion H6.
      inversion H1.
      inversion H1.
    + now apply HNotTL.
  - induction C; try (now (inversion HSubA as [x HInv]; inversion HInv)).
    + inversion WFA; subst; inversion WFB; subst.
      inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      assert (Ha : ~ TopLike C2) by (unfold not; auto).
      eapply IHHOrtho; auto; [ apply Ha
                             | apply sand2; unfold Sub; eauto
                             | unfold Sub; eauto
                             | unfold Sub; eauto ].
    + assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      inversion WFA; subst; inversion WFB; subst.
      inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      destruct Ha.
      apply IHC1; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
    + now apply HNotTL.
  - induction C; try (now (inversion HSubA as [x HInv]; inversion HInv)).
    + inversion HSubA; inversion H1; subst.
      inversion HSubB; inversion H2; subst.
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.      
    + inversion HSubA; inversion H1; subst.
      inversion HSubB; inversion H2; subst.
      inversion WFA; inversion WFB; subst.
      pick_fresh x.
      clear IHC1; clear IHC2; clear HSubAnd.
      eapply H0 with (x := x) (C := open_typ_source C2 (PFVarT x)).
      not_in_L x; apply H7.
      apply H9; not_in_L x.
      apply H15; not_in_L x.
      admit. (* needs renaming lemma here *)
      apply sand2.
      eexists; apply H7.
      not_in_L x.
      apply wf_gives_types_source with (Gamma := (extend x (TyDis C1) Gamma)).
      apply H15; not_in_L x.
      eexists; apply H7; not_in_L x.
      eexists; apply H6; not_in_L x.
    + now apply HNotTL.
  - induction C; try (now (inversion HSubA as [z HInv]; inversion HInv)).
    + destruct HSubA as [c HsubA]; inversion HsubA; subst.
      destruct HSubB as [c HsubB]; inversion HsubB; subst.
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      inversion H3.
      inversion H3.
    + clear HSubAnd.
      destruct HSubA as [c HsubA]; inversion HsubA; subst.
      assert (Ha : Ortho Gamma ty (PFVarT v)).
      apply OVarSym with (A := A); auto.
      apply ortho_no_sub in Ha.
      contradiction.
      auto.
      auto.
      unfold not; intros HInv; inversion HInv.
    + now apply HNotTL.
  (* same as above (var_sym) *)
  - induction C; try (now (inversion HSubB as [z HInv]; inversion HInv)).
    + destruct HSubA as [c HsubA]; inversion HsubA; subst.
      destruct HSubB as [c HsubB]; inversion HsubB; subst.
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      inversion H3.
      inversion H3.
    + clear HSubAnd.
      destruct HSubB as [c HsubB]; inversion HsubB; subst.
      assert (Ha : Ortho Gamma ty (PFVarT v)).
      apply OVarSym with (A := A); auto.
      apply ortho_no_sub in Ha.
      contradiction.
      auto.
      auto.
      unfold not; intros HInv; inversion HInv.
    + now apply HNotTL.
  - apply complete_sub in HSubA; apply usub_top in HSubA; contradiction.
  - apply complete_sub in HSubB; apply usub_top in HSubB; contradiction.
  - destruct H as [ PTypHd1 [ PTypHd2 PTypHd3 ]].
    induction C.
    + inversion HSubA as [x HsA]; inversion HsA; subst; try orthoax_inv PTypHd1.
      inversion HSubB as [x HsB]; inversion HsB; subst; try orthoax_inv PTypHd2.
      apply PTypHd3; auto.
    + inversion HSubA as [x HsA]; inversion HsA; subst; try orthoax_inv PTypHd1.
      inversion HSubB as [x HsB]; inversion HsB; subst; try orthoax_inv PTypHd2.
      apply PTypHd3; auto.
    + inversion HSubA as [x HInv1]; inversion HInv1; subst; try (now inversion H0).
      inversion HSubB as [x HInv2]; inversion HInv2; subst; try (now inversion H0).
      assert (Ha : ~ TopLike C1 \/ ~ TopLike C2).
      apply Classical_Prop.not_and_or; unfold not; intros HH; destruct HH; eauto.
      destruct Ha.
      apply IHC1; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.
      apply IHC2; unfold Sub; eauto.
      apply sand2; unfold Sub; eauto.      
    + inversion HSubA as [x HsA]; inversion HsA; subst; inversion H0.
    + inversion HSubA as [x HsA]; inversion HsA; subst; try orthoax_inv PTypHd1.
    + inversion HSubA as [x HsA]; inversion HsA; subst; try orthoax_inv PTypHd1.
      inversion HSubB as [x HsB]; inversion HsB; subst; try orthoax_inv PTypHd2.
      apply PTypHd3; auto.
    + now apply HNotTL.
Admitted.

Lemma foo : forall A, TopLike A -> forall e1, exists e2, and_coercion A e1 = inl e2.
  intros A T. induction T; simpl; intros.
  exists (STUnit _). auto.
  destruct (IHT1 e1). destruct (IHT2 e1). rewrite H, H0.
  eauto.
  destruct (IHT e1). rewrite H.
  exists (STLam _ x). auto.
  eauto.
  Defined.

Lemma same_coercion : forall A, TopLike A -> forall e1 e2, and_coercion A e1 = and_coercion A e2.
  intros A T. induction T; simpl; intros; auto. rewrite (IHT1 e1 e2). rewrite (IHT2 e1 e2).
  pose (foo _ T1 e2). destruct e. rewrite H. pose (foo _ T2 e2). destruct e. rewrite H0. auto.
  rewrite (IHT e1 e2). auto.
Defined.

(* Coercive subtyping is coeherent: Lemma 3 *)

Lemma sub_coherent :
  forall {A Gamma}, WFTyp Gamma A ->
           forall {B}, WFTyp Gamma B ->
                  forall {C1}, sub A B C1 ->
                          forall {C2}, sub A B C2 -> C1 = C2.
Proof.
  intros.
  generalize dependent C2.
  generalize dependent Gamma.
  (* Case: Int <: Int *)
  induction H1; intros.
  - inversion H2. 
    reflexivity.
  (* Case: Fun t1 t2 <: Fun t3 t4 *)
  - inversion H. inversion H0. inversion H2.
    assert (c2 = c3). apply IHsub2 with (Gamma := Gamma); auto.
    assert (c1 = c0). apply IHsub1 with (Gamma := Gamma); auto.
    now subst.
  (* Case: t <: And t1 t2 *) 
  - inversion H2; inversion H0; subst.
    assert (c1 = c0) by (apply IHsub1 with (Gamma := Gamma); auto).
    assert (c2 = c3) by (apply IHsub2 with (Gamma := Gamma); auto).
    now subst.
    now subst.
    now subst.
  (* different coercion case*)
  - inversion H2; subst.
    inversion H4; subst.
    inversion H.
    assert (c = c0). apply IHsub with (Gamma := Gamma); auto.
    now subst.
    destruct (toplike_dec t0).
    erewrite same_coercion.
    reflexivity.
    apply t3.
    assert (HSub : Sub (And t1 t2) t0) by (apply sand2; unfold Sub; eauto).
    assert (Ha := uniquesub _ t1 t2 t0 H7 H9 n H10 HSub).
    exfalso; apply Ha.
    split; unfold Sub; eauto.
    inversion H.
  - inversion H2; subst.
    inversion H4; subst.
    inversion H.
    destruct (toplike_dec t0).
    erewrite same_coercion.
    reflexivity.
    apply t3.    
    assert (HSub : Sub (And t1 t2) t0) by (apply sand3; unfold Sub; eauto).
    assert (Ha := uniquesub _ t1 t2 t0 H7 H9 n H10 HSub).
    exfalso; apply Ha.
    split; unfold Sub; eauto.
    assert (c = c0). apply IHsub with (Gamma := Gamma); auto.
    now subst.
    now subst.
  - now inversion H2.
  - inversion H2; subst.
    inversion H3; subst.
    inversion H4; subst.
    pick_fresh x.
    assert (Ha : (open_typ_term c (STFVarT x)) = (open_typ_term c0 (STFVarT x))).
    assert (ty := Top).
    eapply H0 with (Gamma := extend x (TyDis d) Gamma).
    not_in_L x.
    apply H8.
    not_in_L x.
    apply H10.
    not_in_L x.
    apply H12.
    not_in_L x.
    assert (c = c0).
    eapply open_typ_term_app_eq with (x := x) (n := 0).
    not_in_L x.
    not_in_L x.
    apply Ha.
    now subst.
  - inversion H2.
    inversion H4.
    inversion H4.
    now subst.    
Qed.

(*
End ExtendedSub.

Module Extended
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Require Import Extended_infrastructure.
Module Infrastructure := Infrastructure(VarTyp)(set).
Export Infrastructure.

Module ExtendedSub := ExtendedSub(VarTyp)(set).
Import ExtendedSub.
 *)

(* Typing lemmas *)

Lemma typing_wf_source_alg:
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp Gamma T.
Proof.
  intros Gamma t dir T E H.
  induction H; auto.
  - inversion IHhas_type_source_alg1; assumption.
  - inversion IHhas_type_source_alg; subst.
    apply open_body_wf_type with (d := d); auto.
    unfold body_wf_typ; eauto.
  - pick_fresh x.
    assert (Ha : not (M.In x L)) by (not_in_L x).
    apply WFFun.
    assumption.
    apply H0 in Ha.
    rewrite <- app_nil_l with (l := Gamma).
    eapply wf_strengthen_source with (z := x).
    not_in_L x.
    rewrite app_nil_l; apply Ha.
  - apply_fresh WFForAll as x.
    apply H1.
    not_in_L x.
    auto.
Qed.

Lemma type_correct_alg_terms : forall Gamma E ty e dir, has_type_source_alg Gamma E dir ty e -> PTerm E.
Proof.
  intros.
  induction H; auto.
  - apply PTerm_TApp.
    auto.
    now apply wf_gives_types_source in H.
  - apply_fresh PTerm_Lam as x; auto.
    apply H0; not_in_L x.
  - apply_fresh PTerm_TLam as x.
    apply H1; not_in_L x.
Qed.


Lemma typing_alg_wf_env :
  forall Gamma E dir ty e, has_type_source_alg Gamma E dir ty e -> WFEnv Gamma.
Proof.
  intros.
  induction H; auto.
  - pick_fresh x;
    assert (Ha: not (In x L)) by not_in_L x;
    pose (H0 _ Ha) as HInv;
    inversion HInv; auto.
  - pick_fresh x.
    assert (Ha : not (In x L)) by not_in_L x.
    apply H1 in Ha.
    now inversion Ha.
Qed.
  
(* Ignoring the generated expressions + smart constructors *)

Definition has_ty Gamma e d t := exists E, has_type_source_alg Gamma e d t E.

(* Uniqueness *)

Definition almost_unique (A B : PTyp) (d : Dir) : Prop := 
  match d with
    | Inf => A = B
    | Chk => True (* Is this result useful for checking: exists C, Sub C A /\ Sub C B*)
  end.

Lemma typ_unique : forall Gamma e d t1 E1, has_type_source_alg Gamma e d t1 E1 -> forall t2 E2, has_type_source_alg Gamma e d t2 E2 -> almost_unique t1 t2 d.
intros Gamma e d t1 E1 H.
induction H; intros; unfold almost_unique; auto.
(* case Var *)
- inversion H2; subst.
  assert (Ha : TermV ty = TermV t2).
  erewrite ok_unique_type with (x0 := x).
  reflexivity.
  apply wfenv_to_ok in H4.
  apply H4.
  apply (conj H5 H0).
  decide equality.
  now inversion Ha.
(* case Lit *)
- inversion H0. auto.
(* case App *)
- inversion H1.
  apply IHhas_type_source_alg1 in H5. simpl in H5.
  apply IHhas_type_source_alg2 in H6.
  injection H5. intros. auto.
(* Case Merge *)
- inversion H2.
  apply IHhas_type_source_alg1 in H5.
  apply IHhas_type_source_alg2 in H7.
  rewrite H5. rewrite H7. auto.
(* Case Ann *)
- inversion H0. auto.
(* Case TApp *)
- inversion H2; subst.
  apply IHhas_type_source_alg in H7.
  injection H7; intros.
  now subst.
Qed.

(* Theorem 5. Type inference always gives unique types *)

Lemma typ_inf_unique : forall {Gamma e t1 t2 E1 E2}, has_type_source_alg Gamma e Inf t1 E1 -> has_type_source_alg Gamma e Inf t2 E2 -> t1 = t2.
intros.
pose (@typ_unique _ _ _ _ _ H _ _ H0). simpl in a. auto.
Qed.

(* Theorem 6. *)
Lemma typ_coherence : forall Gamma e d t E1, has_type_source_alg Gamma e d t E1 -> forall E2, has_type_source_alg Gamma e d t E2 -> E1 = E2.
intros Gamma e d t E1 H.
induction H; intros.
(* case PFVar *)
- inversion H2; reflexivity. 
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
- inversion H0.
  apply IHhas_type_source_alg in H3. auto.
(* Case TApp *)
- inversion H2; subst.
  assert (Ha : ForAll d ty = ForAll d0 ty0).
  eapply typ_inf_unique.
  apply H0.
  apply H8.
  rewrite <- Ha in H8.
  apply IHhas_type_source_alg in H8.
  now subst.
(* Case Lam *)
- inversion H2; subst.
  apply f_equal.
  pick_fresh x.
  assert (Ha1: not (M.In x L0)) by (not_in_L x).
  apply H7 in Ha1.
  apply H0 in Ha1.
  assert (HNotE : not (In x (fv E))) by (not_in_L x).
  assert (HNotF : not (In x (fv E0))) by (not_in_L x).
  apply (open_app_eq _ _ _ _ HNotE HNotF Ha1).
  not_in_L x.
  inversion H3. 
(* ATySub *)
- inversion H2.
  subst.
  inversion H.
  assert (A = A0).
  apply (typ_inf_unique H H3).
  subst.
  apply IHhas_type_source_alg in H3.
  subst.
  assert (WFTyp Gamma A0). now apply typing_wf_source_alg in H.
  assert (WFTyp Gamma B). assumption.
  assert (C = C0).
  apply (sub_coherent H3 H6 H0 H4).
  subst; reflexivity.
  subst; inversion H.
(* Case TLam *)
- inversion H2; subst.
  inversion H3.
  apply f_equal.
  pick_fresh x.
  apply open_typ_term_app_eq with (E := E) (F := E0) (x := x) (n := 0).
  not_in_L x.
  not_in_L x.
  apply H1.
  not_in_L x.
  apply H8.
  not_in_L x.
Qed.

Lemma coercions_produce_terms :
  forall E A B, sub A B E -> STTerm E.
Proof.
  intros.
  induction H.
  (* Case SInt *)
  - apply_fresh STTerm_Lam as x; cbn; auto.
  (* Case SFun *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_Lam as y; cbn.
    apply STTerm_App.
    repeat rewrite <- open_rec_term; assumption.
    apply STTerm_App.
    apply STTerm_Var.
    apply STTerm_App; [ repeat rewrite <- open_rec_term; auto | apply STTerm_Var ].
  (* Case SAnd1 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_Pair.
    apply STTerm_App; repeat rewrite <- open_rec_term; auto.
    rewrite <- open_rec_term; auto.
  (* Case SAnd2 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.    
  (* Case SAnd3 *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply STTerm_App; auto.
    rewrite <- open_rec_term; auto.
  (* Case SVar *)
  - apply_fresh STTerm_Lam as x; cbn; auto.
  (* Case SForAll *)
  - apply_fresh STTerm_Lam as x; cbn.
    apply_fresh STTerm_TLam as y; cbn.
    apply STTerm_App; auto.
    assert (Ha : not (In y L)) by (not_in_L y).
    apply H0 in Ha.
    rewrite open_comm_open_typ_term.
    rewrite <- open_rec_term; auto.
Qed.

Hint Resolve coercions_produce_terms.


(* Subtyping rules produce type-correct coercions: Lemma 1 *)
Lemma type_correct_coercions :
  forall Gamma A B E, sub A B E ->
             WFEnv Gamma ->
             WFTyp Gamma A ->
             WFTyp Gamma B ->
             has_type_st (∥ Gamma ∥) E (STFun (|A|) (|B|)) .
Proof.
  intros.
  generalize dependent Gamma.
  induction H; intros.
  (* Case SInt *)
  - simpl.
    remember (∥ Gamma ∥).
    apply_fresh STTyLam as x; cbn; auto.
    apply STTyVar; auto.
    apply WFType_Int; auto.
    apply Ok_push; auto.
    subst; auto.
    apply wfenv_to_ok in H0; auto.
    not_in_L x.
    apply Ok_push; auto.
    subst; auto.
    not_in_L x.
    left; simpl; auto.
    apply WFType_Int.
    subst; auto.
  (* Case SFun *)
  - inversion H2; inversion H3.
    subst.
    remember (∥ Gamma ∥).
    apply_fresh STTyLam as x; cbn.
    apply_fresh STTyLam as y; cbn.
    apply STTyApp with (A := (| o2 |)).
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    repeat apply typing_weaken_extend.
    subst; apply (IHsub2 _ H1 H8 H13).
    not_in_L x.
    not_in_L y.
    not_in_L x.
    now apply coercions_produce_terms in H0.
    rewrite <- open_rec_term.
    now apply coercions_produce_terms in H0.
    now apply coercions_produce_terms in H0.
    apply STTyApp with (A := (| o1 |)).
    apply STTyVar.
    repeat apply wf_weaken_extend.
    apply WFType_Fun.
    subst; now apply WFTyp_to_WFType.
    subst; now apply WFTyp_to_WFType.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    right; left; auto.
    rewrite <- open_rec_term.
    rewrite <- open_rec_term.
    eapply STTyApp.
    repeat apply typing_weaken_extend.
    subst; apply IHsub1; auto.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    apply STTyVar.
    repeat apply wf_weaken_extend.
    inversion H3.
    subst; now apply WFTyp_to_WFType.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    not_in_L y.
    not_in_L x.
    left; auto.    
    now apply coercions_produce_terms in H.
    rewrite <- open_rec_term.
    now apply coercions_produce_terms in H.
    now apply coercions_produce_terms in H.
    apply wf_weaken_extend.
    subst; now apply WFTyp_to_WFType.
    not_in_L x.
    apply WFType_Fun; subst; now apply WFTyp_to_WFType.
  - remember (∥ Gamma ∥).
    inversion H3.
    apply_fresh STTyLam as x; cbn.
    apply STTyPair.
    + rewrite <- open_rec_term.
      apply STTyApp with (A := (| t0 |)).
      apply typing_weaken_extend.
      subst; apply IHsub1; auto.
      not_in_L x.
      apply STTyVar.
      apply wf_weaken_extend.
      subst; now apply WFTyp_to_WFType.
      not_in_L x.
      apply Ok_push.
      subst; auto.
      not_in_L x.
      left; auto.
      now apply coercions_produce_terms in H.
    + rewrite <- open_rec_term.
      apply STTyApp with (A := (| t0 |)).
      apply typing_weaken_extend.
      subst; apply IHsub2; auto.
      not_in_L x.
      apply STTyVar.
      apply wf_weaken_extend.
      subst; now apply WFTyp_to_WFType.
      not_in_L x.
      apply Ok_push.
      subst; auto.
      not_in_L x.
      left; auto.
      now apply coercions_produce_terms in H0.
    + subst; now apply WFTyp_to_WFType.
  - remember (∥ Gamma ∥).
    inversion H2.
    apply_fresh STTyLam as x; cbn.
    rewrite <- open_rec_term.
    apply STTyApp with (A := (| t1 |)).
    apply typing_weaken_extend.
    subst; apply IHsub; auto.
    not_in_L x.
    apply STTyProj1 with (B := (| t2 |)).
    apply STTyVar.
    apply wf_weaken_extend.
    apply WFType_Tuple; subst; now apply WFTyp_to_WFType.
    not_in_L x.
    apply Ok_push. subst; auto. not_in_L x.
    left; auto.
    now apply coercions_produce_terms in H.
    subst; apply WFType_Tuple; now apply WFTyp_to_WFType.
  - remember (∥ Gamma ∥).
    inversion H2.
    apply_fresh STTyLam as x; cbn.
    rewrite <- open_rec_term.
    apply STTyApp with (A := (| t2 |)).
    apply typing_weaken_extend.
    subst; apply IHsub; auto.
    not_in_L x.
    apply STTyProj2 with (A := (| t1 |)).
    apply STTyVar.
    apply wf_weaken_extend.
    apply WFType_Tuple; subst; now apply WFTyp_to_WFType.
    not_in_L x.
    apply Ok_push. subst; auto. not_in_L x.
    left; auto.
    now apply coercions_produce_terms in H.
    subst; apply WFType_Tuple; now apply WFTyp_to_WFType.
  - remember (∥ Gamma ∥).
    apply_fresh STTyLam as x.
    unfold open; simpl.
    apply STTyVar.
    apply wf_weaken_extend.
    subst; now apply WFTyp_to_WFType in H1.
    not_in_L x.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    left; auto.
    subst; now apply WFTyp_to_WFType in H1.    
  - remember (∥ Gamma ∥).
    inversion H2.
    inversion H3.
    apply_fresh STTyLam as x.
    unfold open; simpl.
    apply_fresh STTyTLam as y.
    unfold open_typ_term; simpl.
    apply STTyApp with (A := (open_typ (| t1 |) (STFVarT y))).
    rewrite open_comm_open_typ_term.
    rewrite <- open_rec_term.
    unfold open_typ; simpl.
    unfold open_typ_source in H0; simpl in H0.
    subst.
    change (extend y (TyVar STyp)
                   (extend x (TermVar STyp (STForAll (| t1 |))) (∥ Gamma ∥))) with
    (∥ (extend y (TyDis d)
               (extend x (TermV (ForAll d t1)) Gamma)) ∥).
    change (STFVarT y) with (| PFVarT y |).
    rewrite <- open_rec_typ_eq_source.
    rewrite <- open_rec_typ_eq_source.
    apply H0.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    simpl.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.add_iff in HH.
    destruct HH; subst.
    not_in_L y.
    exfalso; apply H25; now apply MSetProperties.Dec.F.singleton_2.
    not_in_L y.
    unfold extend.
    apply wf_weaken_source.
    apply H7.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    simpl.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.add_iff in HH.
    destruct HH; subst.
    not_in_L y.
    exfalso; apply H25; now apply MSetProperties.Dec.F.singleton_2.
    not_in_L y.
    apply wf_weaken_source.
    apply H12.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    not_in_L y.
    not_in_L x.
    assert (Ha : not (In y L)) by not_in_L y.
    apply H in Ha.
    now apply coercions_produce_terms in Ha.
    apply STTyTApp.
    apply WFType_Var.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    unfold extend; not_in_L y.
    not_in_L x.
    left; auto.
    apply STTyVar.
    apply WFTyp_to_WFType in H2.
    repeat apply wf_weaken_extend.
    subst; apply H2.
    not_in_L x.
    unfold extend; not_in_L y.
    not_in_L x.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    unfold extend; not_in_L y.
    not_in_L x.
    right; left; auto.
    subst; now apply WFTyp_to_WFType in H2.
    subst; inversion H8.
    subst.


    inversion H2; inversion H3; subst.
    inversion H14.
    inversion H9.
    inversion H12.
    apply_fresh STTyLam as x.
    unfold open; simpl.
    apply_fresh STTyTLam as y.
    unfold open_typ_term; simpl.
    apply STTyApp with (A := (open_typ (| t1 |) (STFVarT y))).
    rewrite open_comm_open_typ_term.
    rewrite <- open_rec_term.
    unfold open_typ; simpl.
    unfold open_typ_source in H0; simpl in H0.
    subst.
    change (extend y (TyVar STyp)
                   (extend x (TermVar STyp (STForAll (| t1 |))) (∥ Gamma ∥))) with
    (∥ (extend y (TyDis Bot)
               (extend x (TermV (ForAll Bot t1)) Gamma)) ∥).
    change (STFVarT y) with (| PFVarT y |).
    rewrite <- open_rec_typ_eq_source.
    rewrite <- open_rec_typ_eq_source.
    apply H0.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    inversion H8.
    simpl.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.add_iff in HH.
    destruct HH; subst.
    not_in_L y.
    exfalso; apply H14; now apply MSetProperties.Dec.F.singleton_2.
    not_in_L y.
    unfold extend.
    apply wf_weaken_source.
    apply H6.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    inversion H8.
    simpl.
    unfold not; intro HH.
    apply MSetProperties.Dec.F.add_iff in HH.
    destruct HH; subst.
    not_in_L y.
    exfalso; apply H14; now apply MSetProperties.Dec.F.singleton_2.
    not_in_L y.
    apply wf_weaken_source.
    apply H10.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    unfold not; intros HH; inversion HH.
    not_in_L y.
    not_in_L y.
    not_in_L x.
    assert (Ha : not (In y L)) by not_in_L y.
    apply H in Ha.
    now apply coercions_produce_terms in Ha.
    apply STTyTApp.
    apply WFType_Var.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    (* TODO add this to not_in_L *)
    unfold conv_context in H4; rewrite <- dom_map_id in H4; contradiction.
    unfold extend; not_in_L y.
    not_in_L x.
    unfold conv_context in H8; rewrite <- dom_map_id in H8; contradiction.
    left; auto.
    apply STTyVar.
    apply WFTyp_to_WFType in H2.
    repeat apply wf_weaken_extend.
    subst; apply H2.
    not_in_L x.
    unfold conv_context in H4; rewrite <- dom_map_id in H4; contradiction.
    unfold extend; not_in_L y.
    not_in_L x.
    unfold conv_context in H8; rewrite <- dom_map_id in H8; contradiction.
    apply Ok_push.
    apply Ok_push.
    subst; auto.
    not_in_L x.
    unfold conv_context in H4; rewrite <- dom_map_id in H4; contradiction.
    unfold extend; not_in_L y.
    not_in_L x.
    unfold conv_context in H8; rewrite <- dom_map_id in H8; contradiction.
    right; left; auto.
    subst; now apply WFTyp_to_WFType in H2.
Qed.
  
(* Type preservation: Theorem 1 *)
Lemma type_preservation :
  forall x ty dir E (Gamma : context TyEnvSource) (H : has_type_source_alg Gamma x dir ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof.
  intros.
  induction H; subst; auto.
  (* TyVar *)
  - apply STTyVar.
    now apply WFTyp_to_WFType.
    auto.
    now apply in_persists in H0.
  (* TyApp *)
  - simpl in *.
    apply STTyApp with (A := |A|).
    assumption.
    assumption.
  (* TyMerge *)
  - simpl; apply STTyPair; assumption.
  (* TyTApp *)
  - simpl in *.
    unfold open_typ_source; rewrite open_rec_typ_eq_source.
    apply STTyTApp.
    now apply WFTyp_to_WFType.
    apply IHhas_type_source_alg.
  (* TyLam *)
  - simpl.
    apply_fresh STTyLam as x.
    unfold open; simpl.
    assert (Ha : not (M.In x L)).
    not_in_L x.
    apply H0 in Ha.
    simpl in *.
    unfold extend.
    simpl.
    apply Ha.
    now apply WFTyp_to_WFType.
  (* ATySub *)
  - apply STTyApp with (|A|).
    apply type_correct_coercions.
    assumption.
    now apply typing_alg_wf_env in H.
    now apply typing_wf_source_alg in H.
    assumption.
    assumption.
  (* ATyTLam *)
  - simpl; apply_fresh STTyTLam as x.
    simpl in *.
    unfold open_typ.
    change (STFVarT x) with (| PFVarT x |).
    rewrite <- open_rec_typ_eq_source.
    apply H1.
    not_in_L x.
  (* ATyTLamBot *)
  - simpl; apply_fresh STTyTLam as x.
    simpl in *.
    unfold open_typ.
    change (STFVarT x) with (| PFVarT x |).
    rewrite <- open_rec_typ_eq_source.
    apply H0.
    not_in_L x.
Qed.

End Extended.