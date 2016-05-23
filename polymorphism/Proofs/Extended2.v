Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended_definitions.
Require Import Extended_infrastructure.

Module Extended
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

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
  intros.
  induction H; auto.
  - apply_fresh OForAll as x; apply H0; not_in_L x.
  - apply OVarSym with (A := A); auto.
  - apply OVar with (A := A); auto.
  - apply ortho_ax_sym in H; now apply OAx.
Qed.

Lemma ortho_and_l : forall Gamma t1 t2 t0, Ortho Gamma (And t1 t2) t0 -> Ortho Gamma t1 t0.
Proof.
  intros.
  dependent induction H.
  - auto.
  - auto.
  - apply OVarSym with (A := A); auto.
    inversion H1; inversion H2; subst.
    eexists; apply H6.
    inversion H4.
    inversion H4.
  - destruct H; inversion H; inversion H2; inversion H4;
    inversion H6; inversion H8; inversion H10.
Qed.

Lemma ortho_and_r : forall Gamma t1 t2 t0, Ortho Gamma (And t1 t2) t0 -> Ortho Gamma t2 t0.
Proof.
  intros.
  dependent induction H.
  - auto.
  - auto.
  - apply OVarSym with (A := A); auto.
    inversion H1; inversion H2; subst.
    eexists; apply H8.
    inversion H4.
    inversion H4.
  - destruct H; inversion H; inversion H2; inversion H4;
    inversion H6; inversion H8; inversion H10.
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
    
Lemma ortho_no_sub :
  forall Gamma A B, WFTyp Gamma A -> WFTyp Gamma B -> Ortho Gamma A B -> not (Sub A B).
Proof.
  intros Gamma A B WFA WFB HOrtho HSub.

  inversion HSub.
  generalize dependent Gamma.
  induction H; intros.
  - inversion HOrtho; subst; destruct H as [a [b c]]; now apply c.
  - inversion HOrtho; subst.
    inversion WFA; inversion WFB; subst.
    apply IHsub2 with (Gamma := Gamma); auto.
    inversion HSub. inversion H1; subst.
    eexists; apply H13.
    destruct H1 as [a [b c]]; now apply c.
  - inversion WFB; subst.
    apply IHsub1 with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_sym.
    apply ortho_and_l with (t2 := t2); auto.
    now apply ortho_sym.
  - inversion WFA; subst; apply IHsub with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_and_l with (t2 := t2); auto.
  - inversion WFA; subst; apply IHsub with (Gamma := Gamma); auto.
    eexists; apply H.
    apply ortho_and_r with (t1 := t1); auto.
  - inversion HOrtho; subst.
    apply wfenv_no_var_sub with (Gamma := Gamma) (A := A) (x := v); auto.
    apply wfenv_no_var_sub with (Gamma := Gamma) (A := A) (x := v); auto.
    destruct H as [a [b c]]; now apply c.    
  - inversion WFA; inversion WFB; subst.
    inversion HSub.
    inversion H1; subst.
    inversion HOrtho; subst.
    pick_fresh x.
    eapply H0 with (x := x).
    not_in_L x.
    eexists; apply H8.
    not_in_L x.
    apply H3.
    not_in_L x.
    apply H7.
    not_in_L x.
    apply H5.
    not_in_L x.
    destruct H2 as [a [b HH]]; now apply HH.
Qed.

(* Unique subtype contributor: Lemma 2 *)

Lemma uniquesub :
  forall Gamma A B C, WFTyp Gamma A -> WFTyp Gamma B ->
             Ortho Gamma A B -> Sub (And A B) C -> not (Sub A C /\ Sub B C).
Proof.
  intros Gamma A B C WFA WFB HOrtho HSubAnd.
  unfold not; intros [HSubA HSubB].
  generalize dependent C.
  dependent induction HOrtho; intros.
  - induction C;
    try (inversion WFA; subst;
         inversion HSubA; inversion H; subst; [
           eapply IHHOrtho1; auto; [ apply sand3; apply HSubB |
                                     eexists; apply H5 |
                                     auto ] | 
           eapply IHHOrtho2; auto; [ apply sand3; apply HSubB |
                                     eexists; apply H5 |
                                     auto ] ]).  
    + inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      apply IHC1.
      apply sand2.
      eexists; apply H3.
      eexists; apply H3.
      eexists; apply H6.
      inversion H2.
      inversion H2.
      inversion H5.
      inversion H5.
  - induction C; 
    try (inversion WFB; subst;
         inversion HSubB; inversion H; subst; [
           eapply IHHOrtho1; auto; [ apply sand2; apply HSubA |
                                     auto | 
                                     eexists; apply H5 ] | 
           eapply IHHOrtho2; auto; [ apply sand2; apply HSubA |
                                     auto |
                                     eexists; apply H5 ] ]). 
    + inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      apply IHC1.
      apply sand2.
      eexists; apply H3.
      eexists; apply H3.
      eexists; apply H6.
      inversion H8.
      inversion H8.
      inversion H1.
      inversion H1.
  - induction C; try (now (inversion HSubA as [x HInv]; inversion HInv)).
    + inversion WFA; subst; inversion WFB; subst.
      inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      eapply IHHOrtho; auto; [ apply sand2; eexists; apply H10
                             | eexists; apply H10
                             | eexists; apply H13 ].
    + inversion WFA; subst; inversion WFB; subst.
      inversion HSubA; inversion H; subst.
      inversion HSubB; inversion H0; subst.
      apply IHC1.
      apply sand2; eexists; apply H7.
      eexists; apply H7.
      eexists; apply H10.
  - induction C; try (now (inversion HSubA as [x HInv]; inversion HInv)).
    + inversion HSubA; inversion H1; subst.
      inversion HSubB; inversion H2; subst.
      apply IHC1.
      apply sand2; eexists; apply H5.
      eexists; apply H5.
      eexists; apply H8.
    + inversion HSubA; inversion H1; subst.
      inversion HSubB; inversion H2; subst.
      inversion WFA; inversion WFB; subst.
      pick_fresh x.
      clear IHC1; clear IHC2; clear HSubAnd.
      eapply H0 with (x := x).
      not_in_L x; apply H7.
      apply H5; not_in_L x.
      apply H11; not_in_L x.
      apply sand2.
      eexists; apply H7; not_in_L x.
      eexists; apply H7; not_in_L x.
      eexists; apply H8; not_in_L x.
  - induction C; try (now (inversion HSubA as [z HInv]; inversion HInv)).
    + inversion HSubA; inversion H2; subst.
      inversion HSubB; inversion H3; subst.
      apply IHC1.
      apply sand2; eexists; apply H6.
      eexists; apply H6.
      eexists; apply H9.
      inversion H5.
      inversion H5.
    + clear HSubAnd.
      inversion HSubA; inversion H2; subst.
      assert (Ha : Ortho Gamma ty (PFVarT v)).
      apply OVarSym with (A := A); auto.
      apply ortho_no_sub in Ha.
      contradiction.
      auto.
      auto.
  (* same as above (var_sym) *)
  - induction C; try (now (inversion HSubB as [z HInv]; inversion HInv)).
    + inversion HSubA; inversion H2; subst.
      inversion HSubB; inversion H3; subst.
      apply IHC1.
      apply sand2; eexists; apply H6.
      eexists; apply H6.
      eexists; apply H9.
      inversion H4.
      inversion H4.
    + clear HSubAnd.
      inversion HSubB; inversion H2; subst.
      assert (Ha : Ortho Gamma ty (PFVarT v)).
      apply OVarSym with (A := A); auto.
      apply ortho_no_sub in Ha.
      contradiction.
      auto.
      auto.
  - destruct H as [ PTypHd1 [ PTypHd2 PTypHd3 ]].
    induction C.
    + inversion HSubA; inversion H; subst;
      try now ( inversion PTypHd1; inversion H1; inversion H3;
                inversion H5; inversion H7; inversion H9).
      inversion HSubB; inversion H0; subst;
      try now ( inversion PTypHd2; inversion H2; inversion H4;
                inversion H6; inversion H8; inversion H10). 
      apply PTypHd3; auto.
    + inversion HSubA; inversion H; subst;
      try now ( inversion PTypHd1; inversion H3;
                inversion H5; inversion H7; inversion H9).
      inversion HSubB; inversion H0; subst;
      try now ( inversion PTypHd2; inversion H6; inversion H8;
                inversion H10; inversion H12; inversion H14). 
      apply PTypHd3; auto.
    + inversion HSubA as [x HInv1]; inversion HInv1; subst; try (now inversion H0).
      inversion HSubB as [x HInv2]; inversion HInv2; subst; try (now inversion H0).
      apply IHC1; [ apply sand2; eexists; apply H2
                  | eexists; apply H2
                  | eexists; apply H3 ].
    + inversion HSubA; inversion H; subst; inversion H1.
    + inversion HSubA; inversion H; subst;
      try now (inversion PTypHd1; inversion H3; inversion H5; inversion H7).
      inversion HSubB; inversion H0; subst;
      try now (inversion PTypHd2; inversion H4; inversion H6; inversion H8).
      apply PTypHd3; auto.
    + inversion HSubA; inversion H; subst;
      try now (inversion PTypHd1; inversion H3; inversion H5; inversion H7).
      inversion HSubB; inversion H0; subst;
      try now (inversion PTypHd2; inversion H5; inversion H7; inversion H9; inversion H11).
      apply PTypHd3; auto.
    + inversion HSubA; inversion H; subst;
      try now (inversion PTypHd1; inversion H3; inversion H5; inversion H7; inversion H9).
Qed.
  
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
  - inversion H0; subst.
    inversion H3; subst.
    inversion H.
    assert (c = c0). apply IHsub with (Gamma := Gamma). inversion H0; subst. auto. auto.
    now subst.
    now subst.
    assert (HSub : Sub (And t1 t2) t0) by (apply sand2; eexists; apply H1).
    assert (Ha := uniquesub _ t1 t2 t0 H6 H8 H9 HSub).
    exfalso; apply Ha.
    split; eexists; [apply H1 | apply H7].
  - inversion H0; subst.
    inversion H3; subst.
    inversion H.
    assert (HSub : Sub (And t1 t2) t0) by (apply sand3; eexists; apply H1).
    assert (Ha := uniquesub _ t1 t2 t0 H6 H8 H9 HSub).
    exfalso; apply Ha.
    split; eexists; [apply H7 | apply H1].
    assert (c = c0). apply IHsub with (Gamma := Gamma). inversion H0; subst. auto. auto.
    now subst.
    now subst.
  - now inversion H2.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    pick_fresh x.
    assert (Ha : (open_typ_term c (STFVarT x)) = (open_typ_term c0 (STFVarT x))).
    assert (ty := Bot).
    eapply H0 with (Gamma := extend x (TyDis ty) Gamma).
    not_in_L x.
    apply H6.
    not_in_L x.
    apply H7.
    not_in_L x.
    apply H10.
    not_in_L x.
    assert (c = c0).
    eapply open_typ_term_app_eq with (x := x) (n := 0).
    not_in_L x.
    not_in_L x.
    apply Ha.
    now subst.
Qed.

 
(* Typing lemmas *)

Lemma typing_wf_source_alg:
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp Gamma T.
Proof.
  intros Gamma t dir T E H.
  induction H; auto.
  - inversion IHhas_type_source_alg1; assumption.
  - inversion IHhas_type_source_alg; subst.
    apply open_body_wf_type with (d := d).
    unfold body_wf_typ.
    exists L.
    intros.
    apply H3.
    not_in_L x.
    auto.
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
    intros.
    admit.
Admitted.

Lemma typing_weaken_alg : forall G E F t T d dir,
   has_type_source_alg (E ++ G) t dir T d -> 
   ok (E ++ F ++ G) ->
   has_type_source_alg (E ++ F ++ G) t dir T d.
Proof.
Admitted. (*
  intros.
  generalize dependent H0.
  remember (E ++ G) as H'.
  generalize dependent HeqH'.
  generalize dependent E.
  dependent induction H; intros; eauto.
  (* TyVar *)
  - subst.
    apply ATyVar.
    assumption.
    apply in_app_or in H0.
    inversion H0.
    apply in_or_app; left; assumption.
    apply in_or_app; right; apply in_or_app; right; assumption.
    apply wf_weaken_source; assumption.
  (* TyTApp *)
  - subst; apply ATyTApp.
    apply wf_weaken_source; auto.
    auto.
  (* TyLam *)
  - unfold extend in *.
    apply_fresh ATyLam as x.
    unfold open in *; simpl in *.
    unfold extend.
    rewrite app_assoc.
    apply H0.
    not_in_L x.
    rewrite HeqH'.
    rewrite <- app_assoc.
    reflexivity.
    rewrite <- app_assoc.
    apply Ok_push.
    assumption.
    repeat (rewrite dom_union; rewrite M.union_spec).
    repeat rewrite M.union_spec in Frx.
    repeat rewrite or_assoc in *.
    unfold not; intro HInv; destruct HInv as [HInv | [HInv | HInv]]; apply Frx; auto 8.
    subst; apply wf_weaken_source; assumption.
  (* TySub *)
  - subst.
    apply ATySub with (A := A); auto.
    apply wf_weaken_source; assumption.
  (* TyTLam *)
  - subst.
    apply_fresh ATyTLam as x.
    intros.
    unfold open in *; simpl in *.
    subst.
    unfold extend; simpl.
    rewrite app_comm_cons.
    eapply H0.
    not_in_L x.
    unfold extend; simpl; reflexivity.
    rewrite <- app_comm_cons.
    apply Ok_push.
    assumption.
    not_in_L x.
    rewrite dom_union in H2.
    rewrite union_spec in H2.
    inversion H2; contradiction.
Qed.
*)

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
- inversion H1; subst.
  apply IHhas_type_source_alg in H6.
  injection H6; intros.
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
- inversion H1; subst.
  assert (Ha : ForAll d ty = ForAll d0 ty0).
  eapply typ_inf_unique.
  apply H0.
  apply H7.
  rewrite <- Ha in H7.
  apply IHhas_type_source_alg in H7.
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
  subst.
  inversion H.
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

(*
Lemma open_rec_term_core :
  forall t j v i u, i <> j -> open_rec_source j (PFVar v) t = open_rec_source i (PFVar u) (open_rec_source j (PFVar v) t) ->
    t = open_rec_source i (PFVar u) t.
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
Defined.
*)



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
    not_in_L y.
    apply MSetProperties.Dec.F.add_iff in H7.
    inversion H7; subst.
    exfalso; apply H20; now apply MSetProperties.Dec.F.singleton_2.
    contradiction.
    unfold extend.
    apply wf_weaken_source.
    apply H6.
    not_in_L y.
    apply WFPushV.
    apply WFPushT.
    auto.
    not_in_L x.
    not_in_L y.
    simpl.
    not_in_L y.
    apply MSetProperties.Dec.F.add_iff in H7.
    inversion H7; subst.
    exfalso; apply H20; now apply MSetProperties.Dec.F.singleton_2.
    contradiction.
    apply wf_weaken_source.
    apply H10.
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
Qed.

End Extended.