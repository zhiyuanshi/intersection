Require Import String.
Require Import STLC.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.
Require Import CoherenceTop.


Module TypeDifferenceModule
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module ST := TLC(VarTyp)(set).
Import ST.

Module CT := CoherenceTopModule(VarTyp)(set).
Export CT.

(*
(* TypSize for Measurement *)
Fixpoint TypSize (A: PTyp) :nat :=
  match A with
  | TopT | PInt => 1
  | And t1 t2 => TypSize t1 + TypSize t2
  end.

Lemma TypSize_lt_0 : forall (t:PTyp),
    0 < TypSize t.
Proof.
  intros t. induction t; auto.
  unfold TypSize.
  apply (plus_lt_compat 0 (TypSize t1) 0 (TypSize t2)).
  assumption. assumption.
Qed.

Lemma TypSize_And_spl : forall (t1 t2:PTyp),
   TypSize (And t1 t2) = TypSize t1 + TypSize t2.
Proof.
  intros.
  unfold TypSize.
  auto.
Qed.
     
Lemma TypSize_And_lt : forall (t1 t2: PTyp),
    TypSize t1 <  TypSize (And t1 t2). 
Proof.
  intros. 
  induction t1.
  - unfold TypSize.
    assert (1+0 < 1+ TypSize t2) as H.
    { apply plus_lt_compat_l. apply TypSize_lt_0. }
    auto.
  - rewrite -> TypSize_And_spl. rewrite -> TypSize_And_spl. rewrite -> TypSize_And_spl.
    rewrite <- Nat.add_assoc. rewrite Nat.add_comm. rewrite (Nat.add_comm (TypSize t1_1)  (TypSize t1_2 + TypSize t2)).
    apply plus_lt_le_compat.
    + assert (0 + TypSize t1_2 < TypSize t2 +  TypSize t1_2) as H.
      { apply plus_lt_le_compat. apply TypSize_lt_0. auto. }
      auto.
    + auto.
  - rewrite TypSize_And_spl.
     assert (0 + TypSize TopT < TypSize TopT + TypSize t2) as H.
     {rewrite (Nat.add_comm (TypSize TopT) (TypSize t2)).
      apply plus_lt_le_compat. apply TypSize_lt_0. auto. }
     auto.
Qed.
*)

Reserved Notation "t1 \ t2 \\ t" (at level 50, left associativity).
Inductive TypDiff: PTyp -> PTyp -> PTyp -> Prop :=  
  | DInt_lr:         forall (t: PTyp), PInt \ PInt \\ TopT   
  (* (A&&B)\te = (A\te) && (B\te) *)                                                        
  | DandTyp_l:       forall (t t1 t2 r1 r2: PTyp), (Atomic t) -> t1\t\\r1 -> t2\t\\r2 -> (And t1 t2)\t\\(And r1 r2)                                         
  | DTop_l:          forall (t: PTyp), (Atomic t) -> TopT \ t \\ TopT   
  (* te -> te\(A&&B) = (te\A)\B *)                                                             
  | DandTyp_r:       forall (t t1 r1 t2 r2:PTyp), t\t1\\r1 -> r1\t2\\r2 -> t\(And t1 t2)\\r2
  | DTop_r:          forall (t: PTyp), t \ TopT \\ t 
where "t1 \ t2 \\ t" := (TypDiff t1 t2 t) : TypExp_Scope.    
                                                           
  
Open Scope TypExp_Scope.

Example case1 :=  (And PInt PInt)\ PInt \\ And TopT TopT.
Example case2 :=  (And TopT PInt)\ PInt \\ And TopT TopT.
Example case3 :=  TopT \ (And PInt TopT) \\ TopT.


Definition deterministic3 {X: Type} (R: X -> X -> X -> Prop) :=
  forall x1 x2 y1 y2 : X, R x1 x2 y1 -> R x1 x2 y2 -> y1 = y2.


Lemma TypDiff_top_l : forall t t2 : PTyp, TopT \ t \\ t2 -> t2 = TopT.
Proof.
  intros. dependent induction H.
  + auto.
  + subst. auto.
  + auto.
Qed.

Lemma TypDiff_top_l_p : forall t : PTyp, TopT \ t \\ TopT.
Proof.
  intros. induction t0.
  + apply DTop_l. auto.
  + eapply DandTyp_r. apply IHt0_1. apply IHt0_2.
  + apply DTop_r.
Qed.
    
Lemma TypDiff_top_r : forall t r : PTyp,  t \ TopT \\ r -> r = t.
Proof.
  intros. dependent induction H; subst; auto.
  inversion H.
Qed.
   
Lemma TypDiff_int_int : forall t : PTyp, PInt \ PInt \\ t -> TopT = t.
Proof.
  intros. dependent induction H.
  + auto.
Qed.

(* Decidable *)
Theorem TypDiff_deterministic : deterministic3 TypDiff.
Proof.
  unfold deterministic3.
  intros x1 x2. generalize dependent x1. induction x2.
  -
    intros x1. induction x1.
    + intros.
    apply TypDiff_int_int in H; subst.
    apply TypDiff_int_int in H0. auto.
    + intros.
    inversion H; subst.
    inversion H0; subst.
    apply (IHx1_1 r1 r0) in H4; subst.
    apply (IHx1_2 r2 r3) in H10; subst.
    auto.
    assumption. assumption.
    +intros.
    inversion H; subst.
    inversion H0; subst.
    auto.
  - intros x1. induction x1.
    + intros.
      inversion H; subst.
      inversion H0; subst.
      apply (IHx2_1 PInt r1 r0) in H4; subst.
      apply (IHx2_2 r0).
       assumption. assumption. assumption.
    + intros.
      inversion H.
      inversion H3; inversion H8.
      subst.
      inversion H0. inversion H3; inversion H10. subst.
      apply (IHx2_1 (And x1_1 x1_2) r1 r0) in H4; subst.
      apply (IHx2_2 r0 y2 y1) in H8; subst.
      auto.
      assumption. assumption.
    + intros.
      apply TypDiff_top_l in H.
      apply TypDiff_top_l in H0.
      subst. auto.
  - intros x1.
    induction x1; intros; inversion H; inversion H0; auto.
    + assert (r1 = r0) as G1.
      { apply IHx1_1. assumption. assumption. }
      assert (r2 = r3) as G2.
      { apply IHx1_2. assumption. assumption. }
      subst. auto.
    + inversion H3.
    + inversion H5.
Qed.

Hint Resolve TypDiff_top_l TypDiff_top_l_p TypDiff_top_r TypDiff_int_int TypDiff_deterministic.


Lemma TypDiff_int_l : forall (A D: PTyp),
    (PInt \ A \\ D) ->  (D=TopT) \/ (D=PInt) .
Proof.
  intros. dependent induction H.
  - auto.
  - assert (PInt = PInt) as SH by auto;
    apply IHTypDiff1 in SH;
    inversion SH; subst.
    + apply TypDiff_top_l in H0.
      left. apply H0.
    + apply IHTypDiff2. auto.
  - right. auto.
Qed.


Lemma TypDiff_int_l_p : forall (A : PTyp),
    (PInt \ A \\ TopT) \/ (PInt \ A \\ PInt).
Proof.
  intro A.
  induction A; intros.
  - left. apply DInt_lr. apply TopT.
  - intros.
    destruct IHA1.
    + left.
      eapply DandTyp_r.
      apply H.
      apply TypDiff_top_l_p.
    + destruct IHA2; [ left | right];
        try eapply DandTyp_r; try apply H; try apply H0.
  - right. apply DTop_r.
Qed. 


Lemma TypDiff_and_l_meg : forall (A B C D E: PTyp),
    A \ C \\ D -> B \ C \\ E -> And A B \ C \\ And D E.
Proof.
  intros A B C. generalize dependent A. generalize dependent B.
  induction C.
  - intros. eapply DandTyp_l.
    auto.
    assumption. assumption.
  - intros.
    inversion H; subst; try inversion H1.
    inversion H0; subst; try inversion H1.
    
    eapply DandTyp_r.
    eapply IHC1.
    apply H4. apply H5.

    eapply IHC2.
    apply H6. apply H8.
  - intros.
    inversion H; subst; try inversion H1.
    inversion H0; subst; try inversion H1.
    apply DTop_r.
Qed.


(* Reversed *)
Lemma TypDiff_and_r_spl : forall (C D E F: PTyp),
    F \ C \\ And D E ->(exists (A B: PTyp), (F = And A B) /\ (A \ C \\ D) /\ (B \ C \\ E)).
Proof.
  intros.
  dependent induction C.
  - (* C = PInt *)
    dependent induction F.
    + (* F = PInt *)
      exfalso.
      inversion H.
    + (* F = And F1 F2 *)
      auto. exists F1. exists F2.
      split; auto; try split.
      * (* F1 \ PInt \\ D *)
        inversion H; subst; apply H6.
      * (* F2 \ PInt \\ E *)
        inversion H; subst; apply H7.
    + (* F = TopT *)
      exfalso.
      inversion H.
  - (* C = And C1 C2 *)
    inversion H; subst.
    + (* F = And t1 t2 *)
      exists t1. exists t2.
      inversion H2.
    + (* \ C1 \ C2 *)
      apply IHC2 in H5.
      inversion H5. inversion H0. inversion H1. inversion H4.
      clear H4 H1 H0 H5. subst.
      apply IHC1 in H3.
      inversion H3. inversion H0. inversion H1. inversion H4.
      clear H4 H1 H0 H3. subst.
      apply (DandTyp_r _ _ _ C2 D) in H5; auto.
      apply (DandTyp_r _ _ _ C2 E) in H8; auto.
      exists x1. exists x2. split; auto.
  - (* C = TopT *)
    inversion H; try inversion H2; subst.
    exists D. exists E. split; auto.
    split; apply DTop_r.
Qed.


Lemma TypDiff_and_l_and_r : forall (A B C F: PTyp),
    And A B \ C \\ F -> (exists (D E: PTyp), (F = And D E)).
Proof.
  intros A B C. generalize dependent A. generalize dependent B.
  induction C; intros; try inversion H; subst.
  - try exists r1; try exists r2; auto.
  - try exists r1; try exists r2; auto.                            
  - (* C = And C1 C2 *)
    auto.
    apply IHC1 in H3. inversion H3. inversion H0. clear H0 H3. subst.
    apply IHC2 in H5. inversion H5. inversion H0. clear H0 H5.
    exists x1. exists x2. auto.
  - exists r1. exists r2. auto.
  - exists A. exists B. auto.
Qed.     

Lemma TypDiff_and_l_spl : forall (A B C F: PTyp),
    And A B \ C \\ F -> (exists (D E: PTyp), (F = And D E) /\ (A \ C \\ D) /\ (B \ C \\ E)).
Proof.
  intros A B C. generalize dependent A. generalize dependent B.
  induction C; intros.
  - (* C = PInt *)
    dependent induction F.
    + (* F = PInt *)
      exfalso.
      inversion H.
    + (* F = And F1 F2 *)
      auto. exists F1. exists F2.
      split; auto; try split.
      * (* F1 \ PInt \\ D *)
        inversion H; subst; apply H6.
      * (* F2 \ PInt \\ E *)
        inversion H; subst; apply H7.
    + (* F = TopT *)
      exfalso.
      inversion H.
  - (* C = And C1 C2 *)
    remember H. clear Heqt0.
    apply TypDiff_and_l_and_r in H.
    inversion H; inversion H0; exists x; exists x0.
    split. auto.
    split.
    inversion t0; inversion H4; subst.
    apply IHC1 in H5.
    destruct H5. destruct H1. destruct H1. destruct H2.
    subst.
    apply IHC2 in H7.
    destruct H7. destruct H1. destruct H1. destruct H4.
    subst.
    apply (DandTyp_r _ _ _ C2 x3) in H2; auto.
    apply (DandTyp_r _ _ _ C2 x4) in H3; auto.
    inversion H1. auto.
    (* repeat for a similar goal *)
    inversion t0; inversion H4; subst.
    apply IHC1 in H5.
    inversion H5. inversion H1. inversion H2. inversion H4.
    clear H4 H2 H1 H5; subst.
    apply IHC2 in H7.
    inversion H7. inversion H1. inversion H2. inversion H4.
    clear H4 H2 H1 H7.
    apply (DandTyp_r _ _ _ C2 x3) in H6; auto.
    apply (DandTyp_r _ _ _ C2 x4) in H9; auto.
    inversion H3.
    auto.
  - (* C = TopT *)
    inversion H; try inversion H2; subst.
    exists A. exists B. split; auto.
    split; apply DTop_r.
Qed.


Theorem TypDiff_comm : forall (C A B D: PTyp), C\(And A B)\\D -> C\(And B A)\\D.
Proof.
  intros C. induction C; intros.
  - remember H as H_p; clear HeqH_p.
    apply TypDiff_int_l in H.
    destruct H; subst; inversion H_p; subst.
    + remember H2 as H2_p; clear HeqH2_p.
      apply TypDiff_int_l in H2.
      remember (TypDiff_int_l_p B) as HB; clear HeqHB.
      destruct HB.
      (* int -> top -> top *)
      * eapply DandTyp_r.
          apply H.
          apply (TypDiff_top_l_p A).
      * destruct H2.
        (* int -> int -> top *)
        {eapply DandTyp_r.
        apply H.
        subst. apply H2_p. }
        (* contra *)
        { exfalso.
          subst.
          assert (PInt = TopT) as CH.
          apply (TypDiff_deterministic PInt B PInt TopT).
          apply H. apply H4.
          inversion CH. }
    + remember (TypDiff_int_l_p B) as HB; clear HeqHB.
      destruct HB.
      * remember H2 as H2_p; clear HeqH2_p.
       apply TypDiff_int_l in H2.
       destruct H2; subst.
       { apply (TypDiff_top_l B) in H4.
         inversion H4. }
       { exfalso.
          subst.
          assert (PInt = TopT) as CH.
          apply (TypDiff_deterministic PInt B PInt TopT).
          apply H4. apply H.
          inversion CH. }
      * remember H2 as H2_p; clear HeqH2_p.
       apply TypDiff_int_l in H2.
       destruct H2; subst.
       { apply (TypDiff_top_l B) in H4.
         inversion H4. }
       { eapply DandTyp_r.
         apply H.
         apply H2_p. }
  - apply TypDiff_and_l_spl in H.
    inversion H; clear H; inversion H0; clear H0; inversion H; subst.
    inversion H1. clear H H1.
    apply IHC1 in H0.
    apply IHC2 in H2.
    apply (TypDiff_and_l_meg C1 C2 _ x x0) in H0; auto.
  - (* TopT *)
    apply TypDiff_top_l in H.
    rewrite H.
    apply TypDiff_top_l_p.
Qed.

Hint Resolve  TypDiff_int_l  TypDiff_int_l_p  TypDiff_and_l_meg  TypDiff_and_r_spl TypDiff_and_l_spl TypDiff_comm.


Theorem TypDiff_id : forall A B C D : PTyp,
    A \ B \\ C -> C \ D \\ A -> C = A.
Proof.
  intro A. induction A.
  - intros.
    apply (TypDiff_int_l _) in H.
    destruct H.
    + exfalso.
      subst.
      apply (TypDiff_top_l _) in H0.
      inversion H0.
    + assumption.
  - intros.
    apply TypDiff_and_l_spl in H.
    inversion H. inversion H1. inversion H2. inversion H4.
    clear H4 H2 H1.
    apply TypDiff_and_r_spl in H0.
    inversion H0. inversion H1. inversion H2. inversion H7.
    clear H7 H2 H1. subst.
    inversion H4. subst. clear H4.
    apply (IHA1 _ _ D) in H5; auto.
    apply (IHA2 _ _ D) in H6; auto.
    rewrite H5. rewrite H6.
    auto.
  - (* TopT *)
    intros.
    apply TypDiff_top_l in H.
    auto.
Qed.

Lemma TypDiff_and_m_spl : forall (C A B : PTyp), C\(And A B)\\C -> (C\A\\C) /\ (C\B\\C).
Proof.
  intros.
  inversion H; inversion H0; inversion H2; subst.
  remember H3. clear Heqt0.
  eapply TypDiff_id in H3.
  rewrite <- H3 in t0.
  rewrite <- H3 in H5.
  split; auto.
  apply H5.
Qed.

Theorem TypDiff_sym :
  forall (A B: PTyp), A \ B \\ A ->  B \ A \\ B.
Proof.
  intros A.
  induction A; intros.
  - induction B.
    * apply (TypDiff_deterministic PInt PInt TopT PInt) in H.
      inversion H.
      apply DInt_lr. apply TopT.
    * inversion H.
      subst.
      apply (TypDiff_int_l B1) in H3.
      destruct H3; subst.
      { apply (TypDiff_top_l _) in H5.
        inversion H5. }
      { apply IHB2 in H5.
        inversion H. subst.
        remember H3 as H3_p; clear HeqH3_p.
        apply (TypDiff_int_l _) in H3.
        destruct H3; subst.
        apply (TypDiff_top_l _) in H6.
        inversion H6.
        apply IHB1 in H3_p.
        eapply TypDiff_and_l_meg.
        assumption. assumption. }
    * apply DTop_l.
      auto.
  - apply TypDiff_and_l_spl in H.
    inversion H. inversion H0. inversion H1. inversion H3.
    clear H3 H1 H0 H.
    inversion H2.
    subst.
    apply IHA1 in H4. apply IHA2 in H5.
    apply (DandTyp_r _ _ _ x0 B) in H4; auto.
  - (* TopT *)
    apply DTop_r.
Qed.

Lemma TypDiff_int_3 : PInt \ PInt \\ PInt -> False.
  intros.
  apply (TypDiff_deterministic PInt PInt PInt TopT) in H.
  inversion H.
  apply DInt_lr. apply TopT.
Qed.

Hint Resolve TypDiff_id TypDiff_and_m_spl TypDiff_sym TypDiff_int_3.


Lemma and_not_atomic : forall (A B : PTyp), (Atomic (And A B)) -> False.
Proof.
  intros.
  inversion H.
Qed.

Lemma TypDiff_and_r : forall A B C D : PTyp, (A \ (And B C) \\ D -> (exists R : PTyp, (A \ B \\ R ) /\ ( R \ C \\ D ))).
Proof.
  intros.
  inversion H.
  - (* Atomic (And B C) *)
    apply and_not_atomic in H0.
    inversion H0.
  - (* Top \ ... \\ Top *)
    exists TopT. split; apply TypDiff_top_l_p.
  - (* \\ r1 \ *)
    exists r1. split; auto.
Qed.
    
(* Disjointness defined on TypDiff *)
Definition OrthoD (A B: PTyp) :=
  A \ B \\ A.

Lemma OrthoD_and : forall ( A B C : PTyp ), OrthoD A (And B C) <-> (OrthoD A B) /\ (OrthoD A C).
Proof.
  split.
  (* -> *)
  unfold OrthoD. intros.
  apply TypDiff_and_r in H. destruct H. destruct H.
  remember H as HB; clear HeqHB.
  apply (TypDiff_id A B x C)in H ; auto; subst.
  split; auto.
  (* <- *)
  unfold OrthoD. intros.
  destruct H.
  apply (DandTyp_r _ _ _ C A) in H; auto.
Qed.

Lemma OrthoD_sym : forall ( A B : PTyp ), OrthoD A B <-> OrthoD B A.
Proof.
  unfold OrthoD.
  split; apply TypDiff_sym.
Qed.

Theorem OrthoD_soundness :
  forall (A B: PTyp), OrthoD A B -> OrthoS A B.
Proof.
  intros.
  induction A.
  - induction B.
    + inversion H.
    + apply OrthoD_and in H. destruct H.
      apply ortho_sym.
      apply ortho_and; apply ortho_sym; [apply IHB1 | apply IHB2]; auto.
    + unfold OrthoS. intros.
      apply toplike_sub_is_toplike in H1.
      auto.
      apply TLTop.
  - apply OrthoD_sym in H. apply OrthoD_and in H. destruct H.
    apply ortho_and; [apply IHA1 | apply IHA2]; apply OrthoD_sym; auto.
  - unfold OrthoS. intros.
    apply toplike_sub_is_toplike in H0; auto.
Qed.

Lemma ortho_and_rev : forall (A B C: PTyp),
    OrthoS (And A B) C -> (OrthoS A C) /\ (OrthoS B C).
Proof.
  intros.
  unfold OrthoS in H.
  unfold OrthoS; split; intros; specialize (H C0);  apply H.
  - apply sand2; auto.
  - auto.
  - apply sand3; auto.
  - auto.
Qed. 
 
Theorem OrthoD_completeness :
  forall (A B: PTyp), OrthoS A B -> OrthoD A B.
Proof.
  intros.
  induction A.
  - induction B.
    + (* PInt PInt *)
      exfalso.
      unfold OrthoS in H.
      remember (H PInt) as HP; clear HeqHP.
      assert (TopLike PInt -> False) as contra.
      { intros. inversion H0. }
      apply contra. apply HP; apply sint.
    + (* PInt (And B1 B2) *)
      rewrite -> OrthoD_and.
      apply ortho_sym in H. apply ortho_and_rev in H. destruct H.
      split; [apply IHB1 | apply IHB2]; apply ortho_sym; auto.
    + (* PInt TopT *)
      unfold OrthoD.
      auto.
  - (* (And A1 A2) B *)
    apply ortho_and_rev in H. destruct H.
    apply OrthoD_sym. apply OrthoD_and.
    split; apply OrthoD_sym; [apply IHA1 | apply IHA2]; auto.
  - (* TopT B *)
    unfold OrthoD.
    apply TypDiff_top_l_p.
Qed.
    
End TypeDifferenceModule.



