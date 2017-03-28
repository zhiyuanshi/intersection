Require Import String.
Require Import CoherenceBasicBD.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.

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
  | ALam : forall t, AExp (PLam t)
  | AMerge : forall v1 v2,
               AExp v1 ->
               AExp v2 ->
               AExp (PMerge v1 v2).

Inductive Value : PExp -> Prop :=
  | VAnn : forall a A, AExp a -> Value (PAnn RT a A).

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
  | Red_App3 : forall A B C e a,
                 AExp a ->
                 red (PApp (PAnn RT (PLam e) (Fun A B)) (PAnn RT a C))
                     (PApp (PAnn RT (PLam e) (Fun A B))
                           (PAnn CT (PAnn RT a C) A))
  | Red_App4 : forall A B C e a,
                 AExp a ->
                 red (PApp (PAnn RT (PLam e) (Fun A B)) (PAnn RT a C))
                     (PAnn CT (open_source e (PAnn RT a C)) B)
  | Red_Merge1 : forall e1 e2 e3,
                   red e1 e3 ->
                   red (PMerge e1 e2) (PMerge e3 e2)
  | Red_Merge2 : forall e1 e2 v,
                   Value v ->
                   red e1 e2 ->
                   red (PMerge v e1) (PMerge v e2)
  | Red_Merge3 : forall A B a1 a2,
                   AExp a1 ->
                   AExp a2 ->
                   red (PMerge (PAnn RT a1 A) (PAnn RT a2 B))
                       (PAnn RT (PMerge a1 a2) (And A B))
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
  | ARed_Merge1 : forall a1 a2 A B C,
                    Sub A C ->
                    Atomic C ->
                    AExp a1 ->
                    AExp a2 ->
                    red (PAnn CT (PAnn RT (PMerge a1 a2) (And A B)) C)
                        (PAnn CT (PAnn RT a1 A) C)
  | ARed_Merge2 : forall a1 a2 A B C,
                    Sub B C ->
                    Atomic C ->
                    AExp a1 ->
                    AExp a2 ->
                    red (PAnn CT (PAnn RT (PMerge a1 a2) (And A B)) C)
                        (PAnn CT (PAnn RT a2 B) C)
  | ARed_Merge3 : forall a A B C D,
                    AExp a ->
                    red (PAnn CT (PAnn RT a (And A B)) (And C D))
                        (PMerge (PAnn CT (PAnn RT a (And A B)) C)
                                (PAnn CT (PAnn RT a (And A B)) D)).



Hint Constructors typing bidityping AExp Value WFTyp red.

Theorem typing_ok : forall Gamma t A, typing Gamma t A -> ST.ok Gamma. Admitted.
Theorem typing_wf : forall Gamma t A, typing Gamma t A -> WFTyp A. Admitted.
Theorem bityping_ok : forall Gamma t A m, bidityping Gamma t m A -> ST.ok Gamma. Admitted.
Theorem bityping_wf : forall Gamma t A m, bidityping Gamma t m A -> WFTyp A. Admitted.
Theorem sub_trans : forall A B, Sub A B -> forall C, Sub B C -> Sub A C. Admitted.

Hint Resolve typing_ok typing_wf bityping_ok bityping_wf reflex sub_trans.
Hint Unfold Sub.

Theorem bityping_ann_sub :
  forall Gamma t A B m1 m2, bidityping Gamma (PAnn m1 t A) m2 B -> Sub A B.
Proof. intros Gamma t A B m1 m2 Htyping; dependent induction Htyping; eauto. Qed.

Theorem bityping_ann :
  forall Gamma t A B m1 m2, bidityping Gamma (PAnn m1 t A) B m2 -> bidityping Gamma t Chk A.
Proof. intros Gamma t A B m1 m2 Htyping; dependent induction Htyping; eauto. Qed.

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
  - admit. (* ??? *)
Admitted.

Hint Resolve bityping_ann_sub bityping_ann.
Hint Unfold erase.

Theorem bityping_inf_chk :
  forall Gamma e A,
    bidityping Gamma e Inf A -> bidityping Gamma e Chk A.
Proof.
  intros Gamma e A Htyping.
  assert (Ha : Sub A A) by eauto; destruct Ha.
  eapply ATySub' with (A := A); eauto.
Qed.

Hint Resolve bityping_inf_chk.

Theorem subject_reduction :
  forall Gamma e1 A m, bidityping Gamma e1 m A ->
              forall e2, red e1 e2 ->
                    bidityping Gamma e2 m A.
Proof.
  intros Gamma e1 A m Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma; generalize dependent m.
  induction Hred; intros; try now (dependent induction Htyping; subst; eauto).
  - admit.
  - admit.
  - admit.
  - admit.
  - dependent induction Htyping; eauto; clear IHHtyping.
    inversion Htyping; subst.
    inversion H3; subst.
    inversion H8; subst.
    inversion H6; subst.
    apply ATyAnnCT'.
    destruct H.
    eapply ATySub' with (A := A); eauto.
    apply ATyAnnRT'.    
Admitted.

Theorem subject_reduction1 :
  forall Gamma e1 A m1, bidityping Gamma e1 m1 A ->
               forall e2, red e1 e2 ->
                     exists m2, bidityping Gamma e2 m2 A.
Proof.
  intros Gamma e1 A m1 Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma; generalize dependent m1.
  induction Hred; intros; try now (inversion Htyping; subst; eauto).
  - dependent induction Htyping.
Admitted.

Theorem subject_reduction2 :
  forall Gamma e1 A, bidityping Gamma e1 Inf A ->
            forall e2, red e1 e2 ->
                  bidityping Gamma e2 Inf A.
Proof.
  intros Gamma e1 A Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma.
  induction Hred; intros; try now (dependent induction Htyping; subst; eauto).
  - dependent induction Htyping; subst.
    eapply ATyApp'; eauto. admit.
  - dependent induction Htyping; subst; eauto. admit.
  - dependent induction Htyping; eauto.
    admit.
  - admit.
  - dependent induction Htyping; eauto.
    apply ATyAnnCT'.
    admit.
  - dependent induction Htyping. clear IHHtyping.
    
    apply ATyAnnRT'.
    eapply ATySub' with (A := PInt). eauto.
    eauto.
Admitted.

Theorem subject_reduction1 :
  forall Gamma e1 A, typing Gamma e1 A ->
            forall e2, red e1 e2 ->
                  typing Gamma e2 A.
Proof.
  intros Gamma e1 A Htyping e2 Hred;
  generalize dependent A; generalize dependent Gamma.
  induction Hred; intros; try now simpl in *; eauto.
Admitted.

Theorem subject_reduction2 :
  forall Gamma e1 A, typing Gamma (erase e1) A ->
            forall e2, red e1 e2 ->
                  typing Gamma (erase e2) A.
Proof.
  intros Gamma e1 A H e2 Hred.
  generalize dependent A. generalize dependent Gamma.
  dependent induction Hred; intros; try now simpl in *; eauto.
  - simpl in *; dependent induction H; eauto.
  - simpl in *; dependent induction H; eauto.
    simpl in *; dependent induction H0; eauto.
  - simpl in *; unfold open_source; rewrite erase_open; simpl.
    dependent induction H0; eauto. clear IHtyping1 IHtyping2.
    admit. (* lambda case *)
  - simpl in *; dependent induction H; eauto.
  - simpl in *; dependent induction H; eauto.
    simpl in *; dependent induction H0; eauto.
  - simpl in *. admit. (* lambda case *)
  - simpl in *.
    admit. (* problem! *)
  - simpl in *.
    admit. (* problem! *)
  - simpl in *.
    admit. (* problem! *)
Admitted. 
   

Theorem typing_and_l : forall Gamma e A B, typing Gamma e (And A B) -> typing Gamma e A.
Proof.
  intros Gamma e A B H.
  eapply TySub' with (A := And A B); eauto.
  assert (Ha := typing_wf _ _ _ H); now inversion Ha.
Qed.  

    
Theorem subject_reduction3 : 
  forall Gamma e1 A, typing Gamma (erase e1) A ->
            forall e2, red e1 e2 ->
                  exists B, typing Gamma (erase e2) B /\ Sub A B /\ WFTyp B.
Proof.
  intros Gamma e1 A Htyping e2 Hred.
  generalize dependent A; generalize dependent Gamma.
  induction Hred; intros; try now simpl in *; eauto.
  - simpl in *.
    dependent induction Htyping.
    + clear IHHtyping1 IHHtyping2.
      apply IHHred in Htyping1; destruct Htyping1 as [C [H1 [H2 H3]]]; clear IHHred.
      destruct H2 as [c H2].
      dependent induction H2; subst; eauto.
      inversion H3; subst; exists o4; repeat split; [ | unfold Sub; eauto | auto].
      eapply TyApp' with (A := A); auto.
      eapply TySub' with (A := Fun o3 o4); eauto 3.
      apply sfun; eauto.
      admit. (* problem! *)
      admit.      
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl in *. dependent induction Htyping.
    + admit.
    + assert (Ha := IHHtyping H0 H H2 H1); destruct Ha as [D [H5 [H6 H7]]].
      exists D; repeat split; auto.
      admit. (* problem! *)
  - admit.
  - admit.
Admitted.
    
Theorem bdtyping_red :
  forall e1 A d, bidityping nil e1 d A -> exists e2, red e1 e2.
Proof.
  intros e1 A d Htyping.
  dependent induction Htyping; eauto.
  - inversion H0.
  - destruct IHHtyping1, IHHtyping2; eauto.
  - destruct IHHtyping1, IHHtyping2; eauto.
  - destruct IHHtyping; eauto.
  - eauto. admit. (* ? *)
Admitted.








