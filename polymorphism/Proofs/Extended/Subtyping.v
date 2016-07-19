Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import SystemF.
Require Import Coq.Program.Equality.
Require Export Infrastructure.

Module MSubtyping
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).
  
Module MInfrastructure := MInfrastructure(VarTyp)(set).
Export MInfrastructure.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

 *)

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2)
  | AVar : forall v, Atomic (PFVarT v)
  | AForAll : forall d t, Atomic (ForAll d t).
(*  | ATop : Atomic Top. *)

Hint Constructors Atomic.
Hint Constructors STType.

(* Subtyping relation *)

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4) 
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2) 
  | USAnd2 : forall t t1 t2 , usub t1 t -> PType t2 -> usub (And t1 t2) t 
  | USAnd3 : forall t t1 t2, usub t2 t -> PType t1 -> usub (And t1 t2) t
  | USVar   : forall v, usub (PFVarT v) (PFVarT v) 
  | USForAll : forall L d t1 t2,
                 (forall x, not (In x L) -> usub (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                 PType d ->
                 usub (ForAll d t1) (ForAll d t2)
  | USTop : forall t, PType t -> usub t Top.

Definition Is_inr {A B} (x : sum A B) : Type :=
  match x with
    | inr _ => True
    | inl _ => False
  end.

Hint Unfold Is_inr.

Inductive and_coercion (e : SExp var) : PTyp -> sum (SExp var) (SExp var) -> Prop :=
  | ACInt : and_coercion e PInt (inr e)
  | ACFunL : forall A B e1, and_coercion e B (inl e1) ->
                       and_coercion e (Fun A B) (inl (STLam _ e1))
  | ACFunR : forall A B, and_coercion e B (inr e) ->
                    and_coercion e (Fun A B) (inr e)
  | ACAndL : forall A B e1 e2, and_coercion e A (inl e1) ->
                          and_coercion e B (inl e2) ->
                          and_coercion e (And A B) (inl (STPair _ e1 e2))
  | ACAndR : forall A B e1 e2, and_coercion e A e1 ->
                          and_coercion e B e2 ->
                          sum (Is_inr e1) (Is_inr e2) -> 
                          and_coercion e (And A B) (inr e)
  | ACVar : forall x, and_coercion e (PFVarT x) (inr e)
  | ACForAllL : forall L A d e1,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inl e1)) ->
                  and_coercion e (ForAll d A) (inl (STTLam _ e1))
  | ACForAllR : forall L A d,
                  (forall x, not (In x L) ->
                        and_coercion e (open_typ_source A (PFVarT x)) (inr e)) ->
                  and_coercion e (ForAll d A) (inr e)
  | ACTop : and_coercion e Top (inl (STUnit _)).

Hint Constructors and_coercion.

Lemma ac_inr_inv : forall t e e', and_coercion e t (inr e') -> and_coercion e t (inr e).
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma ac_rename :
  forall L t e c, forall y,
    ~ In y (union L (fv_ptyp t)) -> and_coercion e (open_typ_source t (PFVarT y)) c ->
    (forall x : elt, ~ In x L -> and_coercion e (open_typ_source t (PFVarT x)) c).
Proof.
  intros.
  destruct (VarTyp.eq_dec x y).
  subst; auto.
Admitted.
  
Lemma ac_ex : forall L e t,
  (forall x, ~ In x L -> exists c, and_coercion e (open_typ_source t (PFVarT x)) c) ->
  exists c, forall x, ~ In x L -> and_coercion e (open_typ_source t (PFVarT x)) c.
Proof.
  intros L e t H.
  pick_fresh x.
  assert (Ha : ~ In x L) by not_in_L x.
  apply H in Ha.
  destruct Ha as [c HAC].
  exists c.
  intros.
  apply ac_rename with (y := x) (L := L).
  not_in_L x.
  admit.
Admitted.

Lemma foo : forall t e, PType t -> exists x, and_coercion e t x.
Proof.
  intros t e Ht.
  induction Ht; eauto.
  - destruct IHHt1, IHHt2.
    destruct x, x0; eauto; apply ac_inr_inv in H0; eauto.
  - destruct IHHt1, IHHt2.
    destruct x, x0; eauto.
  - apply ac_ex in H0.
    destruct IHHt.
    destruct H0.
    destruct x0.
    eexists.
    eapply ACForAllL with (L := L).
    intros.
    apply H0.
    auto.
    eexists.
    eapply ACForAllR with (L := L).
    intros.
    apply H0 in H2.
    now apply ac_inr_inv in H2.
Qed.

Fixpoint and_coercion' (t : PTyp) (e : SExp var) {struct t} : sum (SExp var) (SExp var).
refine(
  match t with
    | PInt => inr e
    | Fun _ B => match (and_coercion' B e) with
                  | inl l => inl (STLam _ l)
                  | inr r => inr r
                 end 
    | And A B => match (and_coercion' A e, and_coercion' B e) with
                  | (inl l1, inl l2) =>
                    inl (STPair _ l1 l2)
                  | _ => inr e
                end
    | PBVarT _  => inr e
    | PFVarT _ => inr e
    | ForAll d A => match and_coercion' A e with
                     | inl l => inl (STTLam _ l)
                     | inr e => inr e
                   end
    | Top    => inl (STUnit _)
  end).
Defined.
(*
pick_fresh x.
destruct (and_coercion (open_typ_source A (PFVarT x)) e).
apply (inl (STTLam _ s)).
apply (inr s).
Admitted. *)

Definition join_sum : forall {A}, A + A -> A.
  intros A H; destruct H as [a | a]; exact a.
Defined.

Inductive sub : PTyp -> PTyp -> (SExp var) -> Prop :=
  | SInt : sub PInt PInt (STLam _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2,
             sub o3 o1 c1 ->
             sub o2 o4 c2 -> 
             sub (Fun o1 o2) (Fun o3 o4) (STLam _ (STLam _ (STApp _ c2 (STApp _ (STBVar _ 1) (STApp _ c1 (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2,
              sub t t1 c1 ->
              sub t t2 c2 -> 
              sub t (And t1 t2) (STLam _ (STPair _ (STApp _ c1 (STBVar _ 0)) (STApp _ c2 (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c,
              sub t1 t c ->
              Atomic t ->
              PType t2 ->
              (* and_coercion ((STApp _ c (STProj1 _ (STBVar _ 0)))) t ac -> 
              sub (And t1 t2) t (STLam _ (join_sum ac)) *)
              sub (And t1 t2) t (STLam _ (join_sum (and_coercion' t ((STApp _ c (STProj1 _ (STBVar _ 0)))))))
  | SAnd3 : forall t t1 t2 c,
              sub t2 t c ->
              Atomic t ->
              PType t1 ->
              sub (And t1 t2) t (STLam _ (join_sum (and_coercion' t ((STApp _ c (STProj2 _ (STBVar _ 0)))))))
              (* and_coercion ((STApp _ c (STProj2 _ (STBVar _ 0)))) t ac -> 
              sub (And t1 t2) t (STLam _ (join_sum ac)) *)
  | SVar : forall v, sub (PFVarT v) (PFVarT v) (STLam _ (STBVar _ 0))
  | SForAll : forall L d t1 t2 c,
                (forall x, not (In x L) -> sub (open_typ_source t1 (PFVarT x))
                                         (open_typ_source t2 (PFVarT x))
                                         (open_typ_term c (STFVarT x))) ->
                PType d ->
                sub (ForAll d t1) (ForAll d t2)
                    (STLam _ (STTLam _ (STApp _ c (STTApp _ (STBVar _ 0) (STBVarT 0)))))
  | STop : forall t, PType t -> sub t Top (STLam _ (STUnit _)).

Hint Constructors Atomic sub usub.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp var), sub t1 t2 e.

Lemma sub_lc : forall t1 t2, Sub t1 t2 -> PType t1 /\ PType t2.
Proof.
  intros t1 t2 HSub.
  destruct HSub.
  induction H; eauto.
  - destruct IHsub1, IHsub2; auto.
  - destruct IHsub1, IHsub2; auto.
  - destruct IHsub; auto.
  - destruct IHsub; auto.
  - split.
    apply_fresh PType_ForAll as x; auto.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 in Ha; now destruct Ha.
    apply_fresh PType_ForAll as x; auto.
    assert (Ha : ~ In x L) by not_in_L x.
    apply H0 in Ha; now destruct Ha.
Qed.

Hint Resolve sub_lc.

(* Smart constructors for Sub *)

Definition stop : forall t, PType t -> Sub t Top.
unfold Sub; eauto.
Defined.

Definition sint : Sub PInt PInt.
unfold Sub. exists (STLam _ (STBVar _ 0)). 
exact SInt.
Defined.

Definition sfun : forall o1 o2 o3 o4, Sub o3 o1 -> Sub o2 o4 -> Sub (Fun o1 o2) (Fun  o3 o4).
unfold Sub; intros. destruct H. destruct H0.
exists (STLam _ ( 
       STLam _ (STApp _ x0 (STApp _ (STBVar _ 1) (STApp _ x (STBVar _ 0)))))).
apply SFun. auto. auto.
Defined.

Definition sand1 : forall t t1 t2, Sub t t1 -> Sub t t2 -> Sub t (And t1 t2).
unfold Sub. intros. destruct H. destruct H0.
exists (STLam _ (
       STPair _ (STApp _ x (STBVar _ 0)) (STApp _ x0 (STBVar _ 0)))).
apply SAnd1. auto. auto.
Defined.

Definition sand2_atomic :
  forall t t1 t2, Sub t1 t -> Atomic t -> PType t2 -> Sub (And  t1 t2) t.
  unfold Sub; intros t t1 t2 H H1 H0;
  destruct t; try (now inversion H1); destruct H; eauto.
Defined.

Definition sand2 : forall t t1 t2, Sub t1 t -> PType t2 -> Sub (And t1 t2) t.
  intro t.
  induction t; intros.
  (* Case PInt *)
  - apply sand2_atomic; auto.
  (* Case Fun *)
  - apply sand2_atomic; auto.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1; auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H7. destruct H7.
    unfold Sub in H8. destruct H8.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H2.
    inversion H2.
  (* Case BVar *)
  - inversion H. inversion H1; inversion H3.
  (* Case FVar *)
  - apply sand2_atomic; auto.
  (* Case ForAll *)
  - apply sand2_atomic; auto; apply AForAll.
  (* Case Top *)
  - apply stop; auto.
    apply PType_And; auto.
    apply sub_lc in H; now destruct H.
Qed.

Definition sand3_atomic :
  forall t t1 t2, Sub t2 t -> Atomic t -> PType t1 -> Sub (And t1 t2) t.
  unfold Sub; intros t t1 t2 H H1 H0.
  destruct t; try (now inversion H1); destruct H; eauto.
Defined.

Definition sand3 : forall t t1 t2, Sub t2 t -> PType t1 -> Sub (And t1 t2) t.
  intros t; induction t; intros.
  (* Case PInt *)
  - apply sand3_atomic; auto.
  (* Case Fun *)
  - apply sand3_atomic; auto.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1. auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H7. destruct H7.
    unfold Sub in H8. destruct H8.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H2.
    inversion H2.
  (* Case BVar *)
  - inversion H; inversion H1; inversion H3.
  (* Case FVar *)
  - apply sand3_atomic; auto.
  (* Case ForAll *)
  - apply sand3_atomic; auto; apply AForAll.
  (* Case Top *)
  - apply stop; auto.
    apply PType_And; auto.
    apply sub_lc in H; now destruct H.
Qed.

Definition svar : forall v, Sub (PFVarT v) (PFVarT v).
  intros.
  unfold Sub.
  exists (STLam _ (STBVar _ 0)).
  apply SVar.
Defined.

(*
Definition sforall : forall L t1 t2 c,
                (forall x, not (In x L) -> sub (open_ptyp t1 (PFVar x))
                                         (open_ptyp t2 (PFVar x))
                                         (open_typ_term c (STFVarT x))) ->
                Sub (ForAll t1) (ForAll t2).
  intros.
  unfold Sub.
  eexists.
  eapply SForAll.
  intros.
  
  pick_fresh.
 *)

Hint Constructors sub.
Hint Resolve stop sint sfun sand1 sand2 sand3 svar.

Lemma sound_sub : forall t1 t2, usub t1 t2 -> Sub t1 t2.
  intros; induction H; auto.
  - unfold Sub.
    eexists.
    apply_fresh SForAll as x; auto.
    admit.
Admitted.

Lemma complete_sub : forall t1 t2, Sub t1 t2 -> usub t1 t2.
Proof.
  intros; destruct H; induction H; auto.
  - apply_fresh USForAll as x.
    apply H0.
    not_in_L x.
    auto.
Qed.  

(* Properties about sub *)

Lemma usub_refl : forall t, PType t -> usub t t.
Proof.
  intros t HWFt; induction HWFt; auto.
  - apply_fresh USForAll as x.
    apply H0.
    not_in_L x.
    auto.
Qed.

Lemma usub_and_l : forall t1 t2 t3, usub t1 (And t2 t3) -> usub t1 t2.
Proof.
  intros t1 t2 t3 Husub.
  apply complete_sub.
  apply sound_sub in Husub as [c Hsub].
  inversion Hsub; subst.
  exists c1; auto. inversion H0. inversion H0.
Qed.

Lemma usub_and_r : forall t1 t2 t3, usub t1 (And t2 t3) -> usub t1 t3.
Proof.
  intros t1 t2 t3 Husub.
  apply complete_sub.
  apply sound_sub in Husub as [c Hsub].
  inversion Hsub; subst.
  exists c2; auto. inversion H0. inversion H0.
Qed.

Lemma usub_lc : forall t1 t2, usub t1 t2 -> PType t1 /\ PType t2.
Proof.
  intros.
  apply sound_sub in H.
  now apply sub_lc in H.
Qed.
  
Lemma usub_trans_mid :
  forall A B C D, usub A B -> usub B C -> usub C D -> usub A D.
Proof.
  intros A B C D HusubAB HusubBC HusubCD.
  generalize dependent A.
  generalize dependent D.
  induction HusubBC; intros; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubAB; subst; auto.
    dependent induction HusubCD; subst; auto.
    apply USAnd1.
    apply IHHusubCD1; auto.
    intros; auto.
    subst.
    apply usub_and_l with (t3 := t2); eauto.
    intros; auto.
    subst.
    apply usub_and_l with (t3 := t2); eauto.
    apply IHHusubCD2; auto.
    intros; auto.
    subst.
    apply usub_and_r with (t2 := t1); eauto.
    intros; auto.
    subst.
    apply usub_and_r with (t2 := t1); eauto.    
    apply usub_lc in HusubAB1; apply usub_lc in HusubAB2.
    apply USTop; destruct HusubAB1; destruct HusubAB2; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubAB; subst; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto. 
  - dependent induction HusubCD; subst; auto.
    dependent induction HusubAB; subst; auto.
    apply_fresh USForAll as x.
    apply H0 with (x := x).
    not_in_L x.
    apply H2.
    not_in_L x.
    apply H6.
    not_in_L x.
    auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
  - dependent induction HusubCD; subst; auto.
    apply usub_lc in HusubAB; apply USTop; destruct HusubAB; auto.
Qed.

Lemma usub_trans :
  forall B A C, PType C -> usub A B -> usub B C -> usub A C.
Proof.
  intros B A C HWFC HusubAB HusubBC.
  assert (HusubCC : usub C C).
  eapply usub_refl; apply HWFC.
  eapply usub_trans_mid.
  apply HusubAB.
  apply HusubBC.
  apply HusubCC.
Qed.

Lemma usub_subst :
  forall A B z u,
    usub A B ->
    PType u ->
    usub (subst_typ_source z u A) (subst_typ_source z u B).
Proof.
  intros A B z u HSub HWFu.
  induction HSub; intros; simpl; eauto.
  - apply USAnd2; auto; now apply subst_source_lc.
  - apply USAnd3; auto; now apply subst_source_lc.
  - destruct eqb; auto.
    eapply usub_refl; apply HWFu.
  - apply_fresh USForAll as x.
    repeat rewrite subst_typ_source_open_source_var; auto.
    apply H0; auto.
    not_in_L x.
    not_in_L x.
    not_in_L x.
    now apply subst_source_lc.
  - apply USTop.
    apply subst_source_lc; auto.
Qed.

Lemma usub_subst_not_in :
  forall A B u z,
    not (In z (fv_ptyp B)) ->
    usub A B ->
    PType u ->
    usub (subst_typ_source z u A) B.
Proof.
  intros A ty u z HNotIn HSub HWFu.
  erewrite <- subst_typ_source_fresh with (t := ty).
  eapply usub_subst; eauto.
  auto.
Qed.

End MSubtyping.