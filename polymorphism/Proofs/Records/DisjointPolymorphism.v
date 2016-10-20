Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

We annotate the Coq theorems with the corresponding lemmas/theorems in the paper. 
The reader can just look for:

Lemma 4

for example, to look for the proof of lemma 4 in the paper.
This top-level Coq script only re-states the lemmas/theorems formulated in the paper,
which have been proven in other sub-scripts.

All lemmas and theorems are complete: there are no uses of admit or Admitted,
with the exceptions of "sound_sub" due to a technical limitation.

*)

Module MDisjointPolymorphism
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MExtended := MExtended(VarTyp)(set).
Export MExtended.

(* Lemma 2: Subtyping reflexivity *)

Lemma subyping_reflexivity : forall t, PType t -> Sub t t.
Proof. intros; apply sound_sub; now apply usub_refl. Qed.

(* Lemma 3: Subtyping transitivity *)

Lemma subtyping_transitivity : forall B A C : PTyp, PType C -> Sub A B -> Sub B C -> Sub A C.
Proof.
  intros B A C HPT HS1 HS2. apply complete_sub in HS1. apply complete_sub in HS2.
  apply sound_sub; eapply usub_trans; eauto.
Qed.

(* Lemma 4: Covariance of disjointness *)

Lemma covariance_disjointness :
  forall Gamma u ty d, PType ty -> Ortho Gamma u d -> Sub d ty -> Ortho Gamma u ty.
Proof.
  intros Gamma u ty d HT HO HS; apply complete_sub in HS; eapply Ortho_usub_trans; eauto.
Qed.

(* Lemma 5: Disjointness is stable under substitution *)

Lemma disjointness_stable_substitution :
  forall z u Gamma d t1 t2,
    not (In z (fv_ptyp u)) ->
    WFEnv (subst_env Gamma z u) ->
    WFEnv Gamma ->
    MapsTo Gamma z d -> 
    Ortho Gamma u d ->
    Ortho Gamma t1 t2 ->
    PType u ->
    PType t1 ->
    PType t2 ->
    Ortho (subst_env Gamma z u) (subst_typ_source z u t1) (subst_typ_source z u t2).
Proof. apply ortho_subst. Qed.

(* Lemma 6: Types are stable under substitution *)

Lemma types_stable_substitution :
  forall t z u Gamma d, not (In z (fv_ptyp u)) ->
               MapsTo Gamma z d ->
               WFEnv (subst_env Gamma z u) ->
               Ortho Gamma u d ->
               WFTyp Gamma u ->
               WFTyp Gamma t ->
               WFTyp (subst_env Gamma z u) (subst_typ_source z u t).
Proof. apply subst_source_wf_typ. Qed.

(* Lemma 7: Well-formed typing *)

Lemma wellformed_typing :
  forall Gamma t T E dir, has_type_source_alg Gamma t dir T E -> WFTyp Gamma T.
Proof. apply typing_wf_source_alg. Qed.  

(* Lemma 8: Subtyping rules produce type-correct coercions *)

Lemma subtype_correct_coercions :
  forall Gamma A B E, sub A B E ->
             WFEnv Gamma ->
             WFTyp Gamma A ->
             WFTyp Gamma B ->
             has_type_st (∥ Gamma ∥) E (STFun (|A|) (|B|)) .
Proof. apply type_correct_coercions. Qed.

(* Lemma 9: Unique subtyping contributor *)

Lemma unique_subtyping_contributor :
  forall Gamma A B C, WFTyp Gamma A ->
             WFTyp Gamma B ->
             ~ TopLike C ->
             Ortho Gamma A B ->
             Sub (And A B) C ->
             not (Sub A C /\ Sub B C).
Proof. apply uniquesub. Qed.

(* Theorem 1: Type preservation *)

Lemma type_preservation :
  forall x ty dir E (Gamma : context TyEnvSource) (H : has_type_source_alg Gamma x dir ty E),
  has_type_st (∥ Gamma ∥) E (|ty|).
Proof. apply type_preservation. Qed.

(* Theorem 3: Uniqueness of type-inference *)

Lemma uniqueness_type_inference :
  forall Gamma e t1 t2 E1 E2, has_type_source_alg Gamma e Inf t1 E1 ->
                     has_type_source_alg Gamma e Inf t2 E2 ->
                     t1 = t2.
Proof. intros; eapply typ_inf_unique; eauto. Qed.

(* Theorem 4: Unique elaboration *)

Lemma unique_elaboration :
  forall Gamma e d t E1 E2, has_type_source_alg Gamma e d t E1 ->
                   has_type_source_alg Gamma e d t E2 ->
                   E1 = E2.
Proof. intros; eapply typ_coherence; eauto. Qed.

End MDisjointPolymorphism.