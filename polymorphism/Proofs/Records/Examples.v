Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import SystemF.
Require Import Extended.

Module MExamples
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MExtended := MExtended(VarTyp)(set).
Export MExtended.

(*** Records ***)

(* { x := 3 }.x : Int *)

Parameter x : var.
Definition RecX := PRec x (PLit 3).
Theorem ex1 : exists c, has_type_source_alg nil (PProjR RecX x) Inf PInt c.
  eexists; unfold RecX. eauto.
Defined.

(* ({ x := 3 } ,, { y := 4 }).x : Int *) (* needs annotation *)

Parameter y : var.
Definition RecY := PRec y (PLit 4).
Definition RecXTy := (Rec x PInt).
Theorem ex2 :
  x <> y ->
  exists c, has_type_source_alg nil (PProjR (PAnn (PMerge RecX RecY) RecXTy) x) Inf PInt c.
  eexists; unfold RecX, RecY, RecXTy.
  apply ATyProjR.
  apply ATyAnn.
  apply ATySub with (A := And (Rec x PInt) (Rec y PInt)); eauto.
  apply ATyMerge; eauto.
Defined.

(* ({ x := 3 } ,, { x := () }).x : Int *) (* needs annotation *)

Definition RecX' := PRec x PUnit.
Theorem ex3 :
  exists c, has_type_source_alg nil (PProjR (PAnn (PMerge RecX RecX') RecXTy) x) Inf PInt c.
  eexists; unfold RecX, RecX', RecXTy.
  apply ATyProjR.
  apply ATyAnn.
  apply ATySub with (A := And (Rec x PInt) (Rec x Top)); eauto.
  apply ATyMerge; eauto.
Defined.

(*** Daan Leijen's Extensible Records ***)

(* Polymorphic records *)

Notation "{{ l = t }}" := (PRec l t) (at level 0, l at next level, t at next level).
Notation "t.l" := (PProjR t x).
Notation "A ,, B" := (PMerge A B) (at level 80, right associativity).

Notation "{{ l :: A }}" := (Rec l A) (at level 0, l at next level, A at next level).
Notation "A & B" := (And A B) (at level 80, right associativity).

Check (Rec x Top).

Print Rec.
Print Grammar constr.

Parameter id : var.
Parameter const : var.
Axiom diff : id <> const.

Hint Resolve diff.

Definition idTyp : PTyp := ForAll Top (Fun (PBVarT 0) (PBVarT 0)).
Definition constTyp : PTyp := ForAll Top (ForAll Top (Fun (PBVarT 1)
                                                         (Fun (PBVarT 0) (PBVarT 1)))).
Definition PreludeTyp : PTyp := {{ id :: idTyp }} & {{ const :: constTyp }}.

Definition idImpl : PExp := PTLam Top (PLam (PBVar 0)).
Definition constImpl : PExp := PTLam Top (PTLam Top (PLam (PLam (PBVar 1)))).
Definition Prelude : PExp := {{ id = (PAnn idImpl idTyp) }} ,, {{ const = constImpl }}.

Theorem foo :
  exists c, has_type_source_alg nil Prelude Inf PreludeTyp c.
Proof.
  eexists; unfold Prelude, PreludeTyp, idImpl, constImpl.
  apply ATyMerge; auto.
  (* id *)
  - apply ATyRec.
    apply ATyAnn.
    apply_fresh ATyTLam as x; auto. 
    unfold open_typ_term_source, open_typ_source, open_typ_term; simpl.
    apply ATyLam.
    
  admit. (* needs annotation *)
  admit. (* needs annotation *)

                                       
End MExamples.