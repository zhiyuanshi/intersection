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

End MExamples.