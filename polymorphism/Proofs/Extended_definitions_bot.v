Require Import String.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import SystemF.

Module Definitions
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).
  
Module SF := SysF(VarTyp)(set).
Export SF.

(* Notes:

The syntax is encoded using Charguéraud's Locally nameless representation:

http://www.chargueraud.org/softs/ln/

 *)

(* Our calculus: *)

Inductive PTyp : Type :=
  | PInt : PTyp
  | Fun : PTyp -> PTyp -> PTyp
  | And : PTyp -> PTyp -> PTyp
  | PBVarT : nat -> PTyp
  | PFVarT : var -> PTyp
  | ForAll : PTyp -> PTyp -> PTyp (* disjoint constraint *)
  | Bot : PTyp.

Fixpoint ptyp2styp (t : PTyp) : STyp :=
  match t with
    | PInt => STInt 
    | Fun t1 t2 => STFun (ptyp2styp t1) (ptyp2styp t2)
    | And t1 t2 => STTuple (ptyp2styp t1) (ptyp2styp t2)
    | PBVarT n => STBVarT n
    | PFVarT v => STFVarT v
    | ForAll _ t => STForAll (ptyp2styp t)
    | Bot => STForAll (STBVarT 0)
  end.

Notation "'|' t '|'" := (ptyp2styp t) (at level 60).

Fixpoint open_rec_typ_source (k : nat) (u : PTyp) (t : PTyp) {struct t} : PTyp :=
  match t with
  | PInt        => PInt
  | Fun t1 t2   => Fun (open_rec_typ_source k u t1) (open_rec_typ_source k u t2)
  | And t1 t2   => And (open_rec_typ_source k u t1) (open_rec_typ_source k u t2) 
  | PFVarT x    => PFVarT x
  | PBVarT i    => if Nat.eqb k i then u else (PBVarT i)
  | ForAll d t => ForAll (open_rec_typ_source k u d) (* d comes before forall *)
                        (open_rec_typ_source (S k) u t)
  | Bot         => Bot
  end.

Definition open_typ_source (t : PTyp) u := open_rec_typ_source 0 u t.

Fixpoint subst_typ_source (z : var) (u : PTyp) (t : PTyp) {struct t} : PTyp :=
  match t with
  | PInt        => PInt
  | Fun t1 t2   => Fun (subst_typ_source z u t1) (subst_typ_source z u t2)
  | And t1 t2   => And (subst_typ_source z u t1) (subst_typ_source z u t2)
  | PFVarT x    => if VarTyp.eqb x z then u else (PFVarT x)
  | PBVarT i    => PBVarT i
  | ForAll d t  => ForAll (subst_typ_source z u d) (subst_typ_source z u t)
  | Bot         => Bot
  end.

Fixpoint fv_ptyp (pTyp : PTyp) : vars :=
  match pTyp with
    | PInt        => empty 
    | Fun t1 t2   => union (fv_ptyp t1) (fv_ptyp t2)
    | And t1 t2   => union (fv_ptyp t1) (fv_ptyp t2)
    | PBVarT n    => empty
    | PFVarT v    => singleton v
    | ForAll d t  => union (fv_ptyp d) (fv_ptyp t)
    | Bot         => empty
  end.  

Inductive PType : PTyp -> Prop :=
  | PType_Var : forall x, PType (PFVarT x)
  | PType_Int : PType PInt
  | PType_Fun : forall t1 t2, PType t1 -> PType t2 -> PType (Fun t1 t2)
  | PType_And : forall t1 t2, PType t1 -> PType t2 -> PType (And t1 t2)
  | PType_ForAll : forall L d t,
                     PType d ->
                     (forall x, not (In x L) -> PType (open_typ_source t (PFVarT x))) ->
                     PType (ForAll d t)
  | PType_Bot : PType Bot.

Hint Constructors PType.

Inductive Atomic : PTyp -> Prop :=
  | AInt : Atomic PInt
  | AFun : forall t1 t2, Atomic (Fun t1 t2)
  | AVar : forall v, Atomic (PFVarT v)
  | AForAll : forall d t, Atomic (ForAll d t)
  | ABot : Atomic Bot.

Inductive BottomLike : PTyp -> Prop :=
  | BLBot : BottomLike Bot
  | BLAnd1 : forall t1 t2, BottomLike t1 -> BottomLike (And t1 t2)                   
  | BLAnd2 : forall t1 t2, BottomLike t2 -> BottomLike (And t1 t2)
  | BLFun : forall t1 t2, BottomLike t2 -> BottomLike (Fun t1 t2) (* what if t1 is bottomlike? should be bottom too ? *)
  | BLForAll : forall L d t,
                 (forall x, not (In x L) -> BottomLike (open_typ_source t (PFVarT x))) ->
                 BottomLike (ForAll d t).
                                       
(* Subtyping relation *)

Inductive usub : PTyp -> PTyp -> Prop :=
  | USInt : usub PInt PInt
  | USFun : forall o1 o2 o3 o4, usub o3 o1 -> usub o2 o4 -> usub (Fun o1 o2) (Fun  o3 o4) 
  | USAnd1 : forall t t1 t2, usub t t1 -> usub t t2 -> usub t (And  t1 t2) 
  | USAnd2 : forall t t1 t2 , usub t1 t -> usub (And t1 t2) t 
  | USAnd3 : forall t t1 t2, usub t2 t -> usub (And t1 t2) t
  | USVar   : forall v, usub (PFVarT v) (PFVarT v) 
  | USForAll : forall L d t1 t2,
                 (forall x, not (In x L) -> usub (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                 usub (ForAll d t1) (ForAll d t2)
  | USBot : forall t, PType t -> usub Bot t.

Inductive sub : PTyp -> PTyp -> (SExp var) -> Prop :=
  | SInt : sub PInt PInt (STLam _ (STBVar _ 0))
  | SFun : forall o1 o2 o3 o4 c1 c2, sub o3 o1 c1 -> sub o2 o4 c2 -> 
     sub (Fun o1 o2) (Fun o3 o4) (STLam _ (STLam _ (STApp _ c2 (STApp _ (STBVar _ 1) (STApp _ c1 (STBVar _ 0))))))
  | SAnd1 : forall t t1 t2 c1 c2, sub t t1 c1 -> sub t t2 c2 -> 
     sub t (And  t1 t2) (STLam _
       (STPair _ (STApp _ c1 (STBVar _ 0)) (STApp _ c2 (STBVar _ 0))))
  | SAnd2 : forall t t1 t2 c, sub t1 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam _ 
       ((STApp _ c (STProj1 _ (STBVar _ 0)))))
  | SAnd3 : forall t t1 t2 c, sub t2 t c -> Atomic t ->
     sub (And  t1 t2) t (STLam _ 
       ((STApp _ c (STProj2 _ (STBVar _ 0)))))
  | SVar : forall v, sub (PFVarT v) (PFVarT v) (STLam _ (STBVar _ 0))
  | SForAll : forall L d t1 t2 c,
                (forall x, not (In x L) -> sub (open_typ_source t1 (PFVarT x))
                                         (open_typ_source t2 (PFVarT x))
                                         (open_typ_term c (STFVarT x))) ->
                sub (ForAll d t1) (ForAll d t2)
                    (STLam _ (STTLam _ (STApp _ c (STTApp _ (STBVar _ 0) (STBVarT 0)))))
  | SBot : forall t, PType t -> sub Bot t (STLam _ (STTApp _ (STBVar _ 0) (| t |))).

Hint Constructors Atomic sub usub.

Definition Sub (t1 t2 : PTyp) : Prop := exists (e:SExp var), sub t1 t2 e.
  
(* Smart constructors for Sub *)

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
  forall t t1 t2, Sub t1 t -> Atomic t -> Sub (And  t1 t2) t.
  unfold Sub. intros t t1 t2 H H0. destruct t; try (now inversion H0).
  - destruct H.
    exists (STLam _ ((STApp _ x (STProj1 _ (STBVar _ 0))))).
    apply SAnd2; auto.
  - destruct H.
    exists (STLam _ ((STApp _ x (STProj1 _ (STBVar _ 0))))).
    apply SAnd2; auto.
  - destruct H.
    exists (STLam _ ((STApp _ x (STProj1 _ (STBVar _ 0))))).
    apply SAnd2; auto.
  - destruct H.
    exists (STLam _ ((STApp _ x (STProj1 _ (STBVar _ 0))))).
    apply SAnd2; auto.
  - destruct H.
    exists (STLam _ ((STApp _ x (STProj1 _ (STBVar _ 0))))).
    apply SAnd2; auto.
Defined.

Definition sand2 : forall t t1 t2, Sub t1 t -> Sub (And t1 t2) t.
  intro t.
  induction t; intros.
  (* Case PInt *)
  - apply sand2_atomic. auto. apply AInt. 
  (* Case Fun *)
  - apply sand2_atomic. auto. apply AFun.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1; auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H6. destruct H6.
    unfold Sub in H7. destruct H7.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H1.
    inversion H1.
    subst.
    assert (Ha : Sub Bot t1). inversion H0; eexists; auto.
    apply IHt1 with (t3 := t3) in Ha.
    destruct Ha.
    assert (Ha : Sub Bot t2) by (inversion H0; eexists; auto).
    apply IHt2 with (t3 := t3) in Ha.
    destruct Ha.
    eexists.
    apply SAnd1; eauto.
  (* Case BVar *)
  - inversion H. inversion H0. inversion H2. inversion H2. inversion H1.
  (* Case FVar *)
  - apply sand2_atomic; auto.
  (* Case ForAll *)
  - apply sand2_atomic; auto; apply AForAll.
  (* Case Bot *)
  - apply sand2_atomic; auto; apply ABot.
Qed.

Definition sand3_atomic :
  forall t t1 t2, Sub t2 t -> Atomic t -> Sub (And t1 t2) t.
  unfold Sub; intros t t1 t2 H H0.
  destruct t; try (now inversion H0);
  destruct H; exists (STLam _ ((STApp _ x (STProj2 _ (STBVar _ 0))))); apply SAnd3; auto. 
Defined.

Definition sand3 : forall t t1 t2, Sub t2 t -> Sub (And t1 t2) t.
  intros t; induction t; intros.
  (* Case PInt *)
  - apply sand3_atomic. auto. apply AInt.
  (* Case Fun *)
  - apply sand3_atomic. auto. apply AFun.
  (* Case And *)
  - unfold Sub. unfold Sub in H. destruct H. inversion H.
    assert (Sub (And t0 t3) t1). apply IHt1.
    unfold Sub. exists c1. auto. auto.
    assert (Sub (And t0 t3) t2). apply IHt2.
    unfold Sub. exists c2. auto. auto.
    unfold Sub in H6. destruct H6.
    unfold Sub in H7. destruct H7.
    exists (STLam _ (STPair _ (STApp _ x0 (STBVar _ 0)) (STApp _ x1 (STBVar _ 0)))).
    apply SAnd1. auto. auto.
    inversion H1.
    inversion H1.
    inversion H0; subst.
    admit.
  (* Case BVar *)
  - inversion H; inversion H0; inversion H2. inversion H1.
  (* Case FVar *)
  - apply sand3_atomic; auto.
  (* Case ForAll *)
  - apply sand3_atomic; auto; apply AForAll.
  (* Case Bot *)
  - apply sand3_atomic; auto; apply ABot.
Admitted.

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

(** Environment definitions **)

Inductive TyEnvSource : Type :=
  | TyDis : PTyp -> TyEnvSource
  | TermV : PTyp -> TyEnvSource.

Hint Constructors TyEnvSource.

Inductive WFEnv : context TyEnvSource -> Prop :=
  | WFNil : WFEnv nil
  | WFPushV : forall Gamma v ty,
                WFEnv Gamma -> not (In v (fv_ptyp ty)) -> ~ In v (dom Gamma) ->
                WFEnv (extend v (TyDis ty) Gamma)              
  | WFPushT : forall Gamma v ty,
                WFEnv Gamma -> ~ In v (dom Gamma) -> WFEnv (extend v (TermV ty) Gamma).

Hint Constructors WFEnv.

Fixpoint subst_env (Gamma : context TyEnvSource) (z : var) (u : PTyp) :=
  match Gamma with
    | nil => nil
    | (x,TyDis d) :: tl => (x, TyDis (subst_typ_source z u d)) ::
                           (subst_env tl z u)
    | (x, TermV ty) :: tl => (x, TermV ty) :: (subst_env tl z u)
  end.

Definition MapsTo (Gamma : context TyEnvSource) (z : var) (d : PTyp) :=
  find (fun x => eqb (fst x) z) Gamma = Some (z, TyDis d).

Definition TyEnvMatch {A} (f : PTyp -> A) (tyenv : TyEnvSource) : A :=
  match tyenv with
    | TyDis d => f d
    | TermV ty => f ty
  end.

Definition codom (c : context TyEnvSource) : vars :=
  fold_right (fun el r => union (TyEnvMatch fv_ptyp (snd el)) r) empty c.

(* Disjointness: Implementation *)

Definition hd (p : PTyp) : nat :=
  match p with
  | PInt       => 0
  | Fun t1 t2  => 1
  | ForAll d t => 2
  | Bot        => 3
  | PBVarT n   => 4
  | PFVarT v   => 5 
  | And t1 t2  => 6
  end.

Definition OrthoAx (t1 t2 : PTyp) : Prop :=
  (hd t1 < 3 /\ hd t2 < 3 /\ not (hd t1 = hd t2)).

Inductive Ortho : context TyEnvSource -> PTyp -> PTyp -> Prop :=
  | OAnd1 : forall Gamma t1 t2 t3, Ortho Gamma t1 t3 -> Ortho Gamma t2 t3 -> Ortho Gamma (And t1 t2) t3
  | OAnd2 : forall Gamma t1 t2 t3, Ortho Gamma t1 t2 -> Ortho Gamma t1 t3 -> Ortho Gamma t1 (And t2 t3)
  | OFun  : forall Gamma t1 t2 t3 t4, Ortho Gamma t2 t4 -> Ortho Gamma (Fun t1 t2) (Fun t3 t4)
  | OForAll : forall L Gamma d t1 t2,
                (forall x, not (In x L) -> Ortho (extend x (TyDis d) Gamma)
                                           (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                Ortho Gamma (ForAll d t1) (ForAll d t2)
  | OVar : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                       usub A ty ->
                       not (BottomLike ty) ->
                       PType ty ->
                       Ortho Gamma (PFVarT x) ty
  | OVarSym : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                          usub A ty ->
                          not (BottomLike ty) ->
                          PType ty ->
                          Ortho Gamma ty (PFVarT x)
  | OBot1 : forall Gamma t A, BottomLike A -> Ortho Gamma A t
  | OBot2 : forall Gamma t A, BottomLike A -> Ortho Gamma t A
  | OAx : forall Gamma t1 t2, OrthoAx t1 t2 -> Ortho Gamma t1 t2.

Hint Constructors Ortho.

(* Disjointness: Specification *)

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

(* Well-formed types *)

Inductive WFTyp : context TyEnvSource -> PTyp -> Prop := 
  | WFInt : forall Gamma, WFEnv Gamma -> WFTyp Gamma PInt
  | WFFun : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> WFTyp Gamma (Fun t1 t2)
  | WFAnd : forall Gamma t1 t2, WFTyp Gamma t1 -> WFTyp Gamma t2 -> Ortho Gamma t1 t2 -> WFTyp Gamma (And t1 t2)
  | WFVar : forall Gamma x ty, List.In (x,TyDis ty) Gamma -> WFEnv Gamma -> WFTyp Gamma (PFVarT x)
  | WFForAll : forall L Gamma d t,
                 (forall x, not (In x L) -> WFTyp (extend x (TyDis d) Gamma) (open_typ_source t (PFVarT x))) ->
                 WFTyp Gamma d ->
                 WFTyp Gamma (ForAll d t)
  | WFBot : forall Gamma, WFEnv Gamma -> WFTyp Gamma Bot.

Hint Constructors WFTyp.

(* Reflexivity *)
Hint Resolve sint sfun sand1 sand2 sand3 svar SInt SFun SAnd1 SAnd2 SAnd3 SVar SForAll.

(* Definitions borrowed from STLC_Tutorial *)

(* Our source language *)
Inductive PExp :=
  | PFVar  : var -> PExp
  | PBVar  : nat -> PExp                   
  | PLit   : nat -> PExp
  | PLam   : PExp -> PExp
  | PApp   : PExp -> PExp -> PExp
  | PMerge : PExp -> PExp -> PExp
  | PAnn   : PExp -> PTyp -> PExp (* only for the algorithmic version *)
  | PTLam  : PTyp -> PExp -> PExp
  | PTApp  : PExp -> PTyp -> PExp.

(* Free variables *)      

(** Source language **)
Fixpoint fv_source (pExp : PExp) : vars :=
  match pExp with
    | PFVar v => singleton v
    | PBVar _ => empty
    | PLit _ => empty
    | PLam t => fv_source t
    | PApp t1 t2 => union (fv_source t1) (fv_source t2)
    | PMerge t1 t2 => union (fv_source t1) (fv_source t2)
    | PAnn t1 A => fv_source t1
    | PTLam tydis t => union (fv_ptyp tydis) (fv_source t)
    | PTApp t ty => union (fv_source t) (fv_ptyp ty)
  end.


(* Tactics dealing with instantiation of fresh variables, taken from STLC_Tutorial *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => singleton x) in
  let C := gather_vars_with (fun x : PExp => fv_source x) in
  let D := gather_vars_with (fun x : PTyp => fv_ptyp x) in
  let E := gather_vars_with (fun x : STyp => fv_typ x) in
  let F := gather_vars_with (fun (x : SExp var) => fv x) in
  let G := gather_vars_with (fun (x : context (TyEnv STyp)) => dom x) in
  let H := gather_vars_with (fun (x : context TyEnvSource) =>
                              union (dom x) (codom x)) in
  constr:(union A (union B (union C (union D (union E (union F (union G H))))))).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

(* Opening a term "u" with term "t" *)

(** Source language **)
Fixpoint open_rec_source (k : nat) (u : PExp) (t : PExp) {struct t} : PExp  :=
  match t with
  | PBVar i      => if Nat.eqb k i then u else (PBVar i)
  | PFVar x      => PFVar x
  | PLit x       => PLit x                     
  | PLam t1      => PLam (open_rec_source (S k) u t1)
  | PApp t1 t2   => PApp (open_rec_source k u t1) (open_rec_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_source k u t1) (open_rec_source k u t2)
  | PAnn e t     => PAnn (open_rec_source k u e) t
  | PTLam ty t   => PTLam ty (open_rec_source k u t)
  | PTApp t ty   => PTApp (open_rec_source k u t) ty
  end.

Fixpoint open_rec_typ_term_source (k : nat) (u : PTyp) (t : PExp) {struct t} : PExp :=
  match t with
  | PBVar i      => PBVar i
  | PFVar x      => PFVar x
  | PLit x       => PLit x                     
  | PLam t1      => PLam (open_rec_typ_term_source k u t1)
  | PApp t1 t2   => PApp (open_rec_typ_term_source k u t1)
                        (open_rec_typ_term_source k u t2)
  | PMerge t1 t2 => PMerge (open_rec_typ_term_source k u t1)
                          (open_rec_typ_term_source k u t2)
  | PAnn e t     => PAnn (open_rec_typ_term_source k u e) t
  | PTLam ty t   => PTLam ty (open_rec_typ_term_source (S k) u t)
  | PTApp t ty   => PTApp (open_rec_typ_term_source k u t)
                         (open_rec_typ_source k u ty)
  end.

Definition open_source t u := open_rec_source 0 u t.
Definition open_typ_term_source t u := open_rec_typ_term_source 0 u t.

(* Functions on contexts *)

Definition ptyp2styp_tyenv (t : TyEnvSource) : TyEnv STyp :=
  match t with
    | TyDis _ => TyVar _
    | TermV t => TermVar _ (ptyp2styp t)
  end.
    
Definition conv_context (env : context TyEnvSource) : context (TyEnv STyp) :=
  mapctx ptyp2styp_tyenv env.

Notation "'∥' t '∥'" := (conv_context t) (at level 60).

Inductive PTerm : PExp -> Prop :=
  | PTerm_Var : forall x,
      PTerm (PFVar x)
  | PTerm_Lit : forall n,
      PTerm (PLit n)
  | PTerm_Lam : forall L t1,
      (forall x, not (In x L) -> PTerm (open_source t1 (PFVar x))) ->
      PTerm (PLam t1)
  | PTerm_App : forall t1 t2,
      PTerm t1 -> 
      PTerm t2 -> 
      PTerm (PApp t1 t2)
  | PTerm_Merge : forall t1 t2,
      PTerm t1 ->
      PTerm t2 ->
      PTerm (PMerge t1 t2)
  | PTerm_Ann : forall e t,
      PTerm e ->
      PTerm (PAnn e t)
  | PTerm_TLam : forall L t ty,
      (forall x, not (In x L) -> PTerm (open_typ_term_source t (PFVarT x))) ->
      PTerm (PTLam ty t)
  | PTerm_TApp : forall t ty,
      PTerm t ->
      PType ty ->
      PTerm (PTApp t ty).

Hint Constructors PTerm.

Inductive Dir := Inf | Chk.

(* bidirection type-system (algorithmic): 

T |- e => t ~> E     (inference mode: infers the type of e producing target E) (use Inf)
T |- e <= t ~> E     (checking mode: checks the type of e producing target E) (use Chk)

Inspiration for the rules:

https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf

 *)

Inductive has_type_source_alg : context TyEnvSource -> PExp -> Dir -> PTyp -> (SExp var) -> Prop :=
  (* Inference rules *)
  | ATyVar : forall Gamma x ty, WFEnv Gamma -> List.In (x,TermV ty) Gamma -> WFTyp Gamma ty ->
                      has_type_source_alg Gamma (PFVar x) Inf ty (STFVar _ x) 
  | ATyLit : forall Gamma x, WFEnv Gamma -> has_type_source_alg Gamma (PLit x) Inf PInt (STLit _ x)
  | ATyApp : forall Gamma A B t1 t2 E1 E2,
              has_type_source_alg Gamma t1 Inf (Fun A B) E1 ->
              has_type_source_alg Gamma t2 Chk A E2 ->
              has_type_source_alg Gamma (PApp t1 t2) Inf B (STApp _ E1 E2)
  | ATyMerge : forall Gamma A B t1 t2 E1 E2,
                has_type_source_alg Gamma t1 Inf A E1 ->
                has_type_source_alg Gamma t2 Inf B E2 ->
                Ortho Gamma A B ->
                has_type_source_alg Gamma (PMerge t1 t2) Inf (And A B) (STPair _ E1 E2)
  | ATyAnn : forall Gamma t1 A E, has_type_source_alg Gamma t1 Chk A E ->
                         has_type_source_alg Gamma (PAnn t1 A) Inf A E
  | ATyTApp : forall Gamma t A ty d E,
                WFTyp Gamma A ->
                has_type_source_alg Gamma t Inf (ForAll d ty) E ->
                Ortho Gamma A d -> 
                has_type_source_alg Gamma (PTApp t A) Inf (open_typ_source ty A) (STTApp _ E (|A|))
  (* Checking rules *)
  | ATyLam : forall L Gamma t A B E,
               (forall x, not (In x L) -> 
                     has_type_source_alg (extend x (TermV A) Gamma) (open_source t (PFVar x)) Chk B (open E (STFVar _ x))) ->
               WFTyp Gamma A ->
               has_type_source_alg Gamma (PLam t) Chk (Fun A B) (STLam _ E)
  | ATySub : forall Gamma t A B C E,
               has_type_source_alg Gamma t Inf A E ->
               sub A B C ->
               WFTyp Gamma B ->
               has_type_source_alg Gamma t Chk B (STApp _ C E)
  | ATyTLam : forall L Gamma t A d E,
               WFTyp Gamma d ->
               (forall x, not (In x L) -> 
                     has_type_source_alg (extend x (TyDis d) Gamma)
                                         (open_typ_term_source t (PFVarT x))
                                         Chk
                                         (open_typ_source A (PFVarT x))
                                         (open_typ_term E (STFVarT x))) ->
               has_type_source_alg Gamma (PTLam d t) Chk (ForAll d A) (STTLam _ E).

Hint Constructors has_type_source_alg.

Lemma decidability_types :
  forall (A B : PTyp), sumbool (A = B) (not (A = B)).
Proof.
  decide equality.
  case_eq (Nat.eqb n n0); intros.
  left; apply beq_nat_true in H; auto.
  right; apply beq_nat_false in H.
  unfold not; intros H1; inversion H1; contradiction.

  apply VarTyp.eq_dec.
Qed.

Hint Resolve decidability_types.

Module PTypDecidable <: DecidableType.

  Definition t := PTyp.

  Definition eq (x : PTyp) y := (x = y).
      
  Definition eq_refl : forall x : t, eq x x.
    Proof. destruct x; reflexivity. Defined.
    
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. destruct x; destruct y; intros; auto; symmetry; assumption. Defined.
  
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros; rewrite H; assumption. Defined.

  Definition eq_equiv : Equivalence eq :=
    Build_Equivalence _ eq_refl eq_sym eq_trans.
    
  Definition eq_dec : forall x y, sumbool (eq x y) (not (eq x y)).
    Proof. apply decidability_types. Defined.
  
End PTypDecidable.

Import PTypDecidable.
Require Import Coq.Structures.DecidableTypeEx.

Module VarTypDecidable <: DecidableType.

  Definition t := VarTyp.t.

  Definition eq (x : VarTyp.t) y := (VarTyp.eq x y).

  Definition eq_equiv : Equivalence eq.
    Proof. apply VarTyp.eq_equiv. Defined.
    
  Definition eq_refl : forall x : t, eq x x.
    Proof. apply reflexivity. Defined.
    
  Definition eq_sym : forall x y : t, eq x y -> eq y x.
    Proof. intros; symmetry; assumption. Defined.
  
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. intros; rewrite H; assumption. Defined.

  Definition eq_dec : forall x y, sumbool (eq x y) (not (eq x y)).
    Proof. apply VarTyp.eq_dec. Defined.
  
End VarTypDecidable.

Ltac orthoax_inv H :=
  let H' := fresh in
  let m := fresh in
  let H1 := fresh in
  let H2 := fresh in
  inversion H as [H' | m H1 H2 ]; orthoax_inv H1.

(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t1 is not part of OrthoAx *)
Ltac orthoax_inv_l :=
  match goal with
    | H: OrthoAx _ _ |- _ => let H1 := fresh in
                           destruct H as [H1 _]; orthoax_inv H1
  end.

(* Solving goals by inversion, with the form OrthoAx t1 t2,
   where t2 is not part of OrthoAx *)
Ltac orthoax_inv_r := 
  match goal with
    | H: OrthoAx _ _ |- _ => let H1 := fresh in
                           destruct H as [_ [H1 _]]; orthoax_inv H1
  end.

Lemma sound_sub : forall t1 t2, usub t1 t2 -> Sub t1 t2.
Proof.
  intros; induction H; auto.
  - unfold Sub.
    eexists.
    apply_fresh SForAll as x.
    admit.
  - eexists; eauto. 
Admitted.

Lemma complete_sub : forall t1 t2, Sub t1 t2 -> usub t1 t2.
Proof.
  intros; destruct H; induction H; auto.
  - apply_fresh USForAll as x.
    apply H0.
    not_in_L x.
Qed.  

End Definitions.
