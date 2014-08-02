(*
data PTyp a = Var a | Forall (a -> PSigma a) | Fun (PSigma a) (PSigma a) | PInt

data PSigma a = And (PSigma a) (PSigma a) | Typ (PTyp a)
*)

Inductive PTyp A :=
  | Var : A -> PTyp A
  | PInt : PTyp A
  | Forall : (A -> PTyp A) -> PTyp A
  | Fun : PTyp A -> PTyp A -> PTyp A
  | And : PTyp A -> PTyp A -> PTyp A.

(*

----------
|t1 <: t2|
----------

a <: a                             Sub-Var

           t1 <: t2
------------------------------     Sub-Forall
forall a . t1 <: forall a . t2

t3 <: t1     t2 <: t4
---------------------              Sub-Arrow
t1 -> t2 <: t3 -> t4

t <: t1   t <: t2
-----------------                  Sub-&1
t <: t1 & t2

t1 <: t
------------                       Sub-&2
t1 & t2 <: t

t2 <: t
------------                       Sub-&3
t1 & t2 <: t

*)

(*
subTyp :: PTyp Int -> PTyp Int -> Int -> Bool
subTyp PInt    PInt             _ = True
subTyp (Var x) (Var y)          _ = x == y
subTyp (Forall f) (Forall g)    i = subSigma (f i) (g i) (i+1)
subTyp (Fun o1 o2) (Fun o3 o4)  i = subSigma o3 o1 i && subSigma o2 o4 i
subTyp _           _            _ = False

subSigma :: PSigma Int -> PSigma Int -> Int -> Bool
subSigma o (And o1 o2) i = subSigma o o1 i && subSigma o o2 i
subSigma o (Typ t)     i = subSigma2 o t i

subSigma2 :: PSigma Int -> PTyp Int -> Int -> Bool
subSigma2 (And o1 o2) t  i = subSigma2 o1 t i || subSigma2 o2 t i
subSigma2 (Typ t1)    t2 i = subTyp t1 t2 i
*)

Require Import Arith.
Require Import Setoid.

Check eq_nat_dec.

Check max.

Fixpoint size (t : PTyp nat) (i : nat) : nat :=
  match t with
      | PInt => 1
      | Var x => 1
      | Forall f => 1 + size (f i) (i+1)
      | And o1 o2 => 1 + max (size o1 i) (size o2 i)
      | Fun o1 o2 => 1 + max (size o1 i) (size o2 i)
  end.

(* Subtyping relation *)

Inductive sub : nat -> PTyp nat -> PTyp nat -> Prop :=
  | SInt : forall i, sub i (PInt nat) (PInt nat)
  | SVar : forall i x, sub i (Var nat x) (Var nat x)
  | SForall : forall i f g, sub (i+1) (f i) (g i) -> sub i (Forall nat f) (Forall nat g)
  (* | SAnd : forall i o1 o2 o3 o4, sub i o1 o3 -> sub i o2 o4 -> sub i (And nat o1 o2) (And nat o3 o4) *)
  | SFun : forall i o1 o2 o3 o4, sub i o3 o1 -> sub i o2 o4 -> sub i (Fun nat o1 o2) (Fun nat o3 o4)
  | SAnd1 : forall i t t1 t2, sub i t t1 -> sub i t t2 -> sub i t (And nat t1 t2)
  | SAnd2 : forall i t t1 t2, sub i t1 t -> sub i (And nat t1 t2) t
  | SAnd3 : forall i t t1 t2, sub i t2 t -> sub i (And nat t1 t2) t.

Definition equiv i t1 t2 := sub i t1 t2 /\ sub i t2 t1.

Lemma reflex : forall t1 i, sub i t1 t1.
Proof.
induction t1; intros.
(* Case Var *)
apply SVar.
(* Case SInt *)
apply SInt.
(* case Forall *)
apply SForall.
apply H.
(* case Fun *)
apply SFun.
apply IHt1_1.
apply IHt1_2.
(* case And *)
apply SAnd1.
apply SAnd2.
apply IHt1_1.
apply SAnd3.
apply IHt1_2.
Defined.

Definition substitutability : 
  forall t1 t2 i, equiv i t2 t1 -> 
    (((forall t, sub i t2 t -> sub i t1 t) /\ (forall t, sub i t t2 -> sub i t t1)) /\ 
    (forall t, sub i t1 t -> sub i t2 t)) /\ (forall t, sub i t t1 -> sub i t t2).
intro. intro. intro. intro.
destruct H.
induction H; split; try split; try split; intros.
(* Case Int *)
exact H.
exact H.
exact H.
exact H.
(* Case Var *)
exact H.
exact H.
exact H.
exact H.
(* Case Forall *)
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd1.
apply IHt1.
apply H6.
apply IHt2.
apply H7.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd2.
apply IHt1.
apply H6.
apply SAnd3.
apply IHt2.
apply H6.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd1.
apply IHt1.
apply H6.
apply IHt2.
apply H7.
induction t; try (inversion H1).
apply SForall.
apply IHsub.
inversion H0.
exact H10.
exact H6.
apply SAnd2.
apply IHt1.
apply H6.
apply SAnd3.
apply IHt2.
apply H6.
(* Case Fun *)
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd1.
apply IHt1.
exact H7. 
apply IHt2.
exact H8.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd2.
apply IHt1.
exact H7. 
apply SAnd3.
apply IHt2.
exact H7.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd1.
apply IHt1.
exact H7. 
apply IHt2.
exact H8.
induction t; try (inversion H2).
inversion H0.
inversion H2.
apply SFun.
apply IHsub1.
apply H14.
apply H7.
apply IHsub2.
exact H16.
exact H23.
apply SAnd2.
apply IHt1.
exact H7. 
apply SAnd3.
apply IHt2.
exact H7.
(* Case And1 *)
induction t.
inversion H0.
apply SAnd2.
apply IHsub1.
exact H7.
exact H2.
apply SAnd3.
apply IHsub2.
exact H7.
exact H2.
inversion H0.
apply SAnd2.
apply IHsub1.
exact H7.
exact H2.
apply SAnd3.
apply IHsub2.
exact H7.
exact H2.
inversion H0.
apply SAnd2.
apply IHsub1.
exact H8.
exact H2.
apply SAnd3. 
apply IHsub2.
exact H8.
exact H2.
apply IHt1.




(*
Inductive Shape : nat -> PTyp nat -> PTyp nat -> Prop :=
  | ShEqual : forall i t, Shape i t t
  | ShAnd1 : forall i t t1 t2, Shape i t t1 -> Shape i t t2 -> Shape i t (And nat t1 t2)
  | ShAnd2 : forall i t t1 t2, Shape i t1 t -> Shape i (And nat t1 t2) t
  | ShAnd3 : forall i t t1 t2, Shape i t2 t -> Shape i (And nat t1 t2) t.

Lemma shapeSub : forall t1 i t2 (s : sub i t1 t2), Shape i t1 t2.
Proof.
intros.
induction s.
(* Case Var *)
apply ShEqual.
apply ShEqual.
apply ShEqual.
apply ShAnd1.
*)

Lemma invAndS1 : forall t t1 t2 i, sub i t (And nat t1 t2) -> sub i t t1 /\ sub i t t2. 
Proof.
induction t; intros.
(* Case Var *)
inversion H.
split.
exact H4.
exact H5.
(* Case Int *)
inversion H.
split.
exact H4.
exact H5.
(* Case Forall *)
inversion H0.
split.
exact H5.
exact H6.
(* Case Fun *)
inversion H.
split.
exact H4.
exact H5.
(* Case And *)
inversion H.
split.
exact H4.
exact H5.
assert (sub i t1 t0 /\ sub i t1 t3).
apply IHt1.
exact H4.
destruct H5.
split.
apply SAnd2.
exact H5.
apply SAnd2.
exact H6.
assert (sub i t2 t0 /\ sub i t2 t3).
apply IHt2.
exact H4.
destruct H5.
split.
apply SAnd3.
exact H5.
apply SAnd3.
exact H6.
Defined.

Lemma invAndS2 : forall t i t1 t2, sub i (And nat t1 t2) t -> sub i t1 t \/ sub i t2 t.
(* Case Var *)
induction t; intros.
inversion H.
left.
exact H4.
right.
exact H4.
(* Case Int *)
inversion H.
left.
exact H4.
right.
exact H4.
(* Case Forall *)
inversion H0.
left.
exact H5.
right.
exact H5.
(* Case Fun *)
inversion H.
left.
exact H4.
right.
exact H4.
(* Case And *)
assert (sub i (And nat t0 t3) t1 /\ sub i (And nat t0 t3) t2).
apply invAndS1.
exact H.
destruct H0.
assert (sub i t0 t1 \/ sub i t3 t1).
apply IHt1.
exact H0.
assert (sub i t0 t2 \/ sub i t3 t2).
apply IHt2.
apply H1.
destruct H2.
destruct H3.
left.
apply SAnd1.
exact H2.
exact H3.
assert (sub i t0 t2 \/ sub i t3 t2).
apply IHt2.
exact H1.
assert (sub i t0 t1 \/ sub i t3 t1).
apply IHt1.
exact H0.
left.
admit.
destruct H3.
admit.
right.
apply SAnd1.
exact H2.
exact H3.
Defined.


Lemma ForallInv : forall t p g i, (forall t : PTyp nat, sub i (Forall nat p) t -> sub i (Forall nat g) t) -> 
                  sub (i + 1) (p i) t -> sub (i + 1) (g i) t.
intros.
assert (sub i (Forall nat g) (Forall nat (fun i => t))).
apply H.
apply SForall.
exact H0.
inversion H1.
exact H5.
Defined.

Lemma FunInv : forall t t1 t2 t3 t4 i, (forall t : PTyp nat, sub i (Fun nat t1 t2) t -> sub i (Fun nat t3 t4) t) -> 
               sub i t2 t -> sub i t4 t.
intros.
assert (exists t10, sub i (Fun nat t3 t4) (Fun nat t10 t)).
exists t1.
apply H.
apply SFun.
apply reflex.
exact H0.
destruct H1.
inversion H1.
exact H8.
Defined.

Lemma funnyLemma : forall t1 t3 i (s : sub i t1 t3) t2, (forall t, sub i t2 t -> sub i t3 t) -> sub i t1 t2.
intro. intro. intro. intro.
induction s; intros.
(* Case PInt *)
apply H.
apply reflex.
(* Case Var *)
apply H.
apply reflex.
(* Case Forall *)
assert (sub i (Forall nat g) t2).
apply H.
apply reflex.
induction t2; try (inversion H0). 
assert (sub (i+1) (f i) (p i)).
apply IHs. intro.
apply (ForallInv _ _ _ _ H).
apply SForall.
exact H6.
apply SAnd1.
apply IHt2_1.
intros.
apply H.
apply SAnd2.
exact H7.
exact H5.
apply IHt2_2.
intros.
apply H.
apply SAnd3.
exact H7.
exact H6.
(* Case Fun *)
assert (sub i (Fun nat o3 o4) t2).
apply H.
apply reflex.
induction t2; try (inversion H0).
apply SFun.
assert (sub i o3 t2_1).
apply IHs1.
admit.
apply IHs2.
intro.
apply (FunInv _ _ _ _ _ _ H). 
admit.




(*
induction t2; try (inversion H0).
assert (forall t : PTyp nat, sub (i+1) (p i) t -> sub (i+1) (g i) t). 
admit.
apply SForall.
apply IHs.
apply H6.
apply SAnd1.
apply IHt2_1.
admit.
exact H5.
apply IHt2_2.
admit.
exact H6.
(* Case Fun *)
assert (sub i (Fun nat o3 o4) t2).
apply H.
apply reflex.
induction t2; try (inversion H0).
apply SFun.
admit.
apply IHs2.
intros.
*)
admit.
admit.
admit.
admit.
admit.
Defined.

Lemma trans : forall t1 t2 i (s : sub i t1 t2) t3, sub i t2 t3 -> sub i t1 t3.
intro. intro. intro. intro.
induction s; intros.
(* Case Var *)
apply H.
(* Case PInt *)
apply H.
(* Case Forall *)
induction t3; try (inversion H).
apply SForall.
apply IHs.
apply H4.
apply SAnd1.
apply IHt3_1.
exact H4.
apply IHt3_2.
exact H5.
(* Case Fun *)
induction t3; try (inversion H).
apply SFun.
apply (funnyLemma _ _ _ _ H4 IHs1). 
apply IHs2.
exact H6.
apply SAnd1.
apply IHt3_1.
exact H4.
apply IHt3_2.
exact H5.
(* Case SAnd *)
(* refactor out *)
induction t3.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
inversion H.
apply IHs1.
exact H5.
apply IHs2.
exact H5.
inversion H.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
assert (sub i (And nat t1 t2) t3_1 /\ sub i (And nat t1 t2) t3_2).
apply invAndS1.
exact H.
destruct H0.
apply SAnd1.
apply IHt3_1.
exact H0.
apply IHt3_2.
exact H1.
apply SAnd2.
apply IHs.
exact H.
apply SAnd3.
apply IHs.
exact H.
Defined.

(*
inversion H.
apply SAnd1.
admit.
apply IHs1.
exact H4.
apply IHs2.
exact H4.
(* Case SAnd2 *)
assert (sub i t1 t3).
apply IHs.
exact H.
apply SAnd2.
exact H0.
(* Case SAnd3 *)
assert (sub i t2 t3).
apply IHs.
exact H.
apply SAnd3.
exact H0.
*)
Defined.



(*
Inductive SubWF : nat -> PTyp nat -> PTyp nat -> Prop :=
  | SubWFBase : forall i t, SubWF i t t
  | SubWFStep : SubWF i t1 t2 -> SubWF SubWF i t1 (And nat t2 t3)

sub i t1 t2 -> t1 = t2 \/   
*)

(* A functional definition : algorithm *)

Fixpoint subTyp (n : nat) (t1 : PTyp nat) (t2 : PTyp nat) (i : nat) : Prop  :=
  match n with
      | 0 => False
      | S m =>
          match (t1,t2) with
            | (PInt,PInt) => True
            | (Var x, Var y) => if (eq_nat_dec x y) then True else False
            | (Forall f, Forall g) => subTyp m (f i) (g i) (i+1)
            | (And o1 o2, And o3 o4) => and (subTyp m o1 o3 i) (subTyp m o2 o4 i)
            | (Fun o1 o2, Fun o3 o4) => and (subTyp m o3 o1 i) (subTyp m o2 o4 i)
            | (_,_) => False
          end
  end.

Lemma implements : forall t1 t2 n i, subTyp (size t1 n) t1 t2 i -> sub i t1 t2.
Proof.
induction t1; intros.
simpl in H.
destruct t2; try destruct H.
destruct (eq_nat_dec a n0).
rewrite e.
apply SVar. reflexivity.
destruct H.
destruct t2; try destruct H.
