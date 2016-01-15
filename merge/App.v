Set Implicit Arguments.

Inductive typ : Set :=
  | typ_arrow : typ -> typ -> typ
  | typ_inter : typ -> typ -> typ.

Inductive Sub : typ -> typ -> Prop :=.

Fixpoint appl (t1 : typ) (t2 : typ) : Prop :=
  match t1 with
    | typ_arrow t3 t4 => t2 = t3
    | typ_inter t3 t4 => (appl t3 t2 /\ not (appl t4 t2)) \/ (not (appl t3 t2) /\ appl t4 t2)
  end.
