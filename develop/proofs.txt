        // Typing produces well-formedness types //

Notations:
    "[B/α] A":     the free variable substitution of B for α in A
    "unify(A, B)": the substitutions produced by the unification of two types A and B
    "ftv(Γ)":      the set of type variables bound in Γ
    "Γ ⊢ [A/α]":  [A/α] is a valid substitution in Γ

Definition (Substitution of context).
    [B/α] ϵ          = ϵ
    [B/α] (Γ, α * A) = [B/α] Γ
    [B/α] (Γ, β * A) = [B/α] Γ, β * [B/α] A

Definiton (Valid substitution).
    We say [A/α] is a valid substitution in Γ (denoted as Γ ⊢ [A/α]) if one
    of the following is true:
    (1) α ∉ ftv(Γ)
    (2) α * B ∈ Γ, and Γ ⊢ A * B.

Definition (Disjointness).
    Γ ⊢ A * B if one of the following is true:
    (1) Both A and B are closed, and
        ∄ C such that A <: C and B <: C
    (2) One of A and B is not closed, and
        [C/α] Γ ⊢ [C/α] A * [C/α] B for all valid [C/α]
        where α is the first type variable in Γ such that α ∈ ftv(A) ∪ ftv(B)

Lemma (Valid substitution preserves disjointness).
    If Γ ⊢ A * B and Γ ⊢ [C/α],
    then Γ ⊢ [C/α] A * [C/α] B.
Proof.
    Case α ∉ ftv(A) ∪ ftv(B):
        Since [C/α] A and [C/α] B are just A and B, respectively, Γ ⊢ [C/α] A *
        [C/α] B trivially holds.

    Case α ∈ ftv(A) ∪ ftv(B):
        ...
Q.E.D.

Lemma (Valid substitution preserves well-formedness).
    If Γ ⊢ A and Γ ⊢ [C/α],
    then Γ ⊢ [C/α] A.
Proof.
    By induction of the derivation of Γ ⊢ [C/α] A.
    Case (WF-Inter):
        Γ ⊢ A    Γ ⊢ B    Γ ⊢ A * B
        ---------------------------- (WF-Inter)
            Γ ⊢ A & B

        By the premise and induction hypothesis, Γ ⊢ [C/α] A and Γ ⊢ [C/α] B. By
        the premise and Lemma (Valid substitution preserves disjointness), Γ ⊢
        [C/α] A * [C/α] B. Therefore Γ ⊢ [C/α] A & [C/α] B, and by the
        definition of substitution, Γ ⊢ [C/α] A & B.

    The other cases are trivial.
Q.E.D.

Lemma (Typing produces well-formedness types).
    If Γ ⊢ e : A,
    then Γ ⊢ A.
Proof.
    Case (Ty-TApp):
        Γ ⊢ e : ∀(α * B). C    Γ ⊢ A    Γ ⊢ [A/α]
        ------------------------------------------- (Ty-TApp)
                Γ ⊢ e A : [A/α] C

        By Lemma (Valid substitution preserves well-formedness), Γ ⊢ [A/α] C.

    The other cases are trivial.
Q.E.D.
