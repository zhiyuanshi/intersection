The proofs for the ESOP paper can be found in the Proofs subdirectory.

The Proofs directory contains the Coq Proofs in the paper. The proofs are in
two files:

- ReflexTrans.v (Lemmas 1 and 2)
- Coherence.v   (Lemmas 4 5; Theorems 3, 4, 6 and 7)

The reason for the two files is that the reflexivity and transitivity
proofs are done in the raw subtyping relation (unannotated with
translated terms). The transitivity proof is a little involved and the
additional noise of the translated terms in the subtyping relation
would make the proof longer and more complex. Since translated terms
do not change the subtyping relation, we have instead done it in the
raw relation.
