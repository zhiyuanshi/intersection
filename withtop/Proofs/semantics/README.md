# Semantics

The direct operational semantics are documented in the `doc` folder.

* bired.ott / bired.pdf
* redsimpl.ott / redsimpl.pdf

Both systems use the idea of "typed values": values + type inference algorithm without subsumption.
This is particularly necessary in the application of subtyping.
It assumes all annotations in a given program are kept and used to execute it.

Summary of redsimpl: 
This system makes use of annotations during computation. 
Values are always enclosed with an annotation.
This follows the idea in red.pdf, which was using two annotations.

Summary of bired: This system follows more closely the bi-directional algorithm. 
Values can be checked or inferred with a type, also without subtyping. The abstraction rule assumes the term has been previously checked. 
The two reduction judgements are also mimicking the directions in the bidir algorithm. 


## Description of the different systems and their respective scripts

The Coq scrips were taken from the Disjoint Intersection Types paper (at https://github.com/jalpuim/disjoint-intersection-types/tree/master/proofs ).
They were updated to use the TLC (at http://www.chargueraud.org/softs/tlc/ ). 
Improved versions of old scripts using the TLC library:

* STLCNew.v 
* CoherenceBasicBDNew.v 

The new scripts are listed below.
Apart from some obvious proofs which are still missing, the Semantics scripts all have similar holes in their respective consistency lemmas w.r.t. lambda-calculus.
The cases missing are: adding/removing "harmless" annotations, which amounts to proving that "if A <: A ~> c then c = id"; the beta-reduction case; and the case for function subtyping. 
Relevant scripts are:

* STLCred.v - common lemmas and definitions for reduction relations in the STLC. Follows scripts defined at http://www.chargueraud.org/softs/ln/ .
* SemanticsFullRed.v - redsimpl.ott using full-beta equality. The stuck lemma is "consistency_fullred".
* SemanticsBiRed.v - bired.ott using full-beta equality. The stuck lemma is "consistency_fullred".  
* SemanticsBiRedEta.v - same as SemanticsBiRed.v but uses full-beta equality with eta-contraction. Stuck lemma: "consistency_fulletared".

I was mainly stuck at proving "if A <: A ~> c then c = id", since this is not true according to equality in cbv lambda-calculus, due to the function case.
For example:

Int -> Int <: Int -> Int ~> \f. \x. id ( f ( id x ) )

which is not equal to \x. x.
This equality can be established using eta-contraction.
However, the proof is still non-trivial due the induction hypothesis in the and case.
You might need to show some property on coercions for And's, something like "if A & B <: A ~> c then c = fst".

Obs: Maybe the theorem specification could be weakened or modified?

## Compiling the Coq scripts

To compile a Coq file `filename.vo`:

1. CD into the folder tlc and run `make`.
2. CD back into root directory.
3. Run `make filename.vo`. 

All scripts were tested with Coq 8.5.
