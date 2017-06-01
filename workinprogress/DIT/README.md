# Coherent Subtyping with Typing

This works extends Linus' work "Subtyping with Typing" with disjointness.
The syntax for abstractions and products are extended with a disjoint constraint.
The environments now associates a variable to its respective type and constraint.

## Typed Subtyping 

Typed subtyping contains typing, well-formedness and subtyping unified in one judgement. 
Here follows a few informal explanations of some rules (the ones different from original):

**App**
An application (e1 A) is a subtype of application (e2 A) when e1 <: e2 under some pi-type.
Notice the well-formed checks for type A and the disjointness constraint in the pi-type. 

**Pi**
The rule is similar to the original typed subtyping. 
It is covariant on the bodies and contravariant on the constraints.

**Merge**
This rule now ensures the merge operator is only applied at the "term-level".

## Typed Disjointness

The rules for disjointness are separated into two different judgements, although they
could easily be merged together. 
Typed disjointness deals with two expressions composed by the same construct, whereas non-structural disjointness deals with different constructs.
In comparison to previous work, the disjointness relation now includes the type/universe
of both expressions.

Next follows a few informal explanations of some rules.

Firstly, the structural rules.

**Lam1** 
Straightforward definition that respects the typed subtyping judgement.

**Pi** 
Two abstractions are disjoint if their bodies are disjoint under a new environment. 
Note how we are assuming that the type/universe of the variable does not play a role in typing/disjointness... 

**App**
The tricky rule. 
We could allow AppAlternative as the first naive version, but that rule will not cover all cases which are disjoint. 
For example, there might be two applications that do not have the same arguments, but live in the same type/universe.
Consider, for example, the (incomplete) disjointness derivation for the following types:

--------------------------------- TDBaseType 
x * T : STAR |- Char * Int : STAR 
----------------------------------------------------------------------- TDLam1
(\x * T : STAR . Char) * (\x * T : STAR . Int) : pi x * T : STAR . STAR          ...
------------------------------------------------------------------------------------ TDApp 
(\x * T : STAR . Char) Char : STAR * (\x * T : STAR . Int) Int : STAR

This derivation is possible with the App rule, but not with AppAlternative. 
The syntactic restriction (C[x -> A] = C[x -> B]) is used to ensure the types/universes of the terms are consistent (and perhaps could be weakened too?).

Also, note on how might need to type e1 and e2 to figure out their type/universe, which should be input to this algorithmic system. 

The rest of the rules in this judgement are quite straightforward and similar to Fi.

Next, the non-structural rules.
Again, these rules have to ensure the expressions live in the same type/universe. 
The "tricky" part is again the application, which might live in any type.

**StarApp**
Applications living in STAR are disjoint with STAR itself.

**AppLam**
Applications and abstractions living in the same pi-type are always disjoint.

**AppPi**
Applications living in STAR and pi types are always disjoint.

**AppMerge**
Applications living in intersection types are always disjoint with merges.

The other rules follow the same structure as defined in Fi.
Observation: rules And1, And2, Top, TopSym are also non-structural.

# Building the document
To build the pdf, please type `make subanddis.pdf`.
Make sure you have ott and LaTeX installed :)

# Disclaimer
This work was heavily based on Linus' work "Subtyping with Typing".
Infrastructure taken from his "subtype" repository, forked here for convenience.
Thanks Linus!
