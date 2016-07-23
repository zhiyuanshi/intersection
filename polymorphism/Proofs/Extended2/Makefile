default: coq

all: coq 

coq: systemf language infrastructure subtyping disjointness typing extended 

systemf: SystemF.vio 
language: Language.vio
infrastructure: Infrastructure.vio
subtyping: Subtyping.vio 
disjointness: Disjointness.vio 
typing: Typing.vio
extended: Extended.vio

SystemF.vio: SystemF.v
	coqc -quick SystemF.v

Language.vio: SystemF.vio Language.v
	coqc -quick Language.v

Infrastructure.vio: Language.vio Infrastructure.v
	coqc -quick Infrastructure.v

Subtyping.vio: Infrastructure.vio Subtyping.v
	coqc -quick Subtyping.v

Disjointness.vio: Subtyping.vio Disjointness.v
	coqc -quick Disjointness.v

Typing.vio: Disjointness.vio Typing.v
	coqc -quick Typing.v

Extended.vio: Typing.vio Extended.v
	coqc -quick Extended.v

clean:
	rm -f *.vo *.vio *.glob
