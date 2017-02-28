OTT = ott
PERL = perl
OTT_OPTS  = -tex_show_meta false
WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%\n"

TLC = tlc
COQBIN =
INCLUDES=-R $(TLC) TLC
COQC=$(COQBIN)coqc $(INCLUDES)
COQDEP=$(COQBIN)coqdep $(INCLUDES)
COQDOC=$(COQBIN)coqdoc --quiet --utf8 --html

src_ott := $(wildcard *.ott)
src_tex := $(wildcard *.src.tex)
obj_ott := $(src_ott:.ott=.ott.tex)
obj_tex := $(src_tex:.src.tex=.gen.tex)
obj_pdf := $(src_ott:.ott=.pdf)

src_coq := $(wildcard *.v)
dep_src := $(src_coq) $(wildcard $(TLC)/*.v)

.PHONY: latex all clean cleantlc distclean cleancoq
.SUFFIXES: .v .vo
.PRECIOUS: %.ott.tex %.gen.tex

latex: $(obj_pdf)

all: $(src_coq:.v=.vo)

%.pdf: %.gen.tex %.ott.tex otthelper.tex
	latexmk -pdf -outdir=.working -jobname=$(@:.pdf=) $<
	mv .working/$@ .

%.ott.tex: %.ott
	$(OTT) -tex_wrap false $(OTT_OPTS) -o $@ $^
	@$(PERL) -0pi -e 's/\{%(\n|\r\n)\\ottpremise/{%\n/g' $@
	@$(PERL) -pi -e 's/^\\ottpremise/\\\\ /g' $@
	@$(PERL) -pi -e 's/^(.*\\ottlinebreak.*)$$/\\\\$$1/g' $@
	@$(PERL) -pi -e 's/\\Pi\s*\\,/\\Pi/g' $@

%.gen.tex: %.src.tex %.ott
	$(OTT) $(OTT_OPTS) -tex_filter $< $@ $(word 2,$^)
	@$(PERL) -pi -e 'print $(WARN_MSG) if $$. == 1' $@
	@$(PERL) -pi -e 's/\\Pi\s*\\,/\\Pi/g' $@

clean:
	rm -f $(obj_ott) $(obj_tex)
	touch $(src_tex)

.v.vo : .depend
	$(COQC) $<

depend: .depend

.depend : $(dep_src) Makefile
	$(COQDEP) $(dep_src) > .depend

ifeq ($(findstring $(MAKECMDGOALS),depend cleancoq cleantlc distclean),)
include .depend
endif

cleancoq:
	rm -f *.vo .depend *.deps *.dot *.glob .*.aux

cleantlc :
	@rm -f $(TLC)/*.vo $(TLC)/*.glob $(TLC)/*.v.d $(TLC)/.*.aux || echo ok  

distclean : clean cleancoq cleantlc
	rm -Rf $(obj_pdf) .working
