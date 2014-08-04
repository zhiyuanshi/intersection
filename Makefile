DIR = Language/Inter

LEXERS  = $(DIR)/Lexer.hs
PARSERS = $(DIR)/TypeParser.hs $(DIR)/ExprParser.hs

.PHONY: all
all: $(LEXERS) $(PARSERS)

ALEX  = alex --ghc
HAPPY = happy --ghc --info

$(LEXERS): %.hs : %.x
	$(ALEX) $<

$(PARSERS): %.hs : %.y
	$(HAPPY) $<

.PHONY: clean
clean:
	rm -f $(LEXERS) $(PARSERS)
