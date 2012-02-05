AGDA=/usr/bin/agda
AGDA_STDLIB=/usr/share/agda-stdlib
AGDA_OPTS=--allow-unsolved-metas

AGDA_FILES=$(shell find -name '*.agda' | egrep -v "(sketch|_darcs)")
AGDAI_FILES=$(addsuffix .agdai,$(basename $(AGDA_FILES)))

%.agdai : %.agda
	$(AGDA) $(AGDA_OPTS) -i . -i $(AGDA_STDLIB) $<

all : $(AGDAI_FILES)
