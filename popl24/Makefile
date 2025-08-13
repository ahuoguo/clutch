SRC_DIRS := 'theories'
EXT_DIRS := 'external'
VFILES := $(shell find $(EXT_DIRS) $(SRC_DIRS) -name '*.v' -a '!' -name '*'.\#'*')
COQC := coqc
Q:=@

# extract global arguments for Coq from _CoqProject
COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)

# TODO: Not exctly sure why? but I need to run `make all` before `make coqdoc`
Makefile.coq: _CoqProject $(VFILES)
	$(Q)coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq -docroot .

-include coqdocjs/Makefile.doc

coqdoc: Makefile.coq

all: $(VFILES:.v=.vo)

.coqdeps.d: $(VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(VFILES) > $@

# do not try to build dependencies if cleaning or just building _CoqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
include .coqdeps.d
endif

%.vo: %.v _CoqProject | .coqdeps.d
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vok $(COQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(EXT_DIRS) $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	rm -rf html
	rm -f Makefile.coq Makefile.coq.conf
	rm -f .coqdeps.d

zip:
	git archive -o coq-clutch.zip main

.PHONY: clean zip
