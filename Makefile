# Builds the development in dependency order and checks the compiled objects.
# Uses the rocq command when present and the legacy coqc and coqchk otherwise.
# Set COQBIN to the directory holding the binaries, with a trailing slash, if
# they are not on the PATH.
COQBIN ?=
ROCQ   := $(shell command -v $(COQBIN)rocq 2>/dev/null)
ifneq ($(ROCQ),)
COQC   := $(ROCQ) compile
COQCHK := $(ROCQ) check
else
COQC   := $(COQBIN)coqc
COQCHK := $(COQBIN)coqchk
endif
FLAGS  := -Q . BeNice

VS  := Vectors.v Actions.v Sums.v LightCone.v Survival.v Resources.v Judges.v \
       Independence.v Population.v Physical.v Summary.v
VOS := $(VS:.v=.vo)

all: $(VOS)

%.vo: %.v
	$(COQC) $(FLAGS) $<

Actions.vo:      Vectors.vo
Sums.vo:
LightCone.vo:    Vectors.vo Actions.vo Sums.vo
Survival.vo:     LightCone.vo
Resources.vo:    Survival.vo
Judges.vo:       Survival.vo
Independence.vo: Survival.vo
Population.vo:   Resources.vo Judges.vo
Physical.vo:     Resources.vo
Summary.vo:      Resources.vo Judges.vo Independence.vo Population.vo Physical.vo

check: all
	$(COQCHK) -silent -o $(FLAGS) BeNice.Summary

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache .nra.cache .csdp.cache

.PHONY: all check clean
