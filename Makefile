# Builds the development in dependency order and checks the compiled objects
# with coqchk. Set COQBIN to the directory holding coqc and coqchk if they are
# not on the PATH, with a trailing slash.
COQBIN ?=
COQC   := $(COQBIN)coqc
COQCHK := $(COQBIN)coqchk
FLAGS  := -Q . BeNice

VS  := Vectors.v Actions.v Sums.v LightCone.v Survival.v Resources.v Judges.v \
       Independence.v Population.v Summary.v
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
Summary.vo:      Resources.vo Judges.vo Independence.vo Population.vo

check: all
	$(COQCHK) -silent -o $(FLAGS) BeNice.Summary

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux .lia.cache .nra.cache .csdp.cache

.PHONY: all check clean
