.SUFFIXES: .vo .v

.PHONY: default config clean clean-dep clean-ml distclean clean-doc tags doc install-doc install-dist install-deps targz graph wc print-unused extracted all run test benchmark timing wc dep-versions

# parse the -j flag if present, set jobs to 1 oterwise
JFLAG=$(patsubst -j%,%,$(filter -j%,$(MFLAGS)))
JOBS=$(if $(JFLAG),$(JFLAG),4)

MAKECOQ := +$(MAKE) -r -f Makefile.coq

VFILES := $(shell find . -name \*.v | grep -v .\#)

default: all

all: .depend Makefile.coq
	$(MAKECOQ)

.depend: $(VFILES) 
	@echo "Analyzing Coq dependencies in" $(VFILES)
	coqdep -f _CoqProject $^ > .depend


Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject $(VFILES) -o Makefile.coq

clean:
	rm -f `find . -name \*~`
	-$(MAKECOQ) clean
	rm -rf `find . -name .coq-native -o -name .\*.aux -o -name \*.time -o -name \*.cache -o -name \*.timing`

clean-dep:
	rm -f .depend
	rm -f `find . -name \*.v.d`

distclean: clean clean-dep
	rm -f Makefile.coq Makefile.coq.conf

wc:
	coqwc $(VFILES)

%.vo: %.v
	$(MAKECOQ) $@

%:
	$(MAKECOQ) $@

