.PHONY: all clean distclean config
.SUFFIXES:

SSRLIB   = $(shell coqc -where)/../ssreflect
INCFLAGS = -I . -I xssr

COQC     = "$(COQBIN)ssrcoq"
COQDEP   = "$(COQBIN)coqdep -c ${INCFLAGS} -I ${SSRLIB}"
COQFLAGS = "$(OPT) ${INCFLAGS} -dont-load-proofs $(COQLIBS) $(OTHERFLAGS) $(COQ_XML) -compile"

COQMAKE  = $(MAKE) -f Makefile.coq

all:
	$(COQMAKE)

config:
	coq_makefile -no-install \
	    $(shell find . -name '*.v' -a \! -wholename './trash/*') \
	    COQC = $(COQC) COQDEP = $(COQDEP) COQFLAGS = $(COQFLAGS) \
	    > Makefile.coq
	$(COQMAKE) depend

clean:
	$(COQMAKE) clean

distclean: clean
	rm -f $(shell find . -name '*~')
	rm -f Makefile.coq

%.vo: %.v
	$(COQMAKE) $@
