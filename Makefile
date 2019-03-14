PYTHON=python2.7

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

theories/GlobalState.v: theories/GlobalState.v.rec
	$(PYTHON) script/extract_record_notation.py theories/GlobalState.v.rec GState > theories/GlobalState.v

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean
