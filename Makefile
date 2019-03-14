PYTHON=python2.7

all: Makefile.coq
	+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

theories/global_state.v: theories/global_state.v.rec
	$(PYTHON) script/extract_record_notation.py theories/global_state.v.rec GState > theories/global_state.v

theories/local_state.v: theories/local_state.v.rec
	$(PYTHON) script/extract_record_notation.py theories/local_state.v.rec UState > theories/local_state.v

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: all clean
