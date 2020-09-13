all: Makefile.coq
	+make -C coq -f Makefile.coq all

clean: Makefile.coq
	+make -C coq -f Makefile.coq clean
	rm -f coq/Makefile.coq
	rm -f coq/Makefile.coq.conf

Makefile.coq: coq/_CoqProject
	cd coq && coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: all clean