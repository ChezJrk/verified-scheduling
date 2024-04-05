MODULES := IdentParsing Normalize CheckSafe NatToString IntToString CodeGen
VS := $(MODULES:%=%.v)
LIB := GenLib
TEST := GenTest

.PHONY: coq clean lib test top

coq: Makefileg.coq
	$(MAKE) -f Makefileg.coq


Makefileg.coq: Makefile $(VS)
	$(MAKE) -C ../../examples
	coq_makefile -R ../atl ATL -R ../../examples Examples -R . Codegen $(VS) -o Makefileg.coq 2> /dev/null


clean:
	rm -f Makefile.coq* *.vo *.vos *.vok *.glob
