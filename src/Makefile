LIB_MODULES := Tactics ATL Div Common CommonTactics LetLifting PairElimination GenPushout Reshape IdentParsing NatToString IntToString Convolution GatherScatter Im2col Blur CheckSafe Normalize CodeGen
EXAMPLE_MODULES := Convolution GatherScatter Im2col Blur
GENLIB_MODULES := GenLib

VSE		:= $(EXAMPLE_MODULES:%=%.v)
VS		:= $(LIB_MODULES:%=%.v)
VSL		:= $(GENLIB_MODULES:%=%.v)

.PHONY: coq clean clib

exx: Makefilee.coq
	$(MAKE) -f Makefilee.coq

ctest: Makefilet.coq
	touch GenTest.v
	$(MAKE) -C ctest clean
	$(MAKE) -s -f Makefilet.coq > ctest/gen
	$(MAKE) -C ctest scrub

clib/gen.out: Makefilel.coq
	touch GenLib.v
	$(MAKE) -s -f Makefilel.coq > clib/gen.out

clib: clib/gen.out
	$(MAKE) -C clib clean
	$(MAKE) -C clib scrub
	$(MAKE) -C clib libscheds.a

Makefilel.coq: coq $(VSL)
	coq_makefile -R . ATL $(VSL) -o Makefilel.coq

Makefilet.coq: coq GenTest.v
	coq_makefile -R . ATL GenTest.v -o Makefilet.coq

Makefilee.coq: coq Makefile $(VSE)
	coq_makefile -R . ATL $(VSE) -o Makefilee.coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -R . ATL $(VS) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefilee.coq Makefilet.coq Makefilel.coq *.vo*
