ATL_MODULES := ATL Tactics Relations Invariant Sets ModelCheck Var Map FrapWithoutSets Div Common CommonTactics LetLifting GenPushout Reshape PairElimination
ATLVS      := $(ATL_MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(ATLVS)
	        coq_makefile -R . ATL $(ATLVS) -o Makefile.coq

clean:
	rm -f Makefile.coq* *.vo *.vos *.vok *.glob
