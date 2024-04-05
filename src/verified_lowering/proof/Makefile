MODULES := ListMisc Range Constant Array Zexpr Bexpr Result Sexpr Meshgrid VarGeneration InterpretReindexer Injective WellFormedEnvironment WellFormedReindexer ResultToArrayDelta WellFormedAllocation ContextsAgree ATLDeep Pad AssignNoOverwrite LowerCorrect LowerExists Correct
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

assumptions: MakefileA.coq
	$(MAKE) -f MakefileA.coq

MakefileA.coq: Makefile.coq
	        coq_makefile -R ../../verified_scheduling/atl ATL -R . Lower Assumptions.v -o MakefileA.coq 2> /dev/null

Makefile.coq: Makefile $(VS)
	        coq_makefile -R ../../verified_scheduling/atl ATL -R . Lower $(VS) -o Makefile.coq 2> /dev/null

clean:
	rm -f Makefile.coq* *.vo *.vos *.vok *.glob
