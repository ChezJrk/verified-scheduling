MODULES := Reify ReifyExamples InferPad
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	        coq_makefile -R ../../verified_scheduling/codegen Codegen -R ../proof Lower -R ../../verified_scheduling/atl ATL -R ../../examples Examples -R . Inferpad $(VS) -o Makefile.coq 2> /dev/null

clean:
	rm -f Makefile.coq* *.vo *.vos *.vok *.glob
