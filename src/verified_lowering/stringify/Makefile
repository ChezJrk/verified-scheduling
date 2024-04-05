MODULES := Stringify
VS      := $(MODULES:%=%.v)

.PHONY: coq clean top

top: coq lib test

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	        coq_makefile -R ../../verified_scheduling/codegen Codegen -R ../proof Lower -R ../../verified_scheduling/atl ATL -R ../../examples Examples -R . Stringify $(VS) -o Makefile.coq 2> /dev/null

lib: coq MakefileLib.coq
	        $(MAKE) -f MakefileLib.coq > lib/gen.out
			$(MAKE) -C lib scrub
			$(MAKE) -C lib libscheds.a

test: coq MakefileTest.coq
	        $(MAKE) -f MakefileTest.coq > test/gen.out
			$(MAKE) -C test scrub
			$(MAKE) -C test	

MakefileTest.coq: Makefile GenTest.v
	        coq_makefile -R ../../verified_scheduling/codegen Codegen -R ../../verified_scheduling/atl ATL -R ../../examples Examples -R . Test GenTest.v -o MakefileTest.coq 2> /dev/null

MakefileLib.coq: Makefile GenLib.v
	coq_makefile -R ../proof Lower -R ../inferpad Inferpad -R ../../verified_scheduling/atl ATL -R ../../verified_scheduling/codegen Codegen -R ../../examples Examples -R . Stringify GenLib.v -o MakefileLib.coq 2> /dev/null

clean:
	rm -f Makefile*.coq* *.vo *.vos *.vok *.glob
	$(MAKE) -C lib clean	
	$(MAKE) -C test clean	


