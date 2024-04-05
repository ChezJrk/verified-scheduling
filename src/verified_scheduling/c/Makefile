.PHONY: coq clean lib test

top: lib test

test: MakefileTest.coq
	        $(MAKE) -f MakefileTest.coq > test/gen.out
			$(MAKE) -C test scrub
			$(MAKE) -C test
			

lib: MakefileLib.coq
	        $(MAKE) -f MakefileLib.coq > lib/gen.out
			$(MAKE) -C lib scrub
			$(MAKE) -C lib libscheds.a


MakefileLib.coq: Makefile GenLib.v
	        coq_makefile -R ../codegen Codegen -R ../atl ATL -R ../../examples Examples -R . Lib GenLib.v -o MakefileLib.coq 2> /dev/null

MakefileTest.coq: Makefile GenTest.v
	        coq_makefile -R ../codegen Codegen -R ../atl ATL -R ../../examples Examples -R . Test GenTest.v -o MakefileTest.coq 2> /dev/null

clean:
	$(MAKE) -C lib clean
	$(MAKE) -C test clean
	rm -f Makefile*.coq* *.vo *.vos *.vok *.glob
