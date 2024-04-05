MODULES := Count
VS      := $(MODULES:%=%.v)

.PHONY: clean

out.csv: Makefile.coq
	        $(MAKE) -f Makefile.coq > out.csv
			./cleanoutput.sh out.csv
			cat out.csv

Makefile.coq: Makefile $(VS)
	        coq_makefile -R ../inferpad Inferpad -R ../../verified_scheduling/codegen Codegen -R ../proof Lower -R ../../verified_scheduling/atl ATL -R ../../examples Examples -R . Count $(VS) -o Makefile.coq 2> /dev/null

clean:
	rm -f Makefile*.coq* *.vo *.vos *.vok *.glob *.csv
