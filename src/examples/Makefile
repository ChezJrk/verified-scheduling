MODULES := Im2col Convolution GatherScatter Matmul TensorAdd Blur
VS      := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	        $(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	        coq_makefile -arg -w -arg none -R ../verified_scheduling/atl ATL -R . Examples $(VS) -o Makefile.coq  2> /dev/null

clean:
	rm -f Makefile.coq* *.vo *.vos *.vok *.glob
