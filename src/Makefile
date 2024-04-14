.PHONY: test lowtest padtest low examples atl clean all assumptions

all: libs test assumptions

assumptions: low
	$(MAKE) -C verified_lowering assumptions

libs: atl examples codegen low

test: padtest lowtest low figure

figure: atl examples codegen low padtest
	$(MAKE) -C verified_lowering/count_reshape out.csv

lowtest: atl examples codegen low padtest figure
	$(MAKE) -C verified_lowering/stringify lib
	$(MAKE) -C verified_lowering/stringify test

padtest: examples low
	$(MAKE) -C verified_lowering/inferpad

codegen: atl
	$(MAKE) -C verified_scheduling/codegen

low: atl
	$(MAKE) -C verified_lowering/proof

examples: atl
	$(MAKE) -C examples

atl:
	$(MAKE) -C verified_scheduling/atl

clean:
	$(MAKE) -C verified_scheduling clean
	$(MAKE) -C verified_lowering clean
	$(MAKE) -C examples clean
