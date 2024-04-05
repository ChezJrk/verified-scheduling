.PHONY: atl codegen tests all clean

all: atl codegen tests

tests: atl codegen
	$(MAKE) -C c

codegen: atl
	$(MAKE) -C codegen

atl:
	$(MAKE) -C atl

clean::
	$(MAKE) -C atl clean
	$(MAKE) -C codegen clean
	$(MAKE) -C c clean
