.PHONY:

all: correct infer

test: correct assumptions
	$(MAKE) -C stringify

assumptions:
	$(MAKE) -C proof assumptions

correct:
	$(MAKE) -C proof

infer: proof
	$(MAKE) -C inferpad

clean::
	$(MAKE) -C proof clean
	$(MAKE) -C inferpad clean
	$(MAKE) -C stringify clean
	$(MAKE) -C count_reshape clean
