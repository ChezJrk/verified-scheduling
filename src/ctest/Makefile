CC = clang
CFLAGS = -Wall -g -I../clib -fopenmp
LDFLAGS = -g -L ../clib
LDLIBS = -lscheds
INCLUDES = -I../clib

TESTS   := $(wildcard *.c)
GENFILE := gen

.PHONY: scrub clean

OBJECTS := $(patsubst %.c,%.o, $(TESTS))
EXECUTABLES := $(patsubst %.c,%,$(TESTS))

tests: $(EXECUTABLES)

%: %.o

scrub:
	./cleanoutput.sh $(GENFILE)

clean:
	rm -f *.o a.out main revecho core *.c $(EXECUTABLES) $(GENFILE)
