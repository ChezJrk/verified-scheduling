CC = clang
CFLAGS = -Wall -g -I../lib -fopenmp
LDFLAGS = -g -L ../lib
LDLIBS = -lscheds
INCLUDES = -I../lib

TESTS   := $(wildcard *.c)
GENFILE := gen.out

.PHONY: scrub clean run

OBJECTS := $(patsubst %.c,%.o, $(TESTS))
EXECUTABLES := $(patsubst %.c,%,$(TESTS))

run: tests
	./run_tests.sh

tests: $(EXECUTABLES)

%: %.o

scrub:
	./cleanoutput.sh $(GENFILE)

clean:
	rm -f *.o a.out main revecho core *.c $(EXECUTABLES) $(GENFILE)
