CC = clang
CFLAGS = -g -Wall
LDFLAGS = -g

GENFILE := gen.out
STEMS	:= $(wildcard *.c)
OBJECTS := $(patsubst %.c,%.o, $(STEMS))

libscheds.a: $(OBJECTS)
	ar rc $@ $^ 
	ranlib $@

%.o: %.c
	$(CC) -g -Wall -ffast-math -O3 -fopenmp -c $^ -o $@

.PHONY: clean scrub

scrub: 
	./cleanoutput.sh $(GENFILE)
	# python cleanoutput.py
	# rm *.BAK

clean:
	rm -f *.o a.out core main *.a *.c *.h *.BAK
