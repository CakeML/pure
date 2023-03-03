all: factorials.exe
.PHONY: all clean cleanAll

# Apple Silicon can emulate the x86
ifeq ($(shell uname), Darwin)
CCOPT = -arch x86_64
endif

CAKEOPT = --skip_type_inference=true --exclude_prelude=true --sexp=true

%.exe: %.S basis_ffi.o
	gcc $(CCOPT) $< basis_ffi.o -o $@

%.S: %.hs pure cake
	cat $< | ./pure | ./cake $(CAKEOPT) > $@

cake: basis_ffi.o | cake.S
	cc $(CCOPT) -o $@ cake.S basis_ffi.o

pure: basis_ffi.o | pure.S
	cc $(CCOPT) -o $@ pure.S basis_ffi.o

cake.S pure.S &: pure.tar.gz
	tar -zxf pure.tar.gz

pure.tar.gz:
	wget --no-check-certificate https://www.cse.chalmers.se/~myreen/pure.tar.gz

basis_ffi.o: basis_ffi.c
	cc $(CCOPT) -c -o $@ basis_ffi.c

clean:
	-rm -f *.exe basis_ffi.o cake pure cake.S pure.S

cleanAll: clean
	-rm -f pure.tar.gz
