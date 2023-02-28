all: cake pure factorials
.PHONY: all

# Apple Silicon can emulate the x86
ifeq ($(shell uname), Darwin)
CCOPT = -arch x86_64
endif

cake: cake.S basis_ffi.o
	cc $(CCOPT) -o $@ cake.S basis_ffi.o

pure: pure.S basis_ffi.o
	cc $(CCOPT) -o $@ pure.S basis_ffi.o

basis_ffi.o: basis_ffi.c
	cc $(CCOPT) -c -o $@ basis_ffi.c

factorials: factorials.hs
	./purecake.sh $<

pure.tar.gz:
	wget --no-check-certificate https://www.cse.chalmers.se/~myreen/pure.tar.gz

cake.S: pure.tar.gz
	tar -zxf pure.tar.gz cake.S

pure.S: pure.tar.gz
	tar -zxf pure.tar.gz pure.S

clean:
	-rm -f pure.tar.gz pure cake factorials factorials.S
