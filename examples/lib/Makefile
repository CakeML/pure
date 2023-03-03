all: cake pure
.PHONY: all clean cleanAll

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
	-rm -rf basis_ffi.o cake pure cake.S pure.S

cleanAll: clean
	-rm -f pure.tar.gz
