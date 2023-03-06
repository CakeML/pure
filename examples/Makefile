all: factorials.exe
.PHONY: all clean

# Apple Silicon can emulate the x86
ifeq ($(shell uname), Darwin)
CCOPT = -arch x86_64
endif

CAKEOPT = --skip_type_inference=true --exclude_prelude=true --sexp=true

%.exe: %.S lib/basis_ffi.o
	@mkdir -p $(dir out/$@)
	gcc $(CCOPT) $< lib/basis_ffi.o -o out/$@

%.S: %.hs lib/pure lib/cake
	cat $< | ./lib/pure | ./lib/cake $(CAKEOPT) > $@

lib/pure: lib/pure.S lib/basis_ffi.o
	cc $(CCOPT) -o $@ $^

lib/cake: lib/cake.S lib/basis_ffi.o
	cc $(CCOPT) -o $@ $^

lib/basis_ffi.o: lib/basis_ffi.c
	cc $(CCOPT) -c -o $@ $^

lib/pure.S:
	cp ../compiler/binary/$(@F) $@

lib/cake.S:
	wget -q https://github.com/cakeml/cakeml/releases/latest/download/cake-x64-64.tar.gz
	@tar -zxf cake-x64-64.tar.gz --directory $(@D) cake-x64-64/$(@F) --strip-components 1
	@rm cake-x64-64.tar.gz

clean:
	rm -rf out lib/basis_ffi.o lib/cake lib/pure lib/cake.S lib/pure.S

