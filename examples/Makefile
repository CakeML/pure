all: factorials.exe
.PHONY: all clean cleanAll lib

# Apple Silicon can emulate the x86
ifeq ($(shell uname), Darwin)
CCOPT = -arch x86_64
endif

CAKEOPT = --skip_type_inference=true --exclude_prelude=true --sexp=true

%.exe: %.S lib
	@mkdir -p out
	gcc $(CCOPT) $< lib/basis_ffi.o -o out/$@

%.S: %.hs lib
	cat $< | ./lib/pure | ./lib/cake $(CAKEOPT) > $@

lib:
	$(MAKE) -C lib

clean:
	rm -rf out
	$(MAKE) -C lib clean

cleanAll: clean
	$(MAKE) -C lib cleanAll
