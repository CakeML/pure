all: factorials.exe
.PHONY: all check clean download

# Apple Silicon can emulate the x86
ifeq ($(shell uname), Darwin)
CCOPT = -arch x86_64
endif

CAKEOPT = --skip_type_inference=true --exclude_prelude=true --sexp=true
LDLIBS = -lm

ifeq ($(DEBUG),1)
  CAKEOPT += --emit_empty_ffi=true
  CCOPT += -DDEBUG_FFI
endif

%.exe: %.S lib/basis_ffi.o
	@mkdir -p $(dir out/$@)
	$(CC) $(CCOPT) $< lib/basis_ffi.o -o out/$@ $(LDLIBS)

%.S: %.hs lib/pure lib/cake
	cat $< | ./lib/pure $(PUREOPT) | ./lib/cake $(CAKEOPT) > $@

check: $(patsubst %.hs,%.exe,$(wildcard *.hs)) \
       $(patsubst %.hs,%.exe,$(wildcard prelude/*.hs))

lib/pure: lib/pure.S lib/basis_ffi.o
	$(CC) $(CCOPT) -o $@ $^ $(LDLIBS)

lib/cake: lib/cake.S lib/basis_ffi.o
	$(CC) $(CCOPT) -o $@ $^ $(LDLIBS)

lib/basis_ffi.o: lib/basis_ffi.c
	$(CC) $(CCOPT) -c -o $@ $^ $(LDLIBS)

lib/pure.S:
	@if [ ! -f "../compiler/binary/$(@F)" ] ; then $(MAKE) download ; else cp ../compiler/binary/$(@F) $@ ; fi

download:
	@echo "$(red)Could not find \`pure.S\`. Downloading the latest version from PureCake's GitHub releases.$(reset)"
	wget -q https://github.com/cakeml/pure/releases/latest/download/pure.S -P lib

lib/cake.S:
	wget -q https://github.com/cakeml/cakeml/releases/latest/download/cake-x64-64.tar.gz
	@tar -zxf cake-x64-64.tar.gz --directory $(@D) cake-x64-64/$(@F) --strip-components 1
	@rm cake-x64-64.tar.gz

clean:
	rm -rf out lib/basis_ffi.o lib/cake lib/pure lib/cake.S lib/pure.S

red = \033[0;31m
reset = \033[0m
