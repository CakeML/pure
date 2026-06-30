# target.mk --- rules for a single benchmark directory.
#
# Included (after boilerplate.mk) by each benchmark's Makefile, which must set:
#   PROG       the benchmark name (matches <PROG>.hs and the directory name)
#   FAST_ARG   single command-line argument for the `fast` workload
#   NORM_ARG     "          "          "      "  `norm`      "
#   SLOW_ARG     "          "          "      "  `slow`      "
#
# PureLang programs take their workload as one command-line argument (read via
# #(cline_arg)), not on stdin, so there are no .stdin files; the per-mode args
# live here in the Makefile (the GHC-nofib idiom of baking *_OPTS into the
# Makefile). The mode's reference output is <PROG>.<MODE_EXT>.

# Select the argument and reference extension for the current mode.
ifeq ($(mode),fast)
ARG := $(FAST_ARG)
else ifeq ($(mode),slow)
ARG := $(SLOW_ARG)
else
ARG := $(NORM_ARG)
endif

REF := $(PROG).$(MODE_EXT)

# Locate this benchmark relative to examples/ so we can drive the examples
# Makefile (which bootstraps lib/{pure,cake,basis_ffi.o} and runs pure | cake).
REL    := $(patsubst $(EXAMPLES)/%,%,$(abspath $(CURDIR)))
EXE    := $(EXAMPLES)/out/$(REL)/$(PROG).exe
SUBSET := $(notdir $(patsubst %/,%,$(dir $(abspath $(CURDIR)))))
LABEL  := $(SUBSET)/$(PROG)

.PHONY: all build runtests check accept clean list

all: build

# Compile via the proven examples pipeline: cat PROG.hs | pure | cake -> PROG.exe
# Quiet on success; on failure, show the captured build log.
build:
	@$(MAKE) -C $(EXAMPLES) $(REL)/$(PROG).exe PUREOPT='$(PUREOPT)' > $(PROG).buildlog 2>&1 \
	   || { echo 'BUILD FAILED ($(LABEL)):'; cat $(PROG).buildlog; rm -f $(PROG).buildlog; exit 1; }
	@rm -f $(PROG).buildlog

# Run at the current mode and diff stdout against the reference (never aborts).
runtests check: build
	@CML_HEAP_SIZE=$(HEAP) $(EXE) '$(ARG)' > $(PROG).runout 2>/dev/null; \
	 if [ ! -f $(REF) ]; then \
	   printf '%-26s %s (no reference; run `make mode=%s accept`)\n' '$(LABEL)' 'NOREF' '$(mode)'; \
	 elif diff -q $(REF) $(PROG).runout >/dev/null 2>&1; then \
	   printf '%-26s %s  arg=%s\n' '$(LABEL)' 'PASS' '$(ARG)'; \
	 else \
	   printf '%-26s %s  arg=%s\n' '$(LABEL)' 'FAIL' '$(ARG)'; \
	 fi; \
	 rm -f $(PROG).runout

# Regenerate the reference output for the current mode from a fresh run.
accept: build
	@CML_HEAP_SIZE=$(HEAP) $(EXE) '$(ARG)' > $(REF)
	@printf 'accepted %-22s (mode=%s, arg=%s)\n' '$(REF)' '$(mode)' '$(ARG)'

clean:
	@rm -f $(PROG).runout
	@rm -rf $(EXAMPLES)/out/$(REL)

list:
	@echo '$(LABEL)'
