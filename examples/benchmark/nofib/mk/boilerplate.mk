# boilerplate.mk --- common variables for the PureLang nofib suite.
#
# Modelled on GHC nofib's mk/boilerplate.mk. Every Makefile in the suite sets
# TOP (the relative path to benchmark/nofib) and includes this file first.
#
# Unlike GHC nofib there is no `ghc`; PureLang programs are built through the
# `pure | cake` pipeline already encoded in examples/Makefile. The suite reuses
# that pipeline rather than reimplementing it (see target.mk).

# Absolute path to the examples/ directory (benchmark/nofib is examples/benchmark/nofib).
EXAMPLES := $(abspath $(TOP)/../..)

# Workload size: fast | norm | slow. Overridable, e.g. `make mode=fast runtests`.
mode ?= norm

# CakeML heap size in MB used when running a benchmark.
HEAP ?= 4096

# Extra flags forwarded to the PureCake frontend (passed through as PUREOPT).
PUREOPT ?=

# Map the chosen mode to the reference-file extension (GHC convention: norm = .stdout).
ifeq ($(mode),fast)
MODE_EXT := faststdout
else ifeq ($(mode),slow)
MODE_EXT := slowstdout
else ifeq ($(mode),norm)
MODE_EXT := stdout
else
$(error invalid mode '$(mode)': expected fast, norm or slow)
endif
