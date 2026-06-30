# Top-level Makefile for the PureLang nofib suite.
#
# Usage (see README.md):
#   make all                  build every benchmark
#   make runtests             build, run and check everything at mode=norm
#   make mode=fast runtests   the quick workloads (smoke test)
#   make accept               regenerate every reference for the current mode
#   make clean
#   make -C imaginary/tak runtests    just one benchmark
#
# Mirrors GHC nofib's layout: a top-level Makefile recursing into subset
# directories via mk/subdir.mk.

TOP = .
include $(TOP)/mk/boilerplate.mk

SUBDIRS = imaginary spectral

include $(TOP)/mk/subdir.mk
