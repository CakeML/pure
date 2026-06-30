# subdir.mk --- recurse a suite target into $(SUBDIRS).
#
# Included by the top-level and per-subset Makefiles. Each recursive target
# simply runs the same target in every subdirectory, forwarding mode/HEAP/PUREOPT.
# `all`/`build` abort on the first failure (a compile error is fatal); the
# run-and-check targets let each leaf report PASS/FAIL and keep going.

.PHONY: all build runtests check accept clean list

all build accept clean list:
	@for d in $(SUBDIRS); do \
	   $(MAKE) --no-print-directory -C $$d $@ \
	     mode='$(mode)' HEAP='$(HEAP)' PUREOPT='$(PUREOPT)' || exit $$?; \
	 done

# runtests/check never abort, so the whole suite is reported in one pass.
runtests check:
	@for d in $(SUBDIRS); do \
	   $(MAKE) --no-print-directory -C $$d $@ \
	     mode='$(mode)' HEAP='$(HEAP)' PUREOPT='$(PUREOPT)'; \
	 done
