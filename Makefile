# Verify every F* module under src/.
#
# `fstar` is the wrapper the flake's dev shell provides (`nix develop`): it is
# `fstar.exe` with the F* library on the include path. Outside the dev shell,
# run `make FSTAR=fstar.exe`. Checked files are cached in $(CACHE_DIR); both
# the dependency scan and the checks are told so explicitly, so overriding
# CACHE_DIR gives a verification from an empty cache.
#
# Every module is an interface `M.fsti` and an implementation `M.fst`, and F*
# checks them one file per invocation: a single invocation may not name both
# files of a module that another file on its command line depends on. So
# `fstar --dep full` writes the dependency graph to $(DEPEND), and make runs
# the per-file checks in that order (in parallel under `make -j`). The F*
# library counts as already checked.

FSTAR       ?= fstar
FSTAR_FLAGS ?= --include src
CACHE_DIR   ?= .fstar-cache
CACHE_FLAGS := --cache_checked_modules --cache_dir $(CACHE_DIR)
DEPEND      := $(CACHE_DIR)/.depend
SRCS        := $(sort $(wildcard src/*.fsti src/*.fst))

.PHONY: all verify clean

all: verify

$(DEPEND): $(SRCS) Makefile
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) $(FSTAR_FLAGS) $(CACHE_FLAGS) --already_cached Prims,FStar --dep full $(SRCS) --output_deps_to $@

# The dependency graph is required: if it cannot be generated (for example
# when `fstar` is not on PATH), make fails instead of verifying nothing.
ifneq ($(strip $(MAKECMDGOALS)),clean)
include $(DEPEND)
endif

verify: $(ALL_CHECKED_FILES)
	@test -n "$(strip $(ALL_CHECKED_FILES))" || { echo "no modules to verify" >&2; exit 1; }

$(CACHE_DIR)/%.checked:
	$(FSTAR) $(FSTAR_FLAGS) $(CACHE_FLAGS) $<
	@touch -c $@

clean:
	rm -f $(CACHE_DIR)/*.checked $(DEPEND)
