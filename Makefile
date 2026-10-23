# =============================================================================
# agda-lattices: Makefile
# =============================================================================
#
# Run from the repository root inside `nix develop`, so that `agda` is the
# wrapper that knows the pinned standard library and agda-algebras (see
# flake.nix).
#
# Agda targets:
#   make check               Check every module's pragma (make safety), then
#                            type-check the library: every module under src/.
#   make test                Alias for `make check`.
#   make safety              Every module carries the --safe pragma and no
#                            postulate or unsafe pragma (scripts/check-safety.sh).
#   make safety-test         The cases of that check (scripts/test-check-safety.sh).
#   make profile             Type-check with Agda profiling enabled.
#   make clean               Remove this library's interface files and the
#                            aggregator (the agda-algebras copy under .deps/
#                            and its interfaces are left alone).
#
# The aggregator, EverythingLattices.agda:
#   +  every module under src/, generated and gitignored, so that one run of
#      Agda checks the whole library;
#   +  a PHONY target, always regenerated, so that adding or removing a module
#      is picked up without anyone having to remember; `find` rather than
#      `git ls-tree`, so that untracked files in the working tree are included.
#
# Variables:
#   AGDA           the agda to run        (default: the one on PATH)
#   AGDA_OPTS      extra agda flags
# =============================================================================

.PHONY: help default check test safety safety-test profile clean EverythingLattices.agda

# -- Configuration -----------------------------------------------------------
SRCDIR    := src
AGDA      ?= agda
# A 6 GiB heap limit, above the peak of a whole-library check: the decision
# modules (Examples.CountableFree, the Nation lemmas) evaluate Whitman's
# procedure and finite searches while they are checked.
RTS_OPTS  := +RTS -M6G -A128M -RTS
AGDA_OPTS ?=

.DEFAULT_GOAL := help

help: ## Show this help
	@grep -hE '^[a-zA-Z][a-zA-Z0-9_-]*:.*## ' $(MAKEFILE_LIST) \
	  | awk 'BEGIN {FS = ":.*## "} {printf "  \033[1m%-14s\033[0m %s\n", $$1, $$2}'

# -- Agda --------------------------------------------------------------------

default: EverythingLattices.agda

# `--exact-split` is deliberately absent from the aggregator's pragma: it
# constrains definitions, and an aggregator contains nothing but imports.
# Each module carries `--exact-split` in its own header and is checked under
# it (make safety).
EverythingLattices.agda: ## Regenerate the aggregator from the current tree
	@echo "target: $@"
	@{ \
	  echo "{-# OPTIONS --without-K --safe #-}"; \
	  echo ""; \
	  echo "module EverythingLattices where"; \
	  echo ""; \
	  find $(SRCDIR) \
	      \( -name '*.lagda.md' -o -name '*.agda' \) \
	      ! -name 'EverythingLattices.agda' \
	    | sed -e 's|^$(SRCDIR)/||' \
	          -e 's|\.lagda\.md$$||' \
	          -e 's|\.agda$$||' \
	          -e 's|/|.|g' \
	          -e 's|^|import |' \
	    | LC_ALL=C sort; \
	} > $(SRCDIR)/EverythingLattices.agda
	@echo "  wrote $(SRCDIR)/EverythingLattices.agda ($$(grep -c '^import' $(SRCDIR)/EverythingLattices.agda) modules)"

safety: ## Check every module's pragma, and that no postulate or unsafe pragma appears
	@echo "target: $@"
	bash scripts/check-safety.sh $(SRCDIR)

safety-test: ## Run the cases of the safety check
	@echo "target: $@"
	bash scripts/test-check-safety.sh

check test: safety EverythingLattices.agda ## Check the pragmas, then type-check the library
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) $(SRCDIR)/EverythingLattices.agda

# Profile a whole-library type-check.  Agda accepts one profiling mode at a
# time, so override PROFILE to choose: internal (phases), modules (per-module
# ranking), definitions (per-definition attribution).  Measure from an empty
# build (`make clean`), or only stale modules are timed.
PROFILE ?= modules

profile: EverythingLattices.agda ## Type-check with Agda profiling (PROFILE=modules|internal|definitions)
	@echo "target: $@"
	$(AGDA) $(RTS_OPTS) --profile=$(PROFILE) $(SRCDIR)/EverythingLattices.agda

clean: ## Remove this library's interface files and the aggregator
	@echo "target: $@"
	rm -rf _build
	find $(SRCDIR) -name '*.agdai' -delete
	rm -f $(SRCDIR)/EverythingLattices.agda
