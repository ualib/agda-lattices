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
# Site targets (the documentation site; see mkdocs.yml):
#   make site-full           agda --html twice, then the site in ./site: what
#                            CI builds and deploys.
#   make site                The site alone, with plain code blocks unless
#                            `make agda-md` has run.
#   make serve               A live preview at http://127.0.0.1:8000.
#   make site-check          The gates on a built site: the links here, no
#                            request to another origin, the reference links.
#   make sibling-links       Every link to the sibling site against its live
#                            pages (needs the network).
#   make theme-check         The theme's files against agda-algebras at
#                            THEME_REV (needs the network).
#   make site-test           The site tools' own tests.
#
# Variables:
#   AGDA           the agda to run        (default: the one on PATH)
#   AGDA_OPTS      extra agda flags
# =============================================================================

.PHONY: help default check test safety safety-test profile clean EverythingLattices.agda \
        agda-md html site site-full serve gen-links check-links site-links sibling-links \
        offline-check site-check theme-check theme-sync site-test \
        contrast-audit font-audit offline-audit design-audit

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

clean: ## Remove this library's interface files, the aggregator and the built site
	@echo "target: $@"
	rm -rf _build
	find $(SRCDIR) -name '*.agdai' -delete
	rm -f $(SRCDIR)/EverythingLattices.agda
	rm -rf $(SITE_DIR) $(AGDA_HTML)

# -- The documentation site --------------------------------------------------
# The pipeline of the Agda Universal Algebra Library's site, adapted (NOTICE).
# MkDocs reads the `.lagda.md` sources through
# scripts/python/mkdocs_gen_library.py.  Everything the build writes is
# gitignored and outside src/, apart from the aggregator.
#
#   agda-md     agda --html --html-highlight=code -> .agda-html/md: the
#               highlighted, hyperlinked code blocks the pages embed.
#   html        agda --html -> .agda-html/classic: Agda's own pages, of which
#               the standard library's are published at /classic/.
#   site        MkDocs under --strict -> ./site.
#   site-full   html, agda-md and site: the published site.
#
# Each agda --html run clears its directory first, so that a module no
# longer in the build leaves no page behind.  The Nix shell sets
# SOURCE_DATE_EPOCH to 1980-01-01, which MkDocs would stamp into every
# sitemap <lastmod>, so the site build unsets it.
MKDOCS    ?= mkdocs
AGDA_HTML := .agda-html
SITE_DIR  ?= site
PYTHON    ?= python3

agda-md: EverythingLattices.agda ## Highlighted code blocks for the pages (agda --html)
	@echo "target: $@"
	rm -rf $(AGDA_HTML)/md
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-highlight=code --html-dir=$(AGDA_HTML)/md $(SRCDIR)/EverythingLattices.agda

html: EverythingLattices.agda ## Agda's own pages, the standard library's published at /classic/
	@echo "target: $@"
	rm -rf $(AGDA_HTML)/classic
	$(AGDA) $(RTS_OPTS) $(AGDA_OPTS) --html --html-dir=$(AGDA_HTML)/classic $(SRCDIR)/EverythingLattices.agda

site: ## Build the site under --strict (plain code blocks unless agda-md has run)
	@echo "target: $@"
	@test -d $(AGDA_HTML)/md || echo "  note: code blocks will be PLAIN; run 'make site-full' for Agda's highlighting."
	env -u SOURCE_DATE_EPOCH $(MKDOCS) build --strict --clean --site-dir $(SITE_DIR)

site-full: ## Build the published site: html, agda-md, then site
	@echo "target: $@"
	$(MAKE) html
	$(MAKE) agda-md
	$(MAKE) site

serve: ## Preview the site at http://127.0.0.1:8000
	@echo "target: $@"
	$(MKDOCS) serve

gen-links: ## Regenerate docs/_links.md's module sections
	@echo "target: $@"
	$(PYTHON) scripts/python/gen_links.py

# Reference-style links that have no definition render as literal text and
# pass --strict, so these two read the sources: docs/_links.md is what the
# trees imply, and every reference the prose uses resolves.
check-links: ## The reference-style links: _links.md in sync, every reference defined
	@echo "target: $@"
	$(PYTHON) scripts/python/gen_links.py --check
	$(PYTHON) scripts/python/check_links.py

site-links: ## Every link and asset of the built site names a file and an id that exist
	@echo "target: $@"
	$(PYTHON) scripts/python/check_site_links.py $(SITE_DIR)

sibling-links: ## Every link to the sibling site, checked against its live pages
	@echo "target: $@"
	$(PYTHON) scripts/python/check_site_links.py --sibling $(SITE_DIR)

offline-check: ## No built page or stylesheet requests anything from another origin
	@echo "target: $@"
	$(PYTHON) scripts/python/theme/check_offline.py $(SITE_DIR)

site-check: site-links offline-check check-links ## The offline gates on a built site

# The theme's files are copies of the Agda Universal Algebra Library's, at
# THEME_REV: the head of that library's pull request 622, which made the
# theme shareable, until it merges; then its merge commit.  To move it, set
# THEME_REV and run `make theme-sync`, then `make theme-check`.
THEME_REV ?= 46f8b13a0e9bb8eefba93fbd926f157e0bd9f49d
THEME_SRC  = $(shell nix flake prefetch --json github:ualib/agda-algebras/$(THEME_REV) | $(PYTHON) -c 'import json,sys; print(json.load(sys.stdin)["storePath"])')

theme-check: ## The theme's files against agda-algebras at THEME_REV
	@echo "target: $@"
	@test -n "$(THEME_SRC)" || { echo "  error: could not fetch agda-algebras at $(THEME_REV)"; exit 2; }
	$(PYTHON) scripts/python/theme/check_theme.py $(THEME_SRC)

theme-sync: ## Copy the theme's files from agda-algebras at THEME_REV
	@echo "target: $@"
	@test -n "$(THEME_SRC)" || { echo "  error: could not fetch agda-algebras at $(THEME_REV)"; exit 2; }
	$(PYTHON) scripts/python/theme/check_theme.py --sync $(THEME_SRC)

site-test: ## The site tools' own tests
	@echo "target: $@"
	$(PYTHON) scripts/python/test_check_links.py
	$(PYTHON) scripts/python/test_site_pipeline.py
	$(PYTHON) scripts/python/theme/test_check_offline.py

# The three audits of the copied theme load the built site in a real browser
# (node 22 and a Chromium; set CHROME=/path/to/chrome if none is found), so
# they are local targets, run before a pull request that touches the theme.
# AUDIT_PAGES restricts a run to pages whose path starts with one of its
# words, for example `make contrast-audit AUDIT_PAGES="index.html Lattices/Free"`.
#   contrast-audit      WCAG contrast of every text element, both schemes
#   font-audit          the face Chromium rasterized every character with
#   offline-audit       every request every page makes
AUDIT_PAGES ?=
NODE        ?= node
AUDIT_SCRIPT_contrast-audit := audit_contrast.mjs
AUDIT_SCRIPT_font-audit     := audit_fonts.mjs
AUDIT_SCRIPT_offline-audit  := audit_offline.mjs

contrast-audit font-audit offline-audit: ## A browser audit of the built site (see the Makefile)
	@echo "target: $@"
	@command -v $(NODE) >/dev/null || { echo "  error: node 22 or later is required for $@"; exit 2; }
	@test -f $(SITE_DIR)/index.html || { echo "  error: $(SITE_DIR)/index.html missing; run 'make site-full' first."; exit 2; }
	$(NODE) scripts/js/$(AUDIT_SCRIPT_$@) $(SITE_DIR) $(AUDIT_PAGES)

design-audit: contrast-audit font-audit offline-audit ## All three browser audits
