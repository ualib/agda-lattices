<!-- File: README.md -->

# agda-lattices

Lattice theory in [Agda][], on top of the [Agda Universal Algebra
Library][agda-algebras].  The library covers free lattices (lattice terms,
Whitman's solution of the word problem, the free lattice and its universal
property, canonical forms, Whitman's condition and semidistributivity,
substitutions, free generating sets, embeddings and complexity, Whitman's
countable family, and the polynomial-time decision of the order), free
generation and breadth in lattices satisfying Whitman's condition, Nation's
theorem and its proof for finite lattices, bounded homomorphisms, projective
lattices and Kostinsky's theorem, quotients, intervals, modular and
distributive lattices, central elements and direct decompositions, finite
products, lattices given by their operation tables, and worked examples.
Every module is checked by Agda under `--without-K --exact-split --safe`.

The library's [documentation site][site] renders every module with Agda's
highlighting, every name a link to its definition, on that site or on the
[site of the Agda Universal Algebra Library][algebras-site].

The reference throughout is R. Freese, J. Ježek and J. B. Nation, *Free
Lattices*, Mathematical Surveys and Monographs 42, American Mathematical
Society, 1995 (FJN below), cited by theorem number.

## Checking it

The toolchain is a [Nix][] flake, so a machine with Nix 2.28 or later, with
flakes enabled, needs nothing else:

    git clone https://github.com/ualib/agda-lattices.git
    cd agda-lattices
    nix develop --command make check

`make check` first runs `scripts/check-safety.sh` (below), then generates
`src/EverythingLattices.agda`, which imports every module under `src/`, and
type-checks it with a heap limit of 6 GiB (`+RTS -M6G -A128M`).  It exits 0
when every module checks.  There is no separate test step: type-checking is
the test.

The Agda is a pre-release of Agda 2.9.0, which Nix builds from source in about
an hour unless it can fetch it from the public binary cache
`formalverification` on [Cachix][], where the Agda Universal Algebra Library's
CI puts it.  To fetch it, run `cachix use formalverification` once, or add the
following lines to your Nix configuration (`/etc/nix/nix.conf`, or the
`nix.conf` in your user's Nix configuration directory if you are a trusted
user):

    extra-substituters = https://formalverification.cachix.org
    extra-trusted-public-keys = formalverification.cachix.org-1:KG/AJuuli2F4/bA56rUYC9V8ZE/Zw6iZjxJEf40cQOo=

The first `make check` also checks the modules of the Agda Universal Algebra
Library that this library imports, and keeps their interface files under
`.deps/`, so later runs check this library alone.

### The toolchain

`flake.lock` pins every input, as follows:

+  the [Agda Universal Algebra Library][agda-algebras] at commit
   [`b4d0ab6c`][algebras-pin] of its master branch, pinned in `flake.nix`
   itself as well;
+  Agda 2.9.0, a pre-release built from [agda/agda][] at commit
   [`da66a8c7`][agda-pin], and the [Agda standard library][agda-stdlib] 2.3
   patched to check under it, both taken from that library's flake, so the
   one pin moves the library, the compiler and the standard library together;
+  nixpkgs, which follows that library's own pin.

`nix develop` writes a project-local Agda configuration (`.agda/`) and an
`agda` wrapper that names the standard library, the Agda Universal Algebra
Library and this library explicitly, so nothing in your own Agda
configuration takes part.

### The site

`nix develop --command make site-full` builds the documentation site into
`site/` (`make serve` previews it), by the pipeline of the Agda Universal
Algebra Library's site and in its theme; `mkdocs.yml` and the Makefile say
how, and `NOTICE` what is taken from that library.

## What is checked

+  Every module carries the pragma
   `{-# OPTIONS --without-K --exact-split --safe #-}`.  Under `--safe` Agda
   refuses postulates, unsafe primitives and non-terminating definitions, so
   every theorem is proved from the type theory alone.
   `scripts/check-safety.sh` (`make safety`, the first step of `make check`)
   checks without running Agda that every module carries that pragma and no
   other, and that its code holds no `postulate` and no pragma that switches a
   check off.  A worked example may add `--lossy-unification`, which `--safe`
   accepts: the option is sound but not complete (Agda's user manual, "Lossy
   Unification"), and it lets Agda compare two applications of a function by
   their arguments, which an example applying general theorems to a concrete
   lattice can need; `Examples.Central` uses it, and says why.  No other
   module does.
+  A statement proved by induction is checked when its proof term has the
   stated type.  A statement about explicit terms or finite lattices is
   checked by computation: Whitman's procedure is a decision `s ≤ʷ? t`, the
   properties of a lattice given by its tables are decided, and Agda evaluates
   the decision while it checks the module; `from-yes` or `from-no` turns the
   answer into a proof.

## The modules

Every module is under `src/Lattices/`; names below drop the common prefix
`Lattices.`.

+  **Free lattices**.  `Free` is the barrel of the free-lattice modules:
   `Free.Term` (lattice terms), `Free.Whitman` (Whitman's rules and their
   decision), `Free.Universal` (the free lattice `FL(X)`, soundness and
   completeness of the rules, FJN Theorems 1.8 and 1.11, and the universal
   property), `Free.Derivability` (equational logic), `Free.Duality`,
   `Free.Canonical` with `Free.Canonical.Basic`, `.Algorithm`, `.Uniqueness`,
   `.Joinands`, `.Recognition`, `.Minimality` and `.JoinIrreducible`
   (canonical forms, FJN Theorems 1.17 to 1.20), `Free.Semidistributive`
   (FJN Theorems 1.8 and 1.21 for `FL(X)`), `Free.Substitution`
   (substitutions and the homomorphisms they induce), `Free.Generation`
   (free generating sets, FJN Corollaries 1.6 and 1.13, decided),
   `Free.Embedding` (FJN Lemma 9.13 and its dual), `Free.Complexity` (the
   complexity of an element, never lowered by an embedding),
   `Free.WhitmanPolynomials`, `Free.FixedPointFree`, `Free.WhitmanChains` and
   `Free.Countable` (Whitman's countable family, FJN Theorems 1.23 to 1.29),
   `Free.Whitman.Polynomial` (the order decided in polynomial time, FJN
   Chapter XI, Section 8) and `Free.Bounded` (homomorphisms into a free
   lattice are bounded, Kostinsky's Lemma 3.1).
+  **Any lattice**.  `Semidistributive` and `Semidistributive.FiniteJoins`
   (the semidistributive laws and Whitman's condition, FJN Theorem 1.21),
   `Generation` (free generation in a lattice satisfying Whitman's condition,
   FJN Corollary 1.12), `Breadth` (Jónsson and Kiefer's theorem, FJN Theorem
   1.30, Corollary 1.31 and the 4-distributive law), `Quotient`, `Interval`,
   `Dual` (the dual lattice), `FilterIdeal` (principal filters and ideals,
   and their union), `OrdinalSum` (the glued ordinal sum), `Product` (binary
   and finite products), `Modular` with `Modular.Dedekind` and
   `Modular.Birkhoff` (the modular and distributive laws, and the `N₅` and
   `M₃` criteria), `Distributive` with `Distributive.Theory`,
   `Distributive.Bundle` and `Distributive.Small` (distributive lattices as a
   structure, its equational theory, its bridge to the standard library's
   bundle, and the structure at the lowest universe level), and `Central`
   with `Central.Decomposition` (neutral and central elements, and direct
   decompositions by central elements).
+  **Bounded lattices and Kostinsky's theorem**.  `Bounded.Homomorphism`
   (bounded homomorphisms), `Bounded.Covers` (join covers and the sets
   `D_k(L)`), `Bounded.Preimage` (FJN Theorem 2.6 and Lemma 2.7),
   `Bounded.Sublattice` (FJN Corollaries 2.15 and 2.16), `Bounded.Finite`
   (the D relation and lower boundedness of a finite lattice, FJN
   Corollary 2.39), `Projective` (projective lattices, FJN Theorem 5.1),
   `Kostinsky` (Kostinsky's theorem: for a finitely generated lattice,
   projective, sublattice of a free lattice, and bounded with Whitman's
   condition are equivalent) and `Kostinsky.Finite` (its finite case on table
   lattices).
+  **Nation's theorem**.  `Nation` states FJN Theorem 5.55 (a finite lattice
   is a sublattice of a free lattice if and only if it is semidistributive
   and satisfies Whitman's condition) as a hypothesis, with its easy
   direction proved; `Nation.Order`, `Nation.Kappa`, `Nation.Cycle`,
   `Nation.Bounded`, `Nation.Configurations`, `Nation.BType`,
   `Nation.Lemma542`, `Nation.Subsequences`, `Nation.Lemma547`,
   `Nation.Lemma548`, `Nation.Extension`, `Nation.Lemma551`,
   `Nation.Alternating`, `Nation.NoCycle` and `Nation.Lemma554` follow
   Nation's argument of FJN Section V.3 on table lattices, to its conclusion
   that a finite lattice with both semidistributive laws and Whitman's
   condition has no C-cycle and is bounded.
+  **Table lattices**.  `Table` builds a finite lattice on `Fin n` from its
   operation tables.
+  **Worked examples**, under `Examples`: `FreeLattice3`, `CountableFree`,
   `WhitmanTable` (FJN Example 11.32), `M3`, `N5`, `Mn`, `Partitions` (the
   partition lattices of three and four elements), `TwoByThree`,
   `SublatticesOfFree` (which five-element lattices are sublattices of a free
   lattice), `Central`, `L2Distributive` (the two-element lattice as a
   distributive lattice) and `L3Heyting` (the three-element chain as a
   Heyting algebra).

A module whose own check takes three seconds or more says so in its front
matter (`check-cost: heavy`) and states its cost in its prose; no barrel
imports it, and `make check` still checks it.

## Provenance

The library's first modules, on lattice terms, Whitman's solution of the word
problem, the free lattice, canonical forms, semidistributivity, substitutions,
free generating sets, embeddings and table lattices, were first written in the
[Agda Universal Algebra Library][agda-algebras], and moved out of it in October
2026; so were the dual lattice, filters and ideals, ordinal sums, binary
products, and distributive lattices with their two examples, written there
between May and August 2026.  The others were written since.

## License and citation

The library is licensed under the Apache License 2.0 (`LICENSE`); `NOTICE`
records the attribution it carries from the Agda Universal Algebra Library.
`CITATION.cff` gives the metadata for citing it.

## Acknowledgment

The formal development in this repository was produced with the assistance of
large language models, chiefly Claude (Anthropic), used as tools under the
author's direction; the author takes full responsibility for every definition,
statement and proof.

[Agda]: https://wiki.portal.chalmers.se/agda/
[agda-algebras]: https://github.com/ualib/agda-algebras
[algebras-site]: https://agda-algebras.universalalgebra.org/
[algebras-pin]: https://github.com/ualib/agda-algebras/tree/b4d0ab6cd9a6e32f28857bd5014bbacaa284bb35
[agda/agda]: https://github.com/agda/agda
[agda-pin]: https://github.com/agda/agda/tree/da66a8c75f11d10699a6b38b261efdf244b66f2a
[agda-stdlib]: https://github.com/agda/agda-stdlib
[Cachix]: https://www.cachix.org/
[Nix]: https://nixos.org/
[site]: https://ualib.github.io/agda-lattices/
