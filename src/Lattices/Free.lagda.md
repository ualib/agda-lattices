---
layout: default
file: "src/Lattices/Free.lagda.md"
title: "Lattices.Free module"
date: "2026-10-07"
author: "the agda-algebras development team"
---

### Free lattices

This is the [Lattices.Free][] module of the [agda-lattices][] library.

This is a barrel module: it declares nothing of its own and re-exports the modules
that construct the free lattice `FL(X)` and decide its order by Whitman's solution
to the word problem ([Freese, Ježek, and Nation (1995)][], Chapter I).  The
development is syntactic: `FL(X)` is the set of lattice terms ordered by the
relation Whitman's rules define, and the rules are proved sound and complete for
the order of every lattice, rather than read off a model built by Day's doubling
construction as in the book.

### Guide to the submodules of <span class="AgdaModule">Lattices.Free</span>

+  [Lattices.Free.Term][]: the lattice terms
   `LatTerm X`{.AgdaDatatype}, their rank, their evaluation in any lattice, and
   the translation to and from the generic `Term X`{.AgdaDatatype} over
   `Sig-Lattice`{.AgdaFunction};
+  [Lattices.Free.Whitman][]: Whitman's rules as the inductive
   relation `_≤ʷ_`{.AgdaDatatype}, its decision procedure, reflexivity,
   transitivity, and formal meet and join as infimum and supremum;
+  [Lattices.Free.Whitman.Polynomial][]: the same relation decided a second
   time, by a table of the pairs of subterms shaped by the terms, in time
   proportional to the product of the two ranks (Chapter XI, Section 8);
+  [Lattices.Free.Universal][]: the free lattice
   `FL X`{.AgdaFunction}, soundness and completeness of the rules (Whitman's
   theorem), and the universal property;
+  [Lattices.Free.Derivability][]: the bridge to equational
   logic, which makes derivable equality under `Th-Lattice`{.AgdaFunction}, and
   hence equality in the relatively free algebra `𝔽[ X ]`{.AgdaFunction},
   decidable;
+  [Lattices.Free.Duality][]: the involution of lattice terms
   that exchanges meet and join and reverses Whitman's order;
+  [Lattices.Free.Canonical][]: canonical forms (Theorems 1.17
   and 1.18), the algorithm that computes them, their uniqueness up to
   commutativity, and the canonical joinands of an element (Theorem 1.19);
+  [Lattices.Free.Semidistributive][]: free lattices satisfy
   Whitman's condition (Theorem 1.8) and are semidistributive (Theorem 1.21);
+  [Lattices.Free.Substitution][]: substitutions, the
   homomorphisms `FL(X) → FL(Y)` they induce, the evaluation lemma, and the
   theorem that every such homomorphism is induced by a substitution, and the
   generator inclusion of `FL(k)` in `FL(n)`;
+  [Lattices.Free.Generation][]: free generating sets
   (Corollaries 1.12 and 1.13, with Lemma 1.3), their decision procedure, and the
   irreducibility of free generators (Corollary 1.6);
+  [Lattices.Free.WhitmanPolynomials][]: the six polynomials preceding
   Theorem 1.23, the chains of Example 1.24, and the family of Theorem 1.28;
+  [Lattices.Free.FixedPointFree][]: Theorem 1.23, proved by descent on
   canonical rank, for all six polynomials;
+  [Lattices.Free.WhitmanChains][]: the strict chains, their index order,
   and Lemma 1.29;
+  [Lattices.Free.Countable][]: Theorem 1.28, the countable family freely
   generates, and the embeddings of countable and finite rank into rank
   three and of any finite rank into every finite rank at least three;
+  [Lattices.Free.Embedding][]: Lemma 9.13 (an embedding of
   free lattices sends a canonical joinand that is not a generator to a canonical
   joinand), its dual, its reading up to equality in the free lattice, and the
   canonical joinands and meetands of an image;
+  [Lattices.Free.Complexity][]: the complexity of an element (the depth of
   its canonical form), which a lattice embedding never lowers, and the
   finiteness of the elements of bounded complexity over finitely many
   generators.

Two worked examples go with these modules:
[Lattices.Examples.FreeLattice3][] decides a few inequalities in `FL(3)` by
evaluation and computes some canonical forms, and
[Lattices.Examples.CountableFree][] decides that the first members of Whitman's
countable family freely generate.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free where

open import Lattices.Free.Canonical         public
open import Lattices.Free.Complexity        public
open import Lattices.Free.Countable         public
open import Lattices.Free.Derivability      public
open import Lattices.Free.Duality           public
open import Lattices.Free.Embedding         public
open import Lattices.Free.FixedPointFree    public
  using ( p-fixed-point-free ; q-fixed-point-free )
open import Lattices.Free.Generation        public
open import Lattices.Free.Semidistributive  public
open import Lattices.Free.Substitution      public
open import Lattices.Free.Term              public
open import Lattices.Free.Universal         public
open import Lattices.Free.Whitman           public
open import Lattices.Free.Whitman.Polynomial public
  using ( Row ; module Decisionᵖ )
open import Lattices.Free.WhitmanChains      public
  using ( ascending-strict ; ascending-reflects ; joined-descending-reflects )
open import Lattices.Free.WhitmanPolynomials public
  using ( f₁ ; f₂ ; f₃ ; f₄ ; f₅ ; f₆ ; σ ; σ-finite )
```
