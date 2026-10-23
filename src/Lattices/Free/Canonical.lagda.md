---
layout: default
file: "src/Lattices/Free/Canonical.lagda.md"
title: "Lattices.Free.Canonical module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Canonical forms in free lattices

This is the [Lattices.Free.Canonical][] module of the [agda-lattices][] library.

Whitman's procedure decides whether two lattice terms name the same element of the
free lattice `FL(X)`; it does not choose a name.  Every element of a free lattice
has a term of minimal rank representing it, unique up to commutativity, its
*canonical form* ([Freese, Ježek, and Nation (1995)][], Theorem 1.17), and Theorem
1.18 characterizes that form by four syntactic conditions.  This is a barrel
module: it declares nothing of its own and re-exports the five modules that
formalize canonical forms.

### Guide to the submodules of <span class="AgdaModule">Lattices.Free.Canonical</span>

+  [Lattices.Free.Canonical.Basic][]: the canonical terms
   `CTerm X`{.AgdaDatatype}, with joins and meets of lists of children, their
   embedding `⌊_⌋`{.AgdaFunction} into lattice terms, their rank, the predicate
   `IsCanonical`{.AgdaDatatype} stating the four conditions of Theorem 1.18, and
   the duality that exchanges joins and meets;
+  [Lattices.Free.Canonical.Algorithm][]: the function
   `canonical`{.AgdaFunction} that computes the canonical form of a lattice term,
   a well-founded recursion on rank, with the theorems that the result represents
   the term and is canonical;
+  [Lattices.Free.Canonical.Uniqueness][]: equality up to
   commutativity `_≈ᶜ_`{.AgdaDatatype}, Lemma 1.16, Theorem 1.17 (two canonical
   terms representing the same element are related), and the decision of equality
   in the free lattice by comparison of canonical forms;
+  [Lattices.Free.Canonical.Joinands][]: the canonical joinands
   and meetands of an element, Theorem 1.19, their refinement of every join (and
   meet) representation, and Theorem 1.17 read through them: equal elements have
   the same canonical joinands up to order and equality.
+  [Lattices.Free.Canonical.Recognition][]: the decision of the four
   conditions of Theorem 1.18, which certifies a canonical form written out by
   hand or computed elsewhere;
+  [Lattices.Free.Canonical.Minimality][]: the flattened rank of a lattice
   term, its comparison with the binary rank, and the minimality half of
   Theorem 1.17: a canonical term has the least rank among all the terms
   representing its element;
+  [Lattices.Free.Canonical.JoinIrreducible][]: join irreducibility in the
   free lattice, its reading on canonical forms, and Theorem 1.20, the
   lattice-theoretic characterization of the canonical joinands, with the
   corners the book passes over made explicit.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical where

open import Lattices.Free.Canonical.Algorithm       public
open import Lattices.Free.Canonical.Basic           public
open import Lattices.Free.Canonical.Joinands        public
open import Lattices.Free.Canonical.JoinIrreducible public
open import Lattices.Free.Canonical.Minimality      public
open import Lattices.Free.Canonical.Recognition     public
open import Lattices.Free.Canonical.Uniqueness      public
```
