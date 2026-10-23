---
layout: default
file: "src/Lattices/Examples/CountableFree.lagda.md"
title: "Lattices.Examples.CountableFree module"
date: "2026-10-17"
author: "William DeMeo"
check-cost: heavy
---

### Finite checks of Whitman's countable family

The first three members of the family in FJN Theorem 1.28 freely
generate, as the decision procedure for Corollary 1.13 independently
checks here.  These decisions check the transcription of the terms;
[Lattices.Free.Countable][] proves free generation for every finite
restriction and for the whole countable family.

**Cost**.  With Agda 2.9.0 and `+RTS -M6G -A128M`, isolated decisions
for sizes two and three took 79 ms and 3.32 s respectively (2026-10-17,
`--profile=definitions`).  The decision for size four exhausted the 6 GB
heap after 35.06 s, so it is omitted from the build.  No larger heap was
tried.  This module is marked heavy and is imported by no barrel.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.CountableFree where

open import Data.Fin.Properties using ( _≟_ )
open import Data.List.Base using ( allFin )
open import Data.List.Membership.Propositional.Properties using ( ∈-allFin )
open import Relation.Nullary.Decidable.Core using ( from-yes )

open import Lattices.Free.Generation using ( FreelyGenerates ; module Decide )
open import Lattices.Free.WhitmanPolynomials using ( σ-finite )

-- The empty restriction freely generates the empty free lattice.
zero-free : FreelyGenerates (σ-finite 0)
zero-free = from-yes (Decide.freelyGenerates? (_≟_ {0}) (allFin 0) ∈-allFin _≟_ (σ-finite 0))

-- The first member freely generates a one-element sublattice.
one-free : FreelyGenerates (σ-finite 1)
one-free = from-yes (Decide.freelyGenerates? (_≟_ {1}) (allFin 1) ∈-allFin _≟_ (σ-finite 1))

-- The first pair passes both conditions of Corollary 1.13.
two-free : FreelyGenerates (σ-finite 2)
two-free = from-yes (Decide.freelyGenerates? (_≟_ {2}) (allFin 2) ∈-allFin _≟_ (σ-finite 2))

-- The first triple passes the same independent decision.
three-free : FreelyGenerates (σ-finite 3)
three-free = from-yes (Decide.freelyGenerates? (_≟_ {3}) (allFin 3) ∈-allFin _≟_ (σ-finite 3))
```
