---
layout: default
file: "src/Lattices/Nation/Lemma554.lagda.md"
title: "Lattices.Nation.Lemma554 module"
date: "2026-10-22"
author: "the agda-algebras development team"
check-cost: heavy
---

### Lemma 5.54 for a table lattice, and boundedness

This is the [Lattices.Nation.Lemma554][] module of the [agda-lattices][]
library.

[Lattices.Nation.NoCycle][] proves Lemma 5.54 of [Freese, Ježek, and Nation
(1995)][] from one fact about B's: the first step of a cycle, if a B, lies
between two A's (the parameter of its module `Final`{.AgdaModule}).  This
module supplies it from the dual lattice, the lattice of the swapped tables.
Through κ, a cycle of the lattice is a cycle of the dual whose B's are A's
(Lemma 2.63 and `dual-cycle`{.AgdaFunction} of [Lattices.Nation.Cycle][]), and
the dual development's fact about A's (`factA0`{.AgdaFunction} at the dual
tables) puts the A between two B's of the dual, which are A's of the cycle.
The dual development is reached by qualified references, never by a module
application, which would copy all of it into this module.  The conclusions:
an S-lattice contains no C-cycle (`lemma-5-54`{.AgdaFunction}), and, by
Corollary 2.65 of [Lattices.Nation.Bounded][], it is bounded
(`bounded`{.AgdaFunction}).

The module checks in 19.4 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).  Its cost puts it under
the barrel policy: the front matter carries `check-cost: heavy`, and no barrel
imports it.  The time is the conversion of the dual fact's statement between
the copies of κ and the relations that [Lattices.Nation.Kappa][] and
[Lattices.Nation.NoCycle][] each open.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Lemma554 where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; suc ; z≤n )
                                                   renaming ( _≤_ to _≤ℕ_ )
open import Data.Nat.Properties                    using ( ≰⇒> ) renaming ( _≤?_ to _≤ℕ?_ )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Finite         using ( dual-laws ; Bounded )
open import Lattices.Nation.Bounded         using ( module BoundedDuality )
open import Lattices.Nation.Cycle           using ( module Cycles ; module CycleMap ; module CycleDuality
                                                  ; vertex ; vertex-end )
open import Lattices.Nation.Kappa           using ( module Kappa ; module KappaDuality )
open import Lattices.Nation.NoCycle         using ( module NoCycle )
open import Lattices.Nation.Order           using ( module Order )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```
-->

```agda
module Lemma554 {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Cycles laws sd w using ( MinimalCycle ; module MinimalCycleProperties ; Cycle )

  -- The dual tables' (W).
  wᵈ : SatisfiesW (tableLattice _∨_ _∧_ (dual-laws laws))
  wᵈ = Order.W-dual laws w

  -- Every member of a cycle is join irreducible, also past the length, where the base returns.
  at-irr′ : (𝒞 : MinimalCycle) → ∀ i → Kappa.HasOneLowerCover laws sd (MinimalCycleProperties.at 𝒞 i)
  at-irr′ 𝒞 i = from (i ≤ℕ? MinimalCycle.k 𝒞)
    where
    open MinimalCycleProperties 𝒞 using ( at ; at-irr )

    from : Dec (i ≤ℕ MinimalCycle.k 𝒞) → Kappa.HasOneLowerCover laws sd (at i)
    from (yes i≤k) = at-irr i i≤k
    from (no i≰k)  = subst (Kappa.HasOneLowerCover laws sd) (sym (vertex-end (MinimalCycle.path 𝒞) i (≰⇒> i≰k)))
                           (at-irr 0 z≤n)

  -- The fact about B's: the first step of a cycle, if a B, lies between two A's.  In the dual cycle the B is an
  -- A, which the dual development's fact about A's puts between two B's of the dual, A's of the cycle.
  factB0 : (𝒞₁ : MinimalCycle) → NoCycle.Steps.IsB laws sd w 𝒞₁ 0
         → NoCycle.Steps.IsA laws sd w 𝒞₁ 1 × NoCycle.Steps.IsA laws sd w 𝒞₁ (NoCycle.Steps.kc laws sd w 𝒞₁)
  factB0 𝒞₁ B0 = back 1 (proj₁ (proj₂ fa)) , back kcᵈ (proj₂ (proj₂ fa))
    where
    𝒞ᵈ : Cycles.MinimalCycle (dual-laws laws) (swap sd) wᵈ
    𝒞ᵈ = CycleDuality.dual-cycle laws sd w 𝒞₁

    at₁ : ℕ → Fin (suc n)
    at₁ = MinimalCycleProperties.at 𝒞₁

    kcᵈ : ℕ
    kcᵈ = NoCycle.Steps.kc (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ

    vm : ∀ i → vertex (CycleMap.map-κ laws sd (MinimalCycle.path 𝒞₁)) i ≡ Kappa.κ laws sd (at₁ i)
    vm i = CycleMap.vertex-map-κ laws sd (MinimalCycle.path 𝒞₁) i

    A0ᵈ : NoCycle.Steps.IsA (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ 0
    A0ᵈ = NoCycle.→IsA (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ 0 (vm 0) (vm 1) (KappaDuality.B→Aᵈ laws sd B0)

    fa : NoCycle.Steps.IsA₂ (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ 0 × NoCycle.Steps.IsB (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ 1
       × NoCycle.Steps.IsB (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ kcᵈ
    fa = NoCycle.factA0 (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ A0ᵈ

    back : ∀ i → NoCycle.Steps.IsB (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ i → NoCycle.Steps.IsA laws sd w 𝒞₁ i
    back i h = KappaDuality.Bᵈ→A laws sd (at-irr′ 𝒞₁ i) (at-irr′ 𝒞₁ (suc i))
                                 (NoCycle.IsB→ (dual-laws laws) (swap sd) wᵈ 𝒞ᵈ i (vm i) (vm (suc i)) h)

  -- Lemma 5.54: an S-lattice contains no C-cycle.
  lemma-5-54 : ∀ {k} → ¬ Cycle k
  lemma-5-54 = NoCycle.Final.lemma-5-54 laws sd w factB0

  -- An S-lattice is bounded: Corollary 2.65 with Lemma 5.54.
  bounded : Bounded laws
  bounded = BoundedDuality.noCCycle→bounded laws sd lemma-5-54
```
