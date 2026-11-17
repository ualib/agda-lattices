---
layout: default
file: "src/Lattices/Modular/Ladder.lagda.md"
title: "Lattices.Modular.Ladder module"
date: "2026-11-17"
author: "the agda-algebras development team"
---

### The ladder stops in a modular lattice

This is the [Lattices.Modular.Ladder][] module of the [agda-lattices][] library.

Fix elements `a`, `b` and `w` of a lattice.  The *ladder* over them is the pair
of sequences

    A₀ = w ∧ a,   Aₖ₊₁ = w ∧ (a ∨ Bₖ),
    B₀ = w ∧ b,   Bₖ₊₁ = w ∧ (b ∨ Aₖ).

In a modular lattice the ladder stops at the first rung: every `Aₖ` and every
`Bₖ` with `k ≥ 1` is `(w ∧ a) ∨ (w ∧ b)`.  A distributive lattice is modular,
so the same holds there, and the distributive law rewrites the common value as
`w ∧ (a ∨ b)`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Modular.Ladder where

-- Imports from the Agda Standard Library -------------------------------------
open import Data.Nat         using ( ℕ ; zero ; suc )
open import Data.Product     using ( _×_ ; proj₁ ; _,_)
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

-- Imports from this library --------------------------------------------------
open import Lattices.Modular  using ( IsModular ; IsDistributive )
```
-->

#### The ladder and the theorem

```agda
module _ {α ρ : Level} (𝓛@(𝑳 , 𝑳⊨Th-Lattice ) : Lattice α ρ) (a b w : 𝕌[ 𝑳 ]) where
  open Lattice-Op 𝓛    using ( _∧_ ; _∨_ )
  open Setoid 𝔻[ 𝑳 ]   using ( _≈_ )

  -- The rungs of the ladder over a, b and w.
  A B : ℕ → 𝕌[ 𝑳 ]
  A zero    = w ∧ a
  A (suc k) = w ∧ (a ∨ B k)
  B zero    = w ∧ b
  B (suc k) = w ∧ (b ∨ A k)

  -- In a modular lattice the ladder stops at the first rung.
  ladder-stops : IsModular 𝓛
    → ∀ k → A (suc k) ≈ (w ∧ a) ∨ (w ∧ b)  ×  B (suc k) ≈ (w ∧ a) ∨ (w ∧ b)
  ladder-stops = {!!}

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive = {!!}
```
