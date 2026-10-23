---
layout: default
file: "src/Lattices/Nation/Order.lagda.md"
title: "Lattices.Nation.Order module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Order lemmas for the finite lattice of a pair of tables, and its dual

This is the [Lattices.Nation.Order][] module of the [agda-lattices][] library.

The modules of Nation's theorem reason about one table lattice of
[Lattices.Table][] through the order of [Lattices.Bounded.Finite][], and about
its dual, the lattice of the tables swapped.  This module collects the small
order lemmas they use at every turn and that neither agda-algebras'
`Lattice-Order`{.AgdaModule} nor `JoinDependency`{.AgdaModule} states:
monotonicity of the operations, absorption of a comparable operand, the order
of the dual tables as the converse order (`≤ᵈ→`{.AgdaFunction},
`→≤ᵈ`{.AgdaFunction}), and Whitman's condition for the dual tables
(`W-dual`{.AgdaFunction}), which is (W) with its disjuncts swapped.  Every
module of the development opens it, [Lattices.Nation.Kappa][] publicly.

The module checks in 0.1 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Order where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( _×_ ; _,_ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ ; [_,_]′ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( module Lattice-Op )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Finite    using ( module JoinDependency ; dual-laws )
open import Lattices.Semidistributive  using ( SatisfiesW )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

```agda
module Order {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
             (laws : LatticeTableLaws _∧_ _∨_) where

  open JoinDependency laws
  open Lattice-Order (tableLattice _∧_ _∨_ laws) public using ( ≤-via-∨ ; ≤-from-∨ )
  open Lattice-Op (tableLattice _∧_ _∨_ laws) public using ( ∧-comm-law ; ∨-comm-law )

  -- Monotonicity of join and meet.
  ∨-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a ∨ c ≤ b ∨ d
  ∨-mono a≤b c≤d = ∨-least (≤-trans a≤b ∨-upperˡ) (≤-trans c≤d ∨-upperʳ)

  ∧-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a ∧ c ≤ b ∧ d
  ∧-mono a≤b c≤d = ∧-greatest (≤-trans ∧-lowerˡ a≤b) (≤-trans ∧-lowerʳ c≤d)

  ∨-monoˡ : ∀ {a b c} → a ≤ b → a ∨ c ≤ b ∨ c
  ∨-monoˡ a≤b = ∨-mono a≤b ≤-refl

  ∨-monoʳ : ∀ {a b c} → b ≤ c → a ∨ b ≤ a ∨ c
  ∨-monoʳ b≤c = ∨-mono ≤-refl b≤c

  ∧-monoˡ : ∀ {a b c} → a ≤ b → a ∧ c ≤ b ∧ c
  ∧-monoˡ a≤b = ∧-mono a≤b ≤-refl

  ∧-monoʳ : ∀ {a b c} → b ≤ c → a ∧ b ≤ a ∧ c
  ∧-monoʳ b≤c = ∧-mono ≤-refl b≤c

  -- A joinand below the other is absorbed, and a meetand above the other.
  ∨-absorbˡ : ∀ {a b} → a ≤ b → a ∨ b ≡ b
  ∨-absorbˡ = ≤-via-∨

  ∨-absorbʳ : ∀ {a b} → b ≤ a → a ∨ b ≡ a
  ∨-absorbʳ b≤a = trans ∨-comm-law (≤-via-∨ b≤a)

  ∧-absorbʳ : ∀ {a b} → a ≤ b → a ∧ b ≡ a
  ∧-absorbʳ a≤b = a≤b

  ∧-absorbˡ : ∀ {a b} → b ≤ a → a ∧ b ≡ b
  ∧-absorbˡ b≤a = trans ∧-comm-law b≤a

  -- Below a join through one joinand; above a meet through one meetand.
  ≤∨ˡ : ∀ {a b c} → a ≤ b → a ≤ b ∨ c
  ≤∨ˡ a≤b = ≤-trans a≤b ∨-upperˡ

  ≤∨ʳ : ∀ {a b c} → a ≤ c → a ≤ b ∨ c
  ≤∨ʳ a≤c = ≤-trans a≤c ∨-upperʳ

  ∧ˡ≤ : ∀ {a b c} → a ≤ c → a ∧ b ≤ c
  ∧ˡ≤ a≤c = ≤-trans ∧-lowerˡ a≤c

  ∧ʳ≤ : ∀ {a b c} → b ≤ c → a ∧ b ≤ c
  ∧ʳ≤ b≤c = ≤-trans ∧-lowerʳ b≤c

  -- An element below a join irreducible element and not equal to it lies below its lower cover.
  <→≤₋′ : ∀ {b c} → c ≤ b → c ≢ b → c ≤ b ₋
  <→≤₋′ c≤b c≢b = <→≤₋ (c≤b , c≢b)

  ≤-reflexive′ : ∀ {x y} → x ≡ y → x ≤ y
  ≤-reflexive′ refl = ≤-refl

  -- The dual order, a ∨ b ≡ a, is the converse order.
  ≤ᵈ→ : ∀ {a b} → a ∨ b ≡ a → b ≤ a
  ≤ᵈ→ e = ≤-from-∨ (trans ∨-comm-law e)

  →≤ᵈ : ∀ {a b} → b ≤ a → a ∨ b ≡ a
  →≤ᵈ e = trans ∨-comm-law (≤-via-∨ e)

  <ᵈ→ : ∀ {a b} → (a ∨ b ≡ a) × a ≢ b → b < a
  <ᵈ→ (a≤ᵈb , a≢b) = ≤ᵈ→ a≤ᵈb , λ b≡a → a≢b (sym b≡a)

  →<ᵈ : ∀ {a b} → b < a → (a ∨ b ≡ a) × a ≢ b
  →<ᵈ (b≤a , b≢a) = →≤ᵈ b≤a , λ a≡b → b≢a (sym a≡b)

  -- (W) is self-dual: the dual tables satisfy it with the disjuncts swapped.
  W-dual : SatisfiesW (tableLattice _∧_ _∨_ laws) → SatisfiesW (tableLattice _∨_ _∧_ (dual-laws laws))
  W-dual w s₁ s₂ t₁ t₂ h =
    [ (λ { (inj₁ x) → inj₂ (inj₁ (→≤ᵈ x)) ; (inj₂ y) → inj₂ (inj₂ (→≤ᵈ y)) })
    , (λ { (inj₁ x) → inj₁ (inj₁ (→≤ᵈ x)) ; (inj₂ y) → inj₁ (inj₂ (→≤ᵈ y)) }) ]′
    (w t₁ t₂ s₁ s₂ (≤ᵈ→ h))
```
