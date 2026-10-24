---
layout: default
file: "src/Lattices/Distributive/Small.lagda.md"
title: "Lattices.Distributive.Small module"
date: "2026-05-31"
author: "the agda-algebras development team"
---

### Level-fixed Distributive Lattice

This is the [Lattices.Distributive.Small][] module of the
[agda-lattices][] library.

Specializes [`Lattices.Distributive`][Lattices.Distributive] to the common case where
the universe level of both the carrier and the equivalence is `0ℓ` (i.e., Set-valued
carriers with propositional or set-truncated equivalence), mirroring the veneers of
`Lattice`, `CommutativeMonoid`, etc.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}
module Lattices.Distributive.Small where
open import Agda.Primitive                          using () renaming ( Set to Type )
open import Level                                   using ( 0ℓ ; suc )
open import Relation.Binary.PropositionalEquality   using ( _≡_ )
import Lattices.Distributive as Polymorphic
```
-->

```agda
DistributiveLattice : Type (suc 0ℓ)
DistributiveLattice = Polymorphic.DistributiveLattice 0ℓ 0ℓ

eqsToDistributiveLattice : (A : Type 0ℓ) (_∧'_ _∨'_ : A → A → A)
  → (∀ a b c → (a ∧' b) ∧' c ≡ a ∧' (b ∧' c))
  → (∀ a b → a ∧' b ≡ b ∧' a)
  → (∀ a → a ∧' a ≡ a)
  → (∀ a b c → (a ∨' b) ∨' c ≡ a ∨' (b ∨' c))
  → (∀ a b → a ∨' b ≡ b ∨' a)
  → (∀ a → a ∨' a ≡ a)
  → (∀ a b → a ∧' (a ∨' b) ≡ a)
  → (∀ a b → (a ∧' b) ∨' a ≡ a)
  → (∀ a b c → a ∧' (b ∨' c) ≡ (a ∧' b) ∨' (a ∧' c))
  → (∀ a b c → a ∨' (b ∧' c) ≡ (a ∨' b) ∧' (a ∨' c))
  → DistributiveLattice
eqsToDistributiveLattice = Polymorphic.eqsToDistributiveLattice
```
