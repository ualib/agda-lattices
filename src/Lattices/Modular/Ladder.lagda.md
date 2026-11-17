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
open import Data.Product     using ( _×_ ; proj₁ ; proj₂ ; _,_ )
open import Level            using ( Level )
open import Relation.Binary  using ( Setoid )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ----------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

-- Imports from this library --------------------------------------------------
open import Lattices.Modular  using ( IsModular ; IsDistributive ; IsDistributive→IsModular )
```
-->

#### The ladder and the theorem

```agda
module _ {α ρ : Level} (𝓛@(𝑳 , 𝑳⊨Th-Lattice ) : Lattice α ρ) (a b w : 𝕌[ 𝑳 ]) where
  open Lattice-Op 𝓛     using  ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                                ; ∨-assoc-law ; absorbʳ-law )
  open Lattice-Order 𝓛  using  ( ∧-lowerˡ )
  open Setoid 𝔻[ 𝑳 ]    using  ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ 𝑳 ]

  -- The rungs of the ladder over a, b and w.
  A B : ℕ → 𝕌[ 𝑳 ]
  A zero    = w ∧ a
  A (suc k) = w ∧ (a ∨ B k)
  B zero    = w ∧ b
  B (suc k) = w ∧ (b ∨ A k)

  -- In a modular lattice the ladder stops at the first rung.
  ladder-stops : IsModular 𝓛
    → ∀ k → A (suc k) ≈ (w ∧ a) ∨ (w ∧ b)  ×  B (suc k) ≈ (w ∧ a) ∨ (w ∧ b)
  ladder-stops m zero    = first-A , first-B
    where
    first-A : w ∧ (a ∨ (w ∧ b)) ≈ (w ∧ a) ∨ (w ∧ b)
    first-A = begin
      w ∧ (a ∨ (w ∧ b))        ≈⟨ ∧-comm-law ⟩
      (a ∨ (w ∧ b)) ∧ w        ≈⟨ ∧-cong ∨-comm-law refl ⟩
      ((w ∧ b) ∨ a) ∧ w        ≈˘⟨ m (w ∧ b) a w ∧-lowerˡ ⟩
      (w ∧ b) ∨ (a ∧ w)        ≈⟨ ∨-cong refl ∧-comm-law ⟩
      (w ∧ b) ∨ (w ∧ a)        ≈⟨ ∨-comm-law ⟩
      (w ∧ a) ∨ (w ∧ b)        ∎
    first-B : w ∧ (b ∨ (w ∧ a)) ≈ (w ∧ a) ∨ (w ∧ b)
    first-B = begin
      w ∧ (b ∨ (w ∧ a))        ≈⟨ ∧-comm-law ⟩
      (b ∨ (w ∧ a)) ∧ w        ≈⟨ ∧-cong ∨-comm-law refl ⟩
      ((w ∧ a) ∨ b) ∧ w        ≈˘⟨ m (w ∧ a) b w ∧-lowerˡ ⟩
      (w ∧ a) ∨ (b ∧ w)        ≈⟨ ∨-cong refl ∧-comm-law ⟩
      (w ∧ a) ∨ (w ∧ b)        ∎
  ladder-stops m (suc k) = next-A , next-B
    where
    s : 𝕌[ 𝑳 ]
    s = (w ∧ a) ∨ (w ∧ b)
    first : A 1 ≈ s × B 1 ≈ s
    first = ladder-stops m zero
    ih : A (suc k) ≈ s × B (suc k) ≈ s
    ih = ladder-stops m k
    -- x ∨ (y ∧ x) ≈ x, by absorption.
    absorb : ∀ {x y} → x ∨ (y ∧ x) ≈ x
    absorb = trans ∨-comm-law (trans (∨-cong ∧-comm-law refl) absorbʳ-law)
    next-A : A (suc (suc k)) ≈ s
    next-A = begin
      w ∧ (a ∨ B (suc k))          ≈⟨ ∧-cong refl (∨-cong refl (ih .proj₂)) ⟩
      w ∧ (a ∨ ((w ∧ a) ∨ (w ∧ b))) ≈˘⟨ ∧-cong refl ∨-assoc-law ⟩
      w ∧ ((a ∨ (w ∧ a)) ∨ (w ∧ b)) ≈⟨ ∧-cong refl (∨-cong absorb refl) ⟩
      w ∧ (a ∨ (w ∧ b))            ≈⟨ first .proj₁ ⟩
      s                            ∎
    next-B : B (suc (suc k)) ≈ s
    next-B = begin
      w ∧ (b ∨ A (suc k))          ≈⟨ ∧-cong refl (∨-cong refl (ih .proj₁)) ⟩
      w ∧ (b ∨ ((w ∧ a) ∨ (w ∧ b))) ≈⟨ ∧-cong refl (∨-cong refl ∨-comm-law) ⟩
      w ∧ (b ∨ ((w ∧ b) ∨ (w ∧ a))) ≈˘⟨ ∧-cong refl ∨-assoc-law ⟩
      w ∧ ((b ∨ (w ∧ b)) ∨ (w ∧ a)) ≈⟨ ∧-cong refl (∨-cong absorb refl) ⟩
      w ∧ (b ∨ (w ∧ a))            ≈⟨ first .proj₂ ⟩
      s                            ∎

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive d k with ladder-stops (IsDistributive→IsModular 𝓛 d) k
  ... | A≈s , B≈s = trans A≈s (sym (d w a b)) , trans B≈s (sym (d w a b))
```

#### How the proof goes

Write `p = w ∧ a`, `q = w ∧ b` and `s = p ∨ q`.  The first rung is one use of
the modular law: since `q ≤ w`, we have `q ∨ (a ∧ w) ≈ (q ∨ a) ∧ w`, and up to
commutativity the left side is `s` and the right side is `A₁ = w ∧ (a ∨ q)`.
The same argument with `p ≤ w` gives `B₁ ≈ s`.

Every later rung reduces to the first.  If `Bₖ₊₁ ≈ s`, then
`a ∨ Bₖ₊₁ ≈ (a ∨ p) ∨ q ≈ a ∨ q`, because `p = w ∧ a` is absorbed by `a`; so
`Aₖ₊₂ ≈ w ∧ (a ∨ q) = A₁ ≈ s`.  The rung `Bₖ₊₂` follows in the same way from
`Aₖ₊₁ ≈ s`, and induction on `k` does the rest.  For the distributive case we
apply the modular theorem, since a distributive lattice is modular, and rewrite
`s` as `w ∧ (a ∨ b)` by the distributive law.
