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
  open Lattice-Op 𝓛     using  ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law )
  open Lattice-Order 𝓛  using  ( _≤_ ; ≤-via-∨ ; ∧-lowerˡ ; ∨-upperˡ ; ∨-upperʳ )
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
  ladder-stops m = go
    where
    p q c : 𝕌[ 𝑳 ]
    p = w ∧ a
    q = w ∧ b
    c = p ∨ q

    -- One step of the ladder, by the modular law at v ≤ w.
    step : ∀ u v → v ≤ w → w ∧ (u ∨ v) ≈ (w ∧ u) ∨ v
    step u v v≤w = begin
      w ∧ (u ∨ v)   ≈⟨ ∧-comm-law ⟩
      (u ∨ v) ∧ w   ≈⟨ ∧-cong ∨-comm-law refl ⟩
      (v ∨ u) ∧ w   ≈˘⟨ m v u w v≤w ⟩
      v ∨ (u ∧ w)   ≈⟨ ∨-comm-law ⟩
      (u ∧ w) ∨ v   ≈⟨ ∨-cong ∧-comm-law refl ⟩
      (w ∧ u) ∨ v   ∎

    -- Joining c with something below it changes nothing.
    p∨c≈c : p ∨ c ≈ c
    p∨c≈c = ≤-via-∨ ∨-upperˡ

    q∨c≈c : q ∨ c ≈ c
    q∨c≈c = ≤-via-∨ ∨-upperʳ

    go : ∀ k → A (suc k) ≈ c  ×  B (suc k) ≈ c
    go zero     = step a q ∧-lowerˡ , trans (step b p ∧-lowerˡ) ∨-comm-law
    go (suc k)  = trans (step a (B (suc k)) ∧-lowerˡ) (trans (∨-cong refl IHB) p∨c≈c)
                , trans (step b (A (suc k)) ∧-lowerˡ) (trans (∨-cong refl IHA) q∨c≈c)
      where
      IHA = proj₁ (go k)
      IHB = proj₂ (go k)

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive d k = trans A≈c c≈w∧[a∨b] , trans B≈c c≈w∧[a∨b]
    where
    A≈c = proj₁ (ladder-stops (IsDistributive→IsModular 𝓛 d) k)
    B≈c = proj₂ (ladder-stops (IsDistributive→IsModular 𝓛 d) k)

    c≈w∧[a∨b] : (w ∧ a) ∨ (w ∧ b) ≈ w ∧ (a ∨ b)
    c≈w∧[a∨b] = sym (d w a b)
```

#### How the proof goes

Write `p = w ∧ a`, `q = w ∧ b` and `c = p ∨ q`.  Every rung is a meet with `w`,
so every rung lies below `w`, and that is all the modular law needs.  For any
`u`, and any `v ≤ w`, the modular law at the triple `v ≤ w`, `u` gives

    w ∧ (u ∨ v)  ≈  v ∨ (u ∧ w)  ≈  (w ∧ u) ∨ v,

which is the lemma `step`.  With `v = Bₖ` it turns `Aₖ₊₁` into `p ∨ Bₖ`, and
with `v = Aₖ` it turns `Bₖ₊₁` into `q ∨ Aₖ`.  At `k = 0` these are `p ∨ q` and
`q ∨ p`, both `c`.  At `k + 1` the induction hypothesis makes them `p ∨ c` and
`q ∨ c`, and both are `c` because `p` and `q` lie below `c`.

The distributive case reuses the modular one, since a distributive lattice is
modular (`IsDistributive→IsModular`), and finishes with one application of the
distributive law, `w ∧ (a ∨ b) ≈ (w ∧ a) ∨ (w ∧ b)`.
