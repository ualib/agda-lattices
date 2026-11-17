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

Write `c` for `(w ∧ a) ∨ (w ∧ b)`.  Every rung is a meet with `w`, so it lies
below `w`, and for `x ≤ w` the modular law, read from the side of `w`, gives
`w ∧ (y ∨ x) ≈ (w ∧ y) ∨ x` (the local lemma `step`).  The proof is an
induction on `k` that proves both equations at once, as follows:

+  at the first rung, `step` at `x = w ∧ b` turns `A 1` into `c` outright, and
   at `x = w ∧ a` turns `B 1` into `(w ∧ b) ∨ (w ∧ a)`, which is `c` by
   commutativity;
+  at rung `k + 2`, `step` turns `A (k + 2)` into `(w ∧ a) ∨ B (k + 1)`, the
   induction hypothesis rewrites `B (k + 1)` to `c`, and `(w ∧ a) ∨ c ≈ c`
   by associativity and idempotence; the case of `B` is the same with `a` and
   `b` exchanged.

The distributive case applies the modular one through
`IsDistributive→IsModular`{.AgdaFunction} and then rewrites `c` to
`w ∧ (a ∨ b)` by the distributive law.

```agda
module _ {α ρ : Level} (𝓛@(𝑳 , 𝑳⊨Th-Lattice ) : Lattice α ρ) (a b w : 𝕌[ 𝑳 ]) where
  open Lattice-Op 𝓛     using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                               ; ∨-assoc-law ; ∨-idem-law )
  open Lattice-Order 𝓛  using ( _≤_ ; ∧-lowerˡ )
  open Setoid 𝔻[ 𝑳 ]    using ( _≈_ ; refl ; sym ; trans )
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
    c : 𝕌[ 𝑳 ]
    c = (w ∧ a) ∨ (w ∧ b)

    -- The modular law at x ≤ w, read from the side of w.
    step : ∀ y x → x ≤ w → w ∧ (y ∨ x) ≈ (w ∧ y) ∨ x
    step y x x≤w = begin
      w ∧ (y ∨ x)    ≈⟨ ∧-comm-law ⟩
      (y ∨ x) ∧ w    ≈⟨ ∧-cong ∨-comm-law refl ⟩
      (x ∨ y) ∧ w    ≈⟨ sym (m x y w x≤w) ⟩
      x ∨ (y ∧ w)    ≈⟨ ∨-comm-law ⟩
      (y ∧ w) ∨ x    ≈⟨ ∨-cong ∧-comm-law refl ⟩
      (w ∧ y) ∨ x    ∎

    -- Joining either generator of c to c gives c back.
    absorb-a : (w ∧ a) ∨ c ≈ c
    absorb-a = trans (sym ∨-assoc-law) (∨-cong ∨-idem-law refl)

    absorb-b : (w ∧ b) ∨ c ≈ c
    absorb-b = begin
      (w ∧ b) ∨ ((w ∧ a) ∨ (w ∧ b))  ≈⟨ ∨-cong refl ∨-comm-law ⟩
      (w ∧ b) ∨ ((w ∧ b) ∨ (w ∧ a))  ≈⟨ sym ∨-assoc-law ⟩
      ((w ∧ b) ∨ (w ∧ b)) ∨ (w ∧ a)  ≈⟨ ∨-cong ∨-idem-law refl ⟩
      (w ∧ b) ∨ (w ∧ a)              ≈⟨ ∨-comm-law ⟩
      c                              ∎

    go : ∀ k → A (suc k) ≈ c  ×  B (suc k) ≈ c
    go zero    = step a (w ∧ b) ∧-lowerˡ , trans (step b (w ∧ a) ∧-lowerˡ) ∨-comm-law
    go (suc k) = A-step , B-step
      where
      A-step : A (suc (suc k)) ≈ c
      A-step = begin
        w ∧ (a ∨ B (suc k))  ≈⟨ step a (B (suc k)) ∧-lowerˡ ⟩
        (w ∧ a) ∨ B (suc k)  ≈⟨ ∨-cong refl (proj₂ (go k)) ⟩
        (w ∧ a) ∨ c          ≈⟨ absorb-a ⟩
        c                    ∎

      B-step : B (suc (suc k)) ≈ c
      B-step = begin
        w ∧ (b ∨ A (suc k))  ≈⟨ step b (A (suc k)) ∧-lowerˡ ⟩
        (w ∧ b) ∨ A (suc k)  ≈⟨ ∨-cong refl (proj₁ (go k)) ⟩
        (w ∧ b) ∨ c          ≈⟨ absorb-b ⟩
        c                    ∎

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive d k with ladder-stops (IsDistributive→IsModular 𝓛 d) k
  ... | A≈c , B≈c = trans A≈c (sym (d w a b)) , trans B≈c (sym (d w a b))
```
