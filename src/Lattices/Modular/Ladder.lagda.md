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
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

-- Imports from this library --------------------------------------------------
open import Lattices.Modular  using ( IsModular ; IsDistributive ; IsDistributive→IsModular )
```
-->

#### The ladder and the theorem

Write `p = w ∧ a`, `q = w ∧ b` and `c = p ∨ q`.  The proof uses the modular law
only at a pair `w ∧ y ≤ w`, where it reads

    w ∧ (x ∨ (w ∧ y)) ≈ (w ∧ y) ∨ (w ∧ x)

(the helper `side`{.AgdaFunction}).  At `x = a`, `y = b` it says the first rung
`A₁ = w ∧ (a ∨ q)` is `q ∨ p ≈ c`, and at `x = b`, `y = a` it says
`B₁ = w ∧ (b ∨ p)` is `c`.  Every later rung is a rung over `c`: since
`p ≤ a`, the join `a ∨ c = a ∨ p ∨ q` absorbs `p` and is `a ∨ q`, so
`w ∧ (a ∨ c)` is `A₁` again, and symmetrically `w ∧ (b ∨ c)` is `B₁`.  An
induction on `k` finishes the proof.  The distributive case applies the
modular one, since a distributive lattice is modular, and rewrites `c` to
`w ∧ (a ∨ b)` by the distributive law.

```agda
module _ {α ρ : Level} (𝓛@(𝑳 , 𝑳⊨Th-Lattice ) : Lattice α ρ) (a b w : 𝕌[ 𝑳 ]) where
  open Lattice-Op 𝓛     using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                               ; ∨-assoc-law ; absorbʳ-law )
  open Lattice-Order 𝓛  using ( ∧-lowerˡ )
  open Setoid 𝔻[ 𝑳 ]    using ( _≈_ ; refl ; sym ; trans )

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

    -- The modular law at w ∧ y ≤ w: w ∧ (x ∨ (w ∧ y)) ≈ (w ∧ y) ∨ (w ∧ x).
    side : ∀ x y → w ∧ (x ∨ (w ∧ y)) ≈ (w ∧ y) ∨ (w ∧ x)
    side x y = trans ∧-comm-law (trans (∧-cong ∨-comm-law refl)
                 (trans (sym (m (w ∧ y) x w ∧-lowerˡ)) (∨-cong refl ∧-comm-law)))

    -- x absorbs w ∧ x from a join: x ∨ ((w ∧ x) ∨ y) ≈ x ∨ y.
    absorb : ∀ x y → x ∨ ((w ∧ x) ∨ y) ≈ x ∨ y
    absorb x y = trans (sym ∨-assoc-law)
                   (∨-cong (trans ∨-comm-law (trans (∨-cong ∧-comm-law refl) absorbʳ-law)) refl)

    -- The first rungs.
    A₁ : w ∧ (a ∨ q) ≈ c
    A₁ = trans (side a b) ∨-comm-law

    B₁ : w ∧ (b ∨ p) ≈ c
    B₁ = side b a

    -- A rung over c is c again.
    stepA : ∀ {y} → y ≈ c → w ∧ (a ∨ y) ≈ c
    stepA y≈c = trans (∧-cong refl (trans (∨-cong refl y≈c) (absorb a q))) A₁

    stepB : ∀ {y} → y ≈ c → w ∧ (b ∨ y) ≈ c
    stepB y≈c = trans (∧-cong refl (trans (∨-cong refl (trans y≈c ∨-comm-law)) (absorb b p))) B₁

    go : ∀ k → A (suc k) ≈ c  ×  B (suc k) ≈ c
    go zero    = A₁ , B₁
    go (suc k) = let (A≈c , B≈c) = go k in stepA B≈c , stepB A≈c

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive d k = let (A≈c , B≈c) = ladder-stops (IsDistributive→IsModular 𝓛 d) k
    in trans A≈c (sym (d w a b)) , trans B≈c (sym (d w a b))
```
