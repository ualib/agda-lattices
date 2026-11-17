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
open import Data.Product     using ( _×_ ; _,_ ; proj₁ ; proj₂ )
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
module _ {α ρ : Level} (𝑳 : Lattice α ρ) (a b w : 𝕌[ proj₁ 𝑳 ]) where
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ )

  -- The rungs of the ladder over a, b and w.
  A B : ℕ → 𝕌[ proj₁ 𝑳 ]
  A zero    = w ∧ a
  A (suc k) = w ∧ (a ∨ B k)
  B zero    = w ∧ b
  B (suc k) = w ∧ (b ∨ A k)

  -- In a modular lattice the ladder stops at the first rung.
  ladder-stops : IsModular 𝑳 → ∀ k
    → A (suc k) ≈ (w ∧ a) ∨ (w ∧ b)  ×  B (suc k) ≈ (w ∧ a) ∨ (w ∧ b)
  ladder-stops = rungs
    where
    open Lattice-Op 𝑳          using ( ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law ; ∨-assoc-law )
    open Lattice-Order 𝑳       using ( ≤-via-∨ ; ∧-lowerˡ ; ∧-lowerʳ )
    open Setoid 𝔻[ proj₁ 𝑳 ]   using ( refl ; trans )
    open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

    p q m : 𝕌[ proj₁ 𝑳 ]
    p = w ∧ a
    q = w ∧ b
    m = p ∨ q

    -- The first rungs, by the modular law at q ≤ w and at p ≤ w.
    A₁ : IsModular 𝑳 → w ∧ (a ∨ q) ≈ m
    A₁ mod = begin
      w ∧ (a ∨ q)    ≈⟨ ∧-comm-law ⟩
      (a ∨ q) ∧ w    ≈⟨ ∧-cong ∨-comm-law refl ⟩
      (q ∨ a) ∧ w    ≈˘⟨ mod q a w ∧-lowerˡ ⟩
      q ∨ (a ∧ w)    ≈⟨ ∨-cong refl ∧-comm-law ⟩
      q ∨ p          ≈⟨ ∨-comm-law ⟩
      m              ∎

    B₁ : IsModular 𝑳 → w ∧ (b ∨ p) ≈ m
    B₁ mod = begin
      w ∧ (b ∨ p)    ≈⟨ ∧-comm-law ⟩
      (b ∨ p) ∧ w    ≈⟨ ∧-cong ∨-comm-law refl ⟩
      (p ∨ b) ∧ w    ≈˘⟨ mod p b w ∧-lowerˡ ⟩
      p ∨ (b ∧ w)    ≈⟨ ∨-cong refl ∧-comm-law ⟩
      m              ∎

    -- Joining a to m adds only q, since p ≤ a; dually for b.
    a∨m : a ∨ m ≈ a ∨ q
    a∨m = begin
      a ∨ (p ∨ q)    ≈˘⟨ ∨-assoc-law ⟩
      (a ∨ p) ∨ q    ≈⟨ ∨-cong (trans ∨-comm-law (≤-via-∨ ∧-lowerʳ)) refl ⟩
      a ∨ q          ∎

    b∨m : b ∨ m ≈ b ∨ p
    b∨m = begin
      b ∨ (p ∨ q)    ≈⟨ ∨-cong refl ∨-comm-law ⟩
      b ∨ (q ∨ p)    ≈˘⟨ ∨-assoc-law ⟩
      (b ∨ q) ∨ p    ≈⟨ ∨-cong (trans ∨-comm-law (≤-via-∨ ∧-lowerʳ)) refl ⟩
      b ∨ p          ∎

    rungs : IsModular 𝑳 → ∀ k → A (suc k) ≈ m  ×  B (suc k) ≈ m
    rungs mod zero    = A₁ mod , B₁ mod
    rungs mod (suc k) =
      trans (∧-cong refl (trans (∨-cong refl (proj₂ ih)) a∨m)) (A₁ mod) ,
      trans (∧-cong refl (trans (∨-cong refl (proj₁ ih)) b∨m)) (B₁ mod)
      where
      ih = rungs mod k

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝑳 → ∀ k
    → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive dist k =
    trans (proj₁ stops) (sym (dist w a b)) , trans (proj₂ stops) (sym (dist w a b))
    where
    open Setoid 𝔻[ proj₁ 𝑳 ]  using ( sym ; trans )
    stops = ladder-stops (IsDistributive→IsModular 𝑳 dist) k
```

#### The proof

Write `p = w ∧ a`, `q = w ∧ b` and `m = p ∨ q`.  The first rung is the modular
law applied twice.  Since `q ≤ w`, the law at `q ≤ w` and `a` gives
`A₁ = w ∧ (a ∨ q) ≈ q ∨ (a ∧ w) ≈ m`; since `p ≤ w`, the law at `p ≤ w` and `b`
gives `B₁ = w ∧ (b ∨ p) ≈ m` in the same way.  For the higher rungs, joining `a`
to `m` adds only `q`, because `p ≤ a`; that is, `a ∨ m ≈ a ∨ q`, and dually
`b ∨ m ≈ b ∨ p`.  So if `Bₖ₊₁ ≈ m`, then `Aₖ₊₂ ≈ w ∧ (a ∨ m) ≈ w ∧ (a ∨ q) ≈ m`,
and likewise for `Bₖ₊₂`, and induction on `k` finishes the proof.  In a
distributive lattice, which is modular by
`IsDistributive→IsModular`{.AgdaFunction}, the distributive law at `w`, `a`, `b`
turns `m` into `w ∧ (a ∨ b)`.
