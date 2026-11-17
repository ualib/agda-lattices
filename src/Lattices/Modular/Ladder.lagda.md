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
open import Data.Product     using ( _×_ ; proj₁ ; proj₂ ; _,_)
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

Write `p = w ∧ a`, `q = w ∧ b` and `c = p ∨ q`.  The proof rests on the
modular law in the shape `w ∧ (x ∨ u) = (w ∧ x) ∨ u` for `u ≤ w`
(`pull`{.AgdaFunction}), which is Dedekind's law at `u ≤ w`, `x` after
commuting.  Since `q` and `p` lie below `w`, it computes the first rung:
`A₁ = w ∧ (a ∨ q) = p ∨ q` and `B₁ = w ∧ (b ∨ p) = q ∨ p`, both `c`.  For the
later rungs, absorption gives `a ∨ c = a ∨ q` and `b ∨ c = b ∨ p`, since `a`
already lies above `p` and `b` above `q`; so once `Bₖ` and `Aₖ` are `c`, the
next rung is `w ∧ (a ∨ q)` and `w ∧ (b ∨ p)` again, which is the first rung.
Induction on `k` finishes the proof.  In a distributive lattice the same
argument applies, by `IsDistributive→IsModular`{.AgdaFunction}, and the
distributive law at `w`, `a`, `b` turns `c` into `w ∧ (a ∨ b)`.

```agda
module _ {α ρ : Level} (𝓛@(𝑳 , 𝑳⊨Th-Lattice ) : Lattice α ρ) (a b w : 𝕌[ 𝑳 ]) where
  open Lattice-Op 𝓛     using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                                ; ∨-assoc-law ; absorbʳ-law )
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
  ladder-stops m = stops
    where
    p q c : 𝕌[ 𝑳 ]
    p = w ∧ a
    q = w ∧ b
    c = p ∨ q

    -- The modular law, in the shape the ladder uses: u ≤ w lets u leave the meet.
    pull : ∀ x u → u ≤ w → w ∧ (x ∨ u) ≈ (w ∧ x) ∨ u
    pull x u u≤w = begin
      w ∧ (x ∨ u)  ≈⟨ ∧-comm-law ⟩
      (x ∨ u) ∧ w  ≈⟨ ∧-cong ∨-comm-law refl ⟩
      (u ∨ x) ∧ w  ≈˘⟨ m u x w u≤w ⟩
      u ∨ (x ∧ w)  ≈⟨ ∨-cong refl ∧-comm-law ⟩
      u ∨ (w ∧ x)  ≈⟨ ∨-comm-law ⟩
      (w ∧ x) ∨ u  ∎

    -- The first rung.
    A₁ : w ∧ (a ∨ q) ≈ c
    A₁ = pull a q ∧-lowerˡ

    B₁ : w ∧ (b ∨ p) ≈ c
    B₁ = trans (pull b p ∧-lowerˡ) ∨-comm-law

    -- Joining c to a adds only q, and joining c to b adds only p.
    absorb : ∀ x → x ∨ (w ∧ x) ≈ x
    absorb x = trans ∨-comm-law (trans (∨-cong ∧-comm-law refl) absorbʳ-law)

    a∨c : a ∨ c ≈ a ∨ q
    a∨c = begin
      a ∨ (p ∨ q)  ≈˘⟨ ∨-assoc-law ⟩
      (a ∨ p) ∨ q  ≈⟨ ∨-cong (absorb _) refl ⟩
      a ∨ q        ∎

    b∨c : b ∨ c ≈ b ∨ p
    b∨c = begin
      b ∨ (p ∨ q)  ≈⟨ ∨-cong refl ∨-comm-law ⟩
      b ∨ (q ∨ p)  ≈˘⟨ ∨-assoc-law ⟩
      (b ∨ q) ∨ p  ≈⟨ ∨-cong (absorb _) refl ⟩
      b ∨ p        ∎

    stops : ∀ k → A (suc k) ≈ c  ×  B (suc k) ≈ c
    stops zero    = A₁ , B₁
    stops (suc k) =
      trans (∧-cong refl (trans (∨-cong refl (proj₂ (stops k))) a∨c)) A₁ ,
      trans (∧-cong refl (trans (∨-cong refl (proj₁ (stops k))) b∨c)) B₁

  -- In a distributive lattice it stops at w ∧ (a ∨ b).
  ladder-stops-distributive : IsDistributive 𝓛
    → ∀ k → A (suc k) ≈ w ∧ (a ∨ b)  ×  B (suc k) ≈ w ∧ (a ∨ b)
  ladder-stops-distributive d k =
    trans (proj₁ s) (sym (d w a b)) , trans (proj₂ s) (sym (d w a b))
    where
    s = ladder-stops (IsDistributive→IsModular 𝓛 d) k
```
