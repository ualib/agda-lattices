---
layout: default
file: "src/Lattices/Semidistributive/FiniteJoins.lagda.md"
title: "Lattices.Semidistributive.FiniteJoins module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### The join semidistributive law for finite joins

This is the [Lattices.Semidistributive.FiniteJoins][] module of the
[agda-lattices][] library.

Theorem 1.21 of [Freese, Ježek, and Nation (1995)][] (p. 18, due to Jónsson and
Kiefer) says that in a join semidistributive lattice the binary law (SD∨) is
equivalent to its form for finite joins,

    w = ⋁ᵢ aᵢ = ⋁ⱼ bⱼ   implies   w = ⋁ᵢⱼ (aᵢ ∧ bⱼ),

and dually in a meet semidistributive lattice.  [Lattices.Free.Semidistributive][]
proves the finite form for free lattices alone, through canonical forms.  This
module proves it for every join semidistributive lattice, by the book's
induction on the two numbers of joinands, in the form in which the proofs that
use it apply it: the joins are taken over a common base `v`, the book's
statement `P(n, m)`, and the conclusion says that `w` lies below every element
that bounds the base and every pairwise meet (`⋁-meets-below`{.AgdaFunction}).
The book's equation is the case of the bound `v ∨ ⋁ᵢⱼ (aᵢ ∧ bⱼ)`, which
every pairwise meet lies below, and the other inequality holds in every
lattice; the dual statement, for a meet semidistributive
lattice, is the theorem at the dual lattice, which for the table lattices of
[Lattices.Table][] is the pair of tables swapped.

The lattice is any `Lattice`{.AgdaFunction} of agda-algebras, with its setoid
equality; membership in a list is propositional, and a member equal to the
element in question is moved along the setoid's reflexivity.  The module
checks in 0.2 s of its own (measured 2026-10-22).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Semidistributive.FiniteJoins where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                                 using ( List ; [] ; _∷_ ; map ; foldr )
open import Data.List.Membership.Propositional             using ( _∈_ )
open import Data.List.Membership.Propositional.Properties  using ( ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.Any                   using ( here ; there )
open import Data.Product                                   using ( _,_ ; proj₁ )
open import Level                                          using ( Level )
open import Relation.Binary                                using ( Setoid )
open import Relation.Binary.PropositionalEquality          using ( refl ) renaming ( sym to ≡-sym )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )

-- Imports from this library ----------------------------------------------------
open import Lattices.Semidistributive  using ( IsJoinSemidistributive )

private variable α ρ : Level
```
-->

#### Joins over a base

Fix a lattice.  `as ∨* v`{.AgdaFunction} is the join of the list `as` over the
base `v`, so that `[] ∨* v` is `v`; the base and every member lie below it, it
lies below every bound of the base and the members, it is monotone in the base,
and two lists over a base can be joined in either order
(`∨*-swap`{.AgdaFunction}).

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∨-comm-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ≤-respˡ-≈ ; ≤-respʳ-≈
                                   ; ∧-lowerˡ ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; sym ; trans ; reflexive )

  infixr 5 _∨*_

  -- The join of a list over a base.
  _∨*_ : List 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ]
  as ∨* v = foldr _∨_ v as

  ∨*-base : ∀ as {v} → v ≤ as ∨* v
  ∨*-base []        = ≤-refl
  ∨*-base (a ∷ as)  = ≤-trans (∨*-base as) ∨-upperʳ

  ∨*-upper : ∀ {a as v} → a ∈ as → a ≤ as ∨* v
  ∨*-upper (here a≡)   = ≤-respˡ-≈ (reflexive (≡-sym a≡)) ∨-upperˡ
  ∨*-upper (there a∈)  = ≤-trans (∨*-upper a∈) ∨-upperʳ

  ∨*-least : ∀ as {v z} → (∀ {a} → a ∈ as → a ≤ z) → v ≤ z → as ∨* v ≤ z
  ∨*-least []        _ v≤z = v≤z
  ∨*-least (a ∷ as)  f v≤z = ∨-least (f (here refl)) (∨*-least as (λ a∈ → f (there a∈)) v≤z)

  ∨*-mono : ∀ as {v v′} → v ≤ v′ → as ∨* v ≤ as ∨* v′
  ∨*-mono as v≤v′ = ∨*-least as (λ a∈ → ∨*-upper a∈) (≤-trans v≤v′ (∨*-base as))

  ∨*-swap : ∀ xs ys {v} → xs ∨* (ys ∨* v) ≤ ys ∨* (xs ∨* v)
  ∨*-swap xs ys = ∨*-least xs (λ x∈ → ≤-trans (∨*-upper x∈) (∨*-base ys)) (∨*-mono ys (∨*-base xs))

  -- Monotonicity of join.
  ∨-mono : ∀ {a b c d} → a ≤ b → c ≤ d → a ∨ c ≤ b ∨ d
  ∨-mono a≤b c≤d = ∨-least (≤-trans a≤b ∨-upperˡ) (≤-trans c≤d ∨-upperʳ)

  -- The pairwise meets of an element with the members of a list.
  meets : 𝕌[ proj₁ 𝑳 ] → List 𝕌[ proj₁ 𝑳 ] → List 𝕌[ proj₁ 𝑳 ]
  meets a bs = map (a ∧_) bs
```

#### Theorem 1.21

The book proves `P(n, m)` by induction on `n + m`: for any base `v`,
`w = v ∨ ⋁ᵢ₌₁ⁿ aᵢ = v ∨ ⋁ⱼ₌₁ᵐ bⱼ` implies `w = v ∨ ⋁ᵢⱼ (aᵢ ∧ bⱼ)`.
`P(1, 1)` is (SD∨).  For `n = 1` and `m > 1`, with `u = v ∨ ⋁ⱼ₌₂ᵐ bⱼ`, the
element `w` is `u ∨ a` and `u ∨ b₁`, so (SD∨) gives `w = u ∨ (a ∧ b₁)`; then
`w = v′ ∨ a = v′ ∨ ⋁ⱼ₌₂ᵐ bⱼ` for the base `v′ = v ∨ (a ∧ b₁)`, and `P(1, m - 1)`
applies.  For `n > 1`, with `u = v ∨ ⋁ᵢ₌₂ⁿ aᵢ`, the element `w` is `u ∨ a₁` and
`u ∨ ⋁ⱼ bⱼ`, so `P(1, m)` gives `w = u ∨ ⋁ⱼ (a₁ ∧ bⱼ)`; then
`w = v″ ∨ ⋁ᵢ₌₂ⁿ aᵢ = v″ ∨ ⋁ⱼ bⱼ` for the base `v″ = v ∨ ⋁ⱼ (a₁ ∧ bⱼ)`, and
`P(n - 1, m)` applies.  The two inductions are `one-many`{.AgdaFunction} and
`⋁-meets-below`{.AgdaFunction}, each stated with a bound `z` in place of the
join of the meets: `w` lies below `z` whenever the base and the pairwise meets
do.  The induction on the lists makes the cases `m = 0` and `n = 0` trivial,
since a join over the base `v` of no elements is `v`.

```agda
  module _ (sd : IsJoinSemidistributive 𝑳) where

    -- P(1, m): if a ∨ v = ⋁ bs ∨ v, then a ∨ v lies below every bound of v and the meets a ∧ b.
    one-many : ∀ a bs {v z} → a ∨ v ≈ bs ∨* v → v ≤ z → (∀ {b} → b ∈ bs → a ∧ b ≤ z) → a ∨ v ≤ z
    one-many a []        {v} {z} e v≤z _ = ≤-respˡ-≈ (sym e) v≤z
    one-many a (b ∷ bs)  {v} {z} e v≤z f =
      ≤-trans (∨-mono ≤-refl ∨-upperˡ) (one-many a bs e′ (∨-least v≤z (f (here refl))) (λ b∈ → f (there b∈)))
      where
      u : 𝕌[ proj₁ 𝑳 ]
      u = bs ∨* v

      v′ : 𝕌[ proj₁ 𝑳 ]
      v′ = v ∨ (a ∧ b)

      -- w = a ∨ v = b ∨ u, and u ≤ w, so w = u ∨ a = u ∨ b and (SD∨) gives w = u ∨ (a ∧ b).
      u≤w : u ≤ a ∨ v
      u≤w = ≤-respʳ-≈ (sym e) ∨-upperʳ

      av≈au : a ∨ v ≈ a ∨ u
      av≈au = ≤-antisym (∨-least ∨-upperˡ (≤-trans (∨*-base bs) ∨-upperʳ)) (∨-least ∨-upperˡ u≤w)

      ua≡ub : u ∨ a ≈ u ∨ b
      ua≡ub = trans ∨-comm-law (trans (sym av≈au) (trans e ∨-comm-law))

      w≈ : a ∨ v ≈ u ∨ (a ∧ b)
      w≈ = trans av≈au (trans ∨-comm-law (sd u a b ua≡ub))

      -- Over the base v′, the two joins agree: a ∨ v′ = w = ⋁ bs ∨ v′.
      e′ : a ∨ v′ ≈ bs ∨* v′
      e′ = ≤-antisym
        (∨-least (≤-trans ∨-upperˡ w≤) (∨-least (≤-trans ∨-upperʳ w≤) (≤-trans ∧-lowerˡ (≤-trans ∨-upperˡ w≤))))
        (∨*-least bs (λ b′∈ → ≤-trans (∨*-upper b′∈) (≤-trans u≤w (∨-mono ≤-refl ∨-upperˡ)))
                     (∨-least (≤-trans ∨-upperʳ (∨-mono ≤-refl ∨-upperˡ)) (≤-trans ∧-lowerˡ ∨-upperˡ)))
        where
        -- w ≤ ⋁ bs ∨ v′, since w = u ∨ (a ∧ b) and u ∨ (a ∧ b) ≤ ⋁ bs ∨ (v ∨ (a ∧ b)).
        w≤ : a ∨ v ≤ bs ∨* v′
        w≤ = ≤-respˡ-≈ (sym w≈) (∨-least (∨*-mono bs ∨-upperˡ) (≤-trans ∨-upperʳ (∨*-base bs)))

    -- Theorem 1.21, P(n, m): if ⋁ as ∨ v = ⋁ bs ∨ v, that element lies below every bound of v and
    -- of the pairwise meets a ∧ b, a ∈ as, b ∈ bs.
    ⋁-meets-below : ∀ as bs {v z} → as ∨* v ≈ bs ∨* v → v ≤ z
                  → (∀ {a b} → a ∈ as → b ∈ bs → a ∧ b ≤ z) → as ∨* v ≤ z
    ⋁-meets-below []        bs {v} {z} e v≤z _ = v≤z
    ⋁-meets-below (a ∷ as)  bs {v} {z} e v≤z f =
      ≤-trans w≤ (⋁-meets-below as bs e″ v″≤z (λ a∈ b∈ → f (there a∈) b∈))
      where
      u : 𝕌[ proj₁ 𝑳 ]
      u = as ∨* v

      -- The new base: v joined with the meets of a with the members of bs.
      v″ : 𝕌[ proj₁ 𝑳 ]
      v″ = meets a bs ∨* v

      -- w = a ∨ u = ⋁ bs ∨ v, and v ≤ u, so also w = ⋁ bs ∨ u.
      e₁ : a ∨ u ≈ bs ∨* u
      e₁ = ≤-antisym (≤-trans (≤-respʳ-≈ e ≤-refl) (∨*-mono bs (∨*-base as)))
                     (∨*-least bs (λ b∈ → ≤-respʳ-≈ (sym e) (∨*-upper b∈)) ∨-upperʳ)

      -- P(1, m) at the base u: w ≤ u ∨ ⋁ meets a bs.
      w≤m : a ∨ u ≤ meets a bs ∨* u
      w≤m = one-many a bs e₁ (∨*-base (meets a bs)) (λ b∈ → ∨*-upper (∈-map⁺ (a ∧_) b∈))

      -- Hence w ≤ ⋁ as ∨ v″.
      w≤ : a ∨ u ≤ as ∨* v″
      w≤ = ≤-trans w≤m (∨*-swap (meets a bs) as)

      -- The meets lie below w, so both joins over v″ equal w.
      m≤w : ∀ {m} → m ∈ meets a bs → m ≤ a ∨ u
      m≤w m∈ with ∈-map⁻ (a ∧_) m∈
      ... | _ , _ , m≡ = ≤-respˡ-≈ (reflexive (≡-sym m≡)) (≤-trans ∧-lowerˡ ∨-upperˡ)
    
      v″≤w : v″ ≤ a ∨ u
      v″≤w = ∨*-least (meets a bs) m≤w (≤-trans (∨*-base as) ∨-upperʳ)

      e″ : as ∨* v″ ≈ bs ∨* v″
      e″ = ≤-antisym
        (≤-trans (∨*-least as (λ a′∈ → ≤-trans (∨*-upper a′∈) ∨-upperʳ) v″≤w) (≤-respˡ-≈ (sym e) (∨*-mono bs (∨*-base (meets a bs)))))
        (≤-trans (∨*-least bs (λ b∈ → ≤-respʳ-≈ (sym e) (∨*-upper b∈)) v″≤w) w≤)

      v″≤z : v″ ≤ z
      v″≤z = ∨*-least (meets a bs) (λ m∈ → meet≤z m∈) v≤z
        where
        meet≤z : ∀ {m} → m ∈ meets a bs → m ≤ z
        meet≤z m∈ with ∈-map⁻ (a ∧_) m∈
        ... | _ , b∈ , m≡ = ≤-respˡ-≈ (reflexive (≡-sym m≡)) (f (here refl) b∈)
      ```
