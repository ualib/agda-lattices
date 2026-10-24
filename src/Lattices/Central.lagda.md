---
layout: default
file: "src/Lattices/Central.lagda.md"
title: "Lattices.Central module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Neutral and central elements

This is the [Lattices.Central][] module of the [agda-lattices][] library.

An element `a` of a lattice is *neutral* when the median identity

    (a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a) = (a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a)

holds for all `x` and `y` ([Grätzer (1998)][], Chapter III, Definition 2.1).
Birkhoff defined neutrality by asking that every triple `a, x, y` generate a
distributive sublattice, and proved that this is the same as `a` being
*distributive* (`a ∨ (x ∧ y) = (a ∨ x) ∧ (a ∨ y)`), dually distributive, and
*cancellable* (`a ∧ x = a ∧ y` and `a ∨ x = a ∨ y` imply `x = y`); that the
median identity alone implies all of this is Grätzer's Theorem 2.4; whether
the identity and Birkhoff's definition agree was asked by Grätzer and
Schmidt, and answered by Grätzer, by Hashimoto and Kinugawa, and by
Iqbalunissa.  An element is *complemented* when it has a complement, an
element meeting it in a bottom and joining it in a top; and *central* when it
is neutral and complemented ([Birkhoff (1948)][], Chapter II, Sections 9 and
10; the third edition has them in Chapter III, Sections 8 and 9).  The central
elements of a bounded lattice are exactly the elements along which it
decomposes as a direct product, which is the theorem of
[Lattices.Central.Decomposition][]; this module supplies the notions and the
lemmas it needs, and decides them in a finite lattice.

The median identity is taken as the definition because a finite sweep decides
it, and the three consequences are proved from it as named lemmas, following
Grätzer's proof of Theorem 2.4, (i) implies (ii).  Complements are defined
without fixing bounds: `a'` is a complement of `a` when `a ∧ a'` is a bottom
and `a ∨ a'` a top (`AreComplements`{.AgdaFunction}).  In a bounded lattice
this is the usual `a ∧ a' = 0` and `a ∨ a' = 1`, since bottoms and tops are
unique up to equality (`complements-from-bounds`{.AgdaFunction},
`complements-∧`{.AgdaFunction}, `complements-∨`{.AgdaFunction}), and in a
lattice without bounds it says, correctly, that nothing is complemented.  A
lattice is *directly indecomposable* when it has two different elements and
every central element is a bottom or a top
(`IsDirectlyIndecomposable`{.AgdaFunction}); the decomposition theorem makes
this agree with the factor-congruence definition of agda-algebras'
`Setoid.Decompositions` for bounded lattices, and a module that imports both
qualifies one.

The module defines the following:

+  `IsNeutral`{.AgdaFunction}, `AreComplements`{.AgdaFunction},
   `IsComplemented`{.AgdaFunction}, `IsCentral`{.AgdaFunction} and
   `IsDirectlyIndecomposable`{.AgdaFunction} on any lattice;
+  the consequences of neutrality: `neutral-∨-distr`{.AgdaFunction},
   `neutral-∧-distr`{.AgdaFunction} (by duality, through the dual lattice of
   [Lattices.Dual][]) and `neutral-cancel`{.AgdaFunction};
   the bounds are neutral (`bottom-neutral`{.AgdaFunction},
   `top-neutral`{.AgdaFunction}) and complement each other;
+  each notion respects equality, and is carried along an isomorphism
   (`IsNeutral-I-invar`{.AgdaFunction}, `IsCentral-I-invar`{.AgdaFunction},
   `IsDirectlyIndecomposable-I-invar`{.AgdaFunction}) and into a product
   componentwise (`×ˡ-neutral`{.AgdaFunction},
   `×ˡ-complements`{.AgdaFunction});
+  the decisions in a finite lattice: `isNeutral?`{.AgdaFunction},
   `isComplemented?`{.AgdaFunction}, `isCentral?`{.AgdaFunction},
   `isDirectlyIndecomposable?`{.AgdaFunction}, and the search
   `properCentral`{.AgdaFunction} that turns a negative verdict into a
   central element that is neither bottom nor top.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Central where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Empty                       using ( ⊥-elim )
open import Data.Fin.Base                    using ( Fin )
open import Data.Fin.Properties              using ( all? ; ¬∀⟶∃¬ )
open import Data.Product                     using ( _×_ ; _,_ ; proj₁ ; proj₂ ; ∃-syntax )
open import Data.Sum.Base                    using ( _⊎_ ; inj₁ ; inj₂ ) renaming ( map to ⊎-map )
open import Function                         using ( Func ; _∘_ )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Nullary.Decidable.Core  using ( Dec ; yes ; no ; map′ ; _×-dec_ ; _⊎-dec_ ; _→-dec_ )
open import Relation.Nullary.Negation.Core   using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Properties.Lattice          using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic    using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic                 using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite                using ( FiniteAlgebra ; all²? ; exists? )
open import Setoid.Congruences.Monolith           using ( Nontrivial )
open import Setoid.Decompositions.Finite          using ( nontrivial? )
open import Setoid.Homomorphisms.Basic            using ( hom )
open import Setoid.Homomorphisms.Isomorphisms     using ( _≅_ ; ≅-sym ; ≅toInjective )

-- Imports from this library --------------------------------------------------------
open import Lattices.Dual              using ( dualLattice ; module LatticeDual )
open import Lattices.Product           using ( _×ˡ_ )
open import Lattices.Semidistributive  using ( hom-preserves-∧ ; hom-preserves-∨ ; hom-preserves-≤ )

open Func renaming ( to to _⟨$⟩_ )
open _≅_

private variable α β γ ρ σ τ : Level
```
-->

#### The predicates

Fix a lattice `𝑳`{.AgdaBound}, with the curried operations of
`Lattice-Op`{.AgdaModule} and the meet order `x ≤ y`, meaning `x ∧ y ≈ x`, of
`Lattice-Order`{.AgdaModule}, with its `IsBottom`{.AgdaFunction} and
`IsTop`{.AgdaFunction}.  The median identity at `a`, `x`, `y` is a separate
definition (`MedianAt`{.AgdaFunction}), so that a sweep can decide it instance
by instance; neutrality is its universal closure in `x` and `y`.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( IsBottom ; IsTop )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )

  private
    U : Type α
    U = 𝕌[ proj₁ 𝑳 ]

  -- The median identity at a, x, y.
  MedianAt : U → U → U → Type ρ
  MedianAt a x y = (a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a) ≈ (a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a)

  -- a is neutral: the median identity holds at a for all x, y.
  IsNeutral : U → Type (α ⊔ ρ)
  IsNeutral a = ∀ x y → MedianAt a x y

  -- a' is a complement of a: their meet is a bottom and their join a top.
  AreComplements : U → U → Type (α ⊔ ρ)
  AreComplements a a' = IsBottom (a ∧ a') × IsTop (a ∨ a')

  -- a has a complement.
  IsComplemented : U → Type (α ⊔ ρ)
  IsComplemented a = ∃[ a' ] AreComplements a a'

  -- a is central: neutral and complemented.
  IsCentral : U → Type (α ⊔ ρ)
  IsCentral a = IsNeutral a × IsComplemented a

  -- A central element that is neither a bottom nor a top.
  ProperCentral : Type (α ⊔ ρ)
  ProperCentral = ∃[ a ] (IsCentral a × ¬ IsBottom a × ¬ IsTop a)

  -- 𝑳 is directly indecomposable: nontrivial, and every central element is a bound.
  IsDirectlyIndecomposable : Type (α ⊔ ρ)
  IsDirectlyIndecomposable = Nontrivial (proj₁ 𝑳) × (∀ a → IsCentral a → IsBottom a ⊎ IsTop a)
```

#### Order lemmas

Three absorption facts about the order, used below: a join absorbs a smaller
joinand, a meet absorbs a larger meetand, and, in the shapes Grätzer's
computation produces, a join `a ∨ ((p ∨ q) ∨ r)` loses `p` and `r` when both lie
below `a`, and a meet `u ∧ (v ∧ w)` loses `w` when `u` lies below it.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-comm-law ; ∨-comm-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-trans ; ≤-antisym ; ≤-via-∨
                                   ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; trans )

  -- A join absorbs a joinand below the other.
  ∨-absorb-≤ : ∀ {z w} → z ≤ w → w ∨ z ≈ w
  ∨-absorb-≤ z≤w = trans ∨-comm-law (≤-via-∨ z≤w)

  -- A meet absorbs a meetand above the other.
  ∧-absorb-≤ : ∀ {z w} → z ≤ w → w ∧ z ≈ z
  ∧-absorb-≤ z≤w = trans ∧-comm-law z≤w

  -- a ∨ ((p ∨ q) ∨ r) ≈ a ∨ q when p and r lie below a.
  ∨-absorb₃ : ∀ {a p q r} → p ≤ a → r ≤ a → a ∨ ((p ∨ q) ∨ r) ≈ a ∨ q
  ∨-absorb₃ p≤a r≤a = ≤-antisym
    (∨-least ∨-upperˡ (∨-least (∨-least (≤-trans p≤a ∨-upperˡ) ∨-upperʳ) (≤-trans r≤a ∨-upperˡ)))
    (∨-least ∨-upperˡ (≤-trans ∨-upperʳ (≤-trans ∨-upperˡ ∨-upperʳ)))

  -- u ∧ (v ∧ w) ≈ u ∧ v when u lies below w.
  ∧-absorb₃ : ∀ {u v w} → u ≤ w → u ∧ (v ∧ w) ≈ u ∧ v
  ∧-absorb₃ u≤w = ≤-antisym
    (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ ∧-lowerˡ))
    (∧-greatest ∧-lowerˡ (∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ u≤w)))
```

#### Consequences of neutrality

Let `a` be neutral.  Grätzer's computation begins with a special case of
distributivity: for `x ≥ a`, `a ∨ (x ∧ y) ≈ x ∧ (a ∨ y)`
(`neutral-above`{.AgdaFunction}).  Its left side is the left side of the
median identity at `a`, `x`, `y`, since `a ∧ x ≈ a` and `y ∧ a ≤ a` is absorbed;
its right side is the right side of the identity, since `a ∨ x ≈ x` and
`x ∧ (x ∨ y) ≈ x`.

Distributivity (`neutral-∨-distr`{.AgdaFunction}) follows: `a ∨ (x ∧ y)` is
`a` joined with the left side of the identity, since `a ∧ x` and `y ∧ a` lie
below `a`; so it is `a ∨ ((a ∨ x) ∧ ((x ∨ y) ∧ (y ∨ a)))`, and two applications
of `neutral-above`{.AgdaFunction}, at `a ∨ x ≥ a` and then at `y ∨ a ≥ a`,
turn it into `(a ∨ x) ∧ ((y ∨ a) ∧ (a ∨ (x ∨ y)))`, in which the last meetand
is absorbed because `a ∨ x` lies below it.

The median identity is self-dual, so `a` is neutral in the dual lattice too
(`IsNeutral-dual`{.AgdaFunction}), and the dual distributive law
(`neutral-∧-distr`{.AgdaFunction}) is the distributive law of the dual
lattice: the meet and join of `dualLattice 𝑳`{.AgdaFunction} are the join and
meet of `𝑳`{.AgdaBound} by definition, so the statement about the dual is the
dual statement, and no second computation is needed.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-assoc-law ; ∧-comm-law ; ∨-comm-law
                                   ; absorbˡ-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-trans ; ≤-via-∨ ; ∧-lowerˡ ; ∧-lowerʳ ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  -- For x above a, a ∨ (x ∧ y) ≈ x ∧ (a ∨ y).
  neutral-above : ∀ {a} → IsNeutral 𝑳 a → ∀ {x} y → a ≤ x → a ∨ (x ∧ y) ≈ x ∧ (a ∨ y)
  neutral-above {a} n {x} y a≤x = begin
    a ∨ (x ∧ y)                          ≈˘⟨ ∨-absorb-≤ 𝑳 (≤-trans ∧-lowerʳ ∨-upperˡ) ⟩
    (a ∨ (x ∧ y)) ∨ (y ∧ a)              ≈˘⟨ ∨-cong (∨-cong a≤x refl) refl ⟩
    (a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a)          ≈⟨ n x y ⟩
    (a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a)          ≈⟨ ∧-cong (∧-cong (≤-via-∨ a≤x) refl) refl ⟩
    x ∧ (x ∨ y) ∧ (y ∨ a)                ≈⟨ ∧-cong absorbˡ-law ∨-comm-law ⟩
    x ∧ (a ∨ y)                          ∎

  -- A neutral element is distributive.
  neutral-∨-distr : ∀ {a} → IsNeutral 𝑳 a → ∀ x y → a ∨ (x ∧ y) ≈ (a ∨ x) ∧ (a ∨ y)
  neutral-∨-distr {a} n x y = begin
    a ∨ (x ∧ y)                                  ≈˘⟨ ∨-absorb₃ 𝑳 ∧-lowerˡ ∧-lowerʳ ⟩
    a ∨ ((a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a))            ≈⟨ ∨-cong refl (n x y) ⟩
    a ∨ ((a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a))            ≈⟨ ∨-cong refl ∧-assoc-law ⟩
    a ∨ ((a ∨ x) ∧ ((x ∨ y) ∧ (y ∨ a)))          ≈⟨ neutral-above n ((x ∨ y) ∧ (y ∨ a)) ∨-upperˡ ⟩
    (a ∨ x) ∧ (a ∨ ((x ∨ y) ∧ (y ∨ a)))          ≈⟨ ∧-cong refl (∨-cong refl ∧-comm-law) ⟩
    (a ∨ x) ∧ (a ∨ ((y ∨ a) ∧ (x ∨ y)))          ≈⟨ ∧-cong refl (neutral-above n (x ∨ y) ∨-upperʳ) ⟩
    (a ∨ x) ∧ ((y ∨ a) ∧ (a ∨ (x ∨ y)))          ≈⟨ ∧-absorb₃ 𝑳 (∨-least ∨-upperˡ (≤-trans ∨-upperˡ ∨-upperʳ)) ⟩
    (a ∨ x) ∧ (y ∨ a)                            ≈⟨ ∧-cong refl ∨-comm-law ⟩
    (a ∨ x) ∧ (a ∨ y)                            ∎

  -- Neutrality is self-dual.
  IsNeutral-dual : ∀ {a} → IsNeutral 𝑳 a → IsNeutral (dualLattice 𝑳) a
  IsNeutral-dual n x y = sym (n x y)
```

Cancellation (`neutral-cancel`{.AgdaFunction}) is Grätzer's last step.  Suppose
`a ∧ x ≈ a ∧ y` and `a ∨ x ≈ a ∨ y`.  Then `x` lies below each of `a ∨ x`,
`x ∨ y` and `y ∨ a`, the last because `y ∨ a ≈ a ∨ x`; so `x` is its meet with
the right side of the median identity, which is the left side
`(a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a)`.  In it `y ∧ a ≈ a ∧ x` is absorbed, and
`(a ∧ x) ∨ (x ∧ y)` lies below `x`, so `x ≈ (a ∧ x) ∨ (x ∧ y)`
(`neutral-cancel-half`{.AgdaFunction}).  The same with `x` and `y` exchanged
gives `y ≈ (a ∧ y) ∨ (y ∧ x)`, and the two right sides are equal.

```agda
  -- Under the two hypotheses of cancellation, x ≈ (a ∧ x) ∨ (x ∧ y).
  neutral-cancel-half : ∀ {a} → IsNeutral 𝑳 a → ∀ {x y}
    → a ∧ x ≈ a ∧ y → a ∨ x ≈ a ∨ y → x ≈ (a ∧ x) ∨ (x ∧ y)
  neutral-cancel-half {a} n {x} {y} ∧≈ ∨≈ = begin
    x                                            ≈˘⟨ x≤median ⟩
    x ∧ ((a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a))            ≈˘⟨ ∧-cong refl (n x y) ⟩
    x ∧ ((a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a))            ≈⟨ ∧-cong refl (∨-cong refl (trans ∧-comm-law (sym ∧≈))) ⟩
    x ∧ ((a ∧ x) ∨ (x ∧ y) ∨ (a ∧ x))            ≈⟨ ∧-cong refl (∨-absorb-≤ 𝑳 ∨-upperˡ) ⟩
    x ∧ ((a ∧ x) ∨ (x ∧ y))                      ≈⟨ ∧-absorb-≤ 𝑳 (∨-least ∧-lowerʳ ∧-lowerˡ) ⟩
    (a ∧ x) ∨ (x ∧ y)                            ∎
    where
    open Lattice-Order 𝑳 using ( ∧-greatest ; ≤-respʳ-≈ )

    x≤y∨a : x ≤ y ∨ a
    x≤y∨a = ≤-respʳ-≈ (trans ∨≈ ∨-comm-law) ∨-upperʳ

    x≤median : x ∧ ((a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a)) ≈ x
    x≤median = ∧-greatest (∧-greatest ∨-upperʳ ∨-upperˡ) x≤y∨a

  -- A neutral element cancels: equal meets and equal joins with it force equality.
  neutral-cancel : ∀ {a} → IsNeutral 𝑳 a → ∀ {x y} → a ∧ x ≈ a ∧ y → a ∨ x ≈ a ∨ y → x ≈ y
  neutral-cancel n {x} {y} ∧≈ ∨≈ = begin
    x                    ≈⟨ neutral-cancel-half n ∧≈ ∨≈ ⟩
    (_ ∧ x) ∨ (x ∧ y)    ≈⟨ ∨-cong ∧≈ ∧-comm-law ⟩
    (_ ∧ y) ∨ (y ∧ x)    ≈˘⟨ neutral-cancel-half n (sym ∧≈) (sym ∨≈) ⟩
    y                    ∎
```

With the block closed, the dual distributive law is the distributive law of
the dual lattice.

```agda
-- A neutral element is dually distributive: the distributive law of the dual lattice.
neutral-∧-distr : (𝑳 : Lattice α ρ) → ∀ {a} → IsNeutral 𝑳 a → ∀ x y
  → let open Lattice-Op 𝑳 ; open Setoid 𝔻[ proj₁ 𝑳 ] in a ∧ (x ∨ y) ≈ (a ∧ x) ∨ (a ∧ y)
neutral-∧-distr 𝑳 n = neutral-∨-distr (dualLattice 𝑳) (IsNeutral-dual 𝑳 n)
```

#### The bounds

A bottom `b` is neutral: with `b ∧ x ≈ b` and `b ∨ x ≈ x`, both sides of the
median identity at `b`, `x`, `y` are `x ∧ y`.  A top is neutral dually, through
the dual lattice again, whose bottoms are the tops of `𝑳`{.AgdaBound}
(`≤ᵈ-unflip`{.AgdaFunction} of [Lattices.Dual][]).  A top
and a bottom are complements of each other, so both are central in a bounded
lattice.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law ; absorbˡ-law )
  open Lattice-Order 𝑳       using ( IsBottom ; IsTop ; ≤-trans ; ≤-via-∨ ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest
                                   ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  -- A bottom is neutral.
  bottom-neutral : ∀ {b} → IsBottom b → IsNeutral 𝑳 b
  bottom-neutral {b} b-bottom x y = begin
    (b ∧ x) ∨ (x ∧ y) ∨ (y ∧ b)    ≈⟨ ∨-cong (∨-cong (b-bottom x) refl) (trans ∧-comm-law (b-bottom y)) ⟩
    (b ∨ (x ∧ y)) ∨ b              ≈⟨ ∨-cong (≤-via-∨ (b-bottom (x ∧ y))) refl ⟩
    (x ∧ y) ∨ b                    ≈⟨ ∨-absorb-≤ 𝑳 (b-bottom (x ∧ y)) ⟩
    x ∧ y                          ≈˘⟨ ∧-cong absorbˡ-law refl ⟩
    (x ∧ (x ∨ y)) ∧ y              ≈˘⟨ ∧-cong (∧-cong (≤-via-∨ (b-bottom x)) refl) (∨-absorb-≤ 𝑳 (b-bottom y)) ⟩
    (b ∨ x) ∧ (x ∨ y) ∧ (y ∨ b)    ∎

  -- A top and a bottom are complements of each other.
  top-bottom-complements : ∀ {t b} → IsTop t → IsBottom b → AreComplements 𝑳 t b
  top-bottom-complements t-top b-bottom = (λ x → ≤-trans ∧-lowerʳ (b-bottom x)) , (λ x → ≤-trans (t-top x) ∨-upperˡ)

  bottom-top-complements : ∀ {b t} → IsBottom b → IsTop t → AreComplements 𝑳 b t
  bottom-top-complements b-bottom t-top = (λ x → ≤-trans ∧-lowerˡ (b-bottom x)) , (λ x → ≤-trans (t-top x) ∨-upperʳ)

-- A top is neutral: a bottom of the dual lattice.
top-neutral : (𝑳 : Lattice α ρ) → ∀ {t} → Lattice-Order.IsTop 𝑳 t → IsNeutral 𝑳 t
top-neutral 𝑳 t-top x y = Setoid.sym 𝔻[ proj₁ 𝑳 ] (bottom-neutral (dualLattice 𝑳) (λ z → ≤ᵈ-unflip (t-top z)) x y)
  where open LatticeDual 𝑳 using ( ≤ᵈ-unflip )
```

#### Complements against given bounds

When `⊥` is a bottom and `⊤` a top, `a'` is a complement of `a` exactly when
`a ∧ a' ≈ ⊥` and `a ∨ a' ≈ ⊤`, by the uniqueness of bottoms and tops
(`bot-unique`{.AgdaFunction}, `top-unique`{.AgdaFunction} of
[Classical.Properties.Lattice][]).  And a central element that is a bottom
equals `⊥`; one that is a top equals `⊤`.

```agda
module _ (𝑳 : Lattice α ρ) {⊥ ⊤ : 𝕌[ proj₁ 𝑳 ]}
         (⊥-bottom : Lattice-Order.IsBottom 𝑳 ⊥) (⊤-top : Lattice-Order.IsTop 𝑳 ⊤) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( IsBottom ; IsTop ; ≤-respˡ-≈ ; ≤-respʳ-≈ ; bot-unique ; top-unique )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; sym )

  complements-from-bounds : ∀ {a a'} → a ∧ a' ≈ ⊥ → a ∨ a' ≈ ⊤ → AreComplements 𝑳 a a'
  complements-from-bounds ∧≈⊥ ∨≈⊤ = (λ x → ≤-respˡ-≈ (sym ∧≈⊥) (⊥-bottom x)) , (λ x → ≤-respʳ-≈ (sym ∨≈⊤) (⊤-top x))

  complements-∧ : ∀ {a a'} → AreComplements 𝑳 a a' → a ∧ a' ≈ ⊥
  complements-∧ (∧-bottom , _) = bot-unique ∧-bottom ⊥-bottom

  complements-∨ : ∀ {a a'} → AreComplements 𝑳 a a' → a ∨ a' ≈ ⊤
  complements-∨ (_ , ∨-top) = top-unique ∨-top ⊤-top

  bottom-is-⊥ : ∀ {a} → IsBottom a → a ≈ ⊥
  bottom-is-⊥ a-bottom = bot-unique a-bottom ⊥-bottom

  top-is-⊤ : ∀ {a} → IsTop a → a ≈ ⊤
  top-is-⊤ a-top = top-unique a-top ⊤-top
```

#### Respecting equality

Each notion respects `≈` in each of its arguments, by the congruence of the
operations and the order; the respect lemmas are what the sweeps below need to
carry a verdict from the enumerated elements to all elements.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong )
  open Lattice-Order 𝑳       using ( IsBottom ; IsTop ; ≤-respˡ-≈ ; ≤-respʳ-≈ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )

  MedianAt-resp : ∀ {a a' x x' y y'} → a ≈ a' → x ≈ x' → y ≈ y'
    → MedianAt 𝑳 a x y → MedianAt 𝑳 a' x' y'
  MedianAt-resp a≈ x≈ y≈ e =
    trans (sym (∨-cong (∨-cong (∧-cong a≈ x≈) (∧-cong x≈ y≈)) (∧-cong y≈ a≈)))
          (trans e (∧-cong (∧-cong (∨-cong a≈ x≈) (∨-cong x≈ y≈)) (∨-cong y≈ a≈)))

  IsNeutral-resp : ∀ {a a'} → a ≈ a' → IsNeutral 𝑳 a → IsNeutral 𝑳 a'
  IsNeutral-resp a≈ n x y = MedianAt-resp a≈ refl refl (n x y)

  IsBottom-resp : ∀ {b b'} → b ≈ b' → IsBottom b → IsBottom b'
  IsBottom-resp b≈ b-bottom x = ≤-respˡ-≈ b≈ (b-bottom x)

  IsTop-resp : ∀ {t t'} → t ≈ t' → IsTop t → IsTop t'
  IsTop-resp t≈ t-top x = ≤-respʳ-≈ t≈ (t-top x)

  AreComplements-resp : ∀ {a a' c c'} → a ≈ a' → c ≈ c' → AreComplements 𝑳 a c → AreComplements 𝑳 a' c'
  AreComplements-resp a≈ c≈ (∧-bottom , ∨-top) =
    IsBottom-resp (∧-cong a≈ c≈) ∧-bottom , IsTop-resp (∨-cong a≈ c≈) ∨-top

  IsComplemented-resp : ∀ {a a'} → a ≈ a' → IsComplemented 𝑳 a → IsComplemented 𝑳 a'
  IsComplemented-resp a≈ (c , comp) = c , AreComplements-resp a≈ refl comp

  IsCentral-resp : ∀ {a a'} → a ≈ a' → IsCentral 𝑳 a → IsCentral 𝑳 a'
  IsCentral-resp a≈ (n , comp) = IsNeutral-resp a≈ n , IsComplemented-resp a≈ comp
```

#### Isomorphic lattices

An isomorphism `φ : 𝑲 ≅ 𝑳` carries a bottom, a top, a neutral element, a pair
of complements and a central element of `𝑲`{.AgdaBound} to one of
`𝑳`{.AgdaBound}, in the direction of the `-I-invar` lemmas of
[Lattices.Semidistributive][].  For the order, `f b ≤ x` because
`b ≤ g x` in `𝑲`{.AgdaBound}, `f` is monotone, and `f (g x) ≈ x`.  For the
median identity at `f a`, `x`, `y`, the identity at `a`, `g x`, `g y` in
`𝑲`{.AgdaBound} is moved along `f`, which commutes with the operations
(`hom-preserves-∧`{.AgdaFunction}, `hom-preserves-∨`{.AgdaFunction}), and
`f (g x) ≈ x` again.  Nontriviality is carried by injectivity, and direct
indecomposability by applying both directions of the isomorphism: a central
element of `𝑳`{.AgdaBound} comes from one of `𝑲`{.AgdaBound}, which is a
bound there, so its image is a bound in `𝑳`{.AgdaBound}.

```agda
module _ (𝑲 : Lattice α ρ) (𝑳 : Lattice β σ) (φ : proj₁ 𝑲 ≅ proj₁ 𝑳) where
  open Lattice-Op 𝑲            using () renaming ( _∧_ to _∧ᴷ_ ; _∨_ to _∨ᴷ_ )
  open Lattice-Order 𝑲         using () renaming ( IsBottom to IsBottomᴷ ; IsTop to IsTopᴷ )
  open Lattice-Op 𝑳            using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong )
  open Lattice-Order 𝑳         using ( IsBottom ; IsTop ; ≤-respˡ-≈ ; ≤-respʳ-≈ )
  open Setoid 𝔻[ proj₁ 𝑳 ]     using ( _≈_ ; refl ; sym ; trans )

  private
    h : hom (proj₁ 𝑲) (proj₁ 𝑳)
    h = to φ

    f : 𝕌[ proj₁ 𝑲 ] → 𝕌[ proj₁ 𝑳 ]
    f = proj₁ h ⟨$⟩_

    g : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑲 ]
    g = proj₁ (from φ) ⟨$⟩_

    -- f moves past a join of three and a meet of three.
    f-∨₃ : ∀ p q r → f ((p ∨ᴷ q) ∨ᴷ r) ≈ (f p ∨ f q) ∨ f r
    f-∨₃ p q r = trans (hom-preserves-∨ 𝑲 𝑳 h (p ∨ᴷ q) r) (∨-cong (hom-preserves-∨ 𝑲 𝑳 h p q) refl)

    f-∧₃ : ∀ p q r → f ((p ∧ᴷ q) ∧ᴷ r) ≈ (f p ∧ f q) ∧ f r
    f-∧₃ p q r = trans (hom-preserves-∧ 𝑲 𝑳 h (p ∧ᴷ q) r) (∧-cong (hom-preserves-∧ 𝑲 𝑳 h p q) refl)

  IsBottom-I-invar : ∀ {b} → IsBottomᴷ b → IsBottom (f b)
  IsBottom-I-invar b-bottom x = ≤-respʳ-≈ (to∼from φ x) (hom-preserves-≤ 𝑲 𝑳 h (b-bottom (g x)))

  IsTop-I-invar : ∀ {t} → IsTopᴷ t → IsTop (f t)
  IsTop-I-invar t-top x = ≤-respˡ-≈ (to∼from φ x) (hom-preserves-≤ 𝑲 𝑳 h (t-top (g x)))

  MedianAt-I-invar : ∀ {a x y} → MedianAt 𝑲 a x y → MedianAt 𝑳 (f a) (f x) (f y)
  MedianAt-I-invar {a} {x} {y} e = begin
    (f a ∧ f x) ∨ (f x ∧ f y) ∨ (f y ∧ f a)    ≈˘⟨ ∨-cong (∨-cong (hom-preserves-∧ 𝑲 𝑳 h a x) (hom-preserves-∧ 𝑲 𝑳 h x y))
                                                          (hom-preserves-∧ 𝑲 𝑳 h y a) ⟩
    (f (a ∧ᴷ x) ∨ f (x ∧ᴷ y)) ∨ f (y ∧ᴷ a)      ≈˘⟨ f-∨₃ (a ∧ᴷ x) (x ∧ᴷ y) (y ∧ᴷ a) ⟩
    f ((a ∧ᴷ x) ∨ᴷ (x ∧ᴷ y) ∨ᴷ (y ∧ᴷ a))        ≈⟨ cong (proj₁ h) e ⟩
    f ((a ∨ᴷ x) ∧ᴷ (x ∨ᴷ y) ∧ᴷ (y ∨ᴷ a))        ≈⟨ f-∧₃ (a ∨ᴷ x) (x ∨ᴷ y) (y ∨ᴷ a) ⟩
    (f (a ∨ᴷ x) ∧ f (x ∨ᴷ y)) ∧ f (y ∨ᴷ a)      ≈⟨ ∧-cong (∧-cong (hom-preserves-∨ 𝑲 𝑳 h a x) (hom-preserves-∨ 𝑲 𝑳 h x y))
                                                         (hom-preserves-∨ 𝑲 𝑳 h y a) ⟩
    (f a ∨ f x) ∧ (f x ∨ f y) ∧ (f y ∨ f a)    ∎
    where open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  IsNeutral-I-invar : ∀ {a} → IsNeutral 𝑲 a → IsNeutral 𝑳 (f a)
  IsNeutral-I-invar n x y =
    MedianAt-resp 𝑳 refl (to∼from φ x) (to∼from φ y) (MedianAt-I-invar (n (g x) (g y)))

  AreComplements-I-invar : ∀ {a a'} → AreComplements 𝑲 a a' → AreComplements 𝑳 (f a) (f a')
  AreComplements-I-invar {a} {a'} (∧-bottom , ∨-top) =
      IsBottom-resp 𝑳 (hom-preserves-∧ 𝑲 𝑳 h a a') (IsBottom-I-invar ∧-bottom)
    , IsTop-resp 𝑳 (hom-preserves-∨ 𝑲 𝑳 h a a') (IsTop-I-invar ∨-top)

  IsComplemented-I-invar : ∀ {a} → IsComplemented 𝑲 a → IsComplemented 𝑳 (f a)
  IsComplemented-I-invar (a' , comp) = f a' , AreComplements-I-invar comp

  IsCentral-I-invar : ∀ {a} → IsCentral 𝑲 a → IsCentral 𝑳 (f a)
  IsCentral-I-invar (n , comp) = IsNeutral-I-invar n , IsComplemented-I-invar comp

  Nontrivial-I-invar : Nontrivial (proj₁ 𝑲) → Nontrivial (proj₁ 𝑳)
  Nontrivial-I-invar (a , b , a≉b) = f a , f b , λ e → a≉b (≅toInjective φ e)
```

The direction that moves a central element of `𝑳`{.AgdaBound} back to
`𝑲`{.AgdaBound} is the same lemma at the inverse isomorphism.

```agda
module _ (𝑲 : Lattice α ρ) (𝑳 : Lattice β σ) (φ : proj₁ 𝑲 ≅ proj₁ 𝑳) where
  private
    g : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑲 ]
    g = proj₁ (from φ) ⟨$⟩_

  IsDirectlyIndecomposable-I-invar : IsDirectlyIndecomposable 𝑲 → IsDirectlyIndecomposable 𝑳
  IsDirectlyIndecomposable-I-invar (nt , bounds) = Nontrivial-I-invar 𝑲 𝑳 φ nt , λ a central →
    ⊎-map (IsBottom-resp 𝑳 (to∼from φ a) ∘ IsBottom-I-invar 𝑲 𝑳 φ)
          (IsTop-resp 𝑳 (to∼from φ a) ∘ IsTop-I-invar 𝑲 𝑳 φ)
          (bounds (g a) (IsCentral-I-invar 𝑳 𝑲 (≅-sym φ) central))
```

#### Products

In a product `𝑳₁ ×ˡ 𝑳₂` of [Lattices.Product][] the
operations, the equality and the order are componentwise by definition, so a
pair of neutral elements is neutral, a pair of bottoms is a bottom, a pair of
tops a top, and complements pair with complements.  In a product of two
bounded lattices the pair `(⊤₁ , ⊥₂)` is therefore central, with complement
`(⊥₁ , ⊤₂)` (`×ˡ-central`{.AgdaFunction}); this is the element the
decomposition theorem transports.

```agda
module _ (𝑳₁ : Lattice α ρ) (𝑳₂ : Lattice β σ) where
  open Lattice-Order 𝑳₁  using () renaming ( IsBottom to IsBottom₁ ; IsTop to IsTop₁ )
  open Lattice-Order 𝑳₂  using () renaming ( IsBottom to IsBottom₂ ; IsTop to IsTop₂ )
  open Lattice-Order (𝑳₁ ×ˡ 𝑳₂)  using ( IsBottom ; IsTop )

  ×ˡ-neutral : ∀ {a₁ a₂} → IsNeutral 𝑳₁ a₁ → IsNeutral 𝑳₂ a₂ → IsNeutral (𝑳₁ ×ˡ 𝑳₂) (a₁ , a₂)
  ×ˡ-neutral n₁ n₂ x y = n₁ (proj₁ x) (proj₁ y) , n₂ (proj₂ x) (proj₂ y)

  ×ˡ-bottom : ∀ {b₁ b₂} → IsBottom₁ b₁ → IsBottom₂ b₂ → IsBottom (b₁ , b₂)
  ×ˡ-bottom b₁ b₂ x = b₁ (proj₁ x) , b₂ (proj₂ x)

  ×ˡ-top : ∀ {t₁ t₂} → IsTop₁ t₁ → IsTop₂ t₂ → IsTop (t₁ , t₂)
  ×ˡ-top t₁ t₂ x = t₁ (proj₁ x) , t₂ (proj₂ x)

  ×ˡ-complements : ∀ {a₁ a₂ c₁ c₂} → AreComplements 𝑳₁ a₁ c₁ → AreComplements 𝑳₂ a₂ c₂
    → AreComplements (𝑳₁ ×ˡ 𝑳₂) (a₁ , a₂) (c₁ , c₂)
  ×ˡ-complements (∧₁ , ∨₁) (∧₂ , ∨₂) = ×ˡ-bottom ∧₁ ∧₂ , ×ˡ-top ∨₁ ∨₂

  -- (⊤₁ , ⊥₂) is central in a product of bounded lattices, with complement (⊥₁ , ⊤₂).
  ×ˡ-central : ∀ {⊥₁ ⊤₁ ⊥₂ ⊤₂} → IsBottom₁ ⊥₁ → IsTop₁ ⊤₁ → IsBottom₂ ⊥₂ → IsTop₂ ⊤₂
    → IsCentral (𝑳₁ ×ˡ 𝑳₂) (⊤₁ , ⊥₂)
  ×ˡ-central ⊥₁ ⊤₁ ⊥₂ ⊤₂ =
      ×ˡ-neutral (top-neutral 𝑳₁ ⊤₁) (bottom-neutral 𝑳₂ ⊥₂)
    , (_ , _) , ×ˡ-complements (top-bottom-complements 𝑳₁ ⊤₁ ⊥₁) (bottom-top-complements 𝑳₂ ⊥₂ ⊤₂)
```

#### Deciding the notions in a finite lattice

In a finite lattice with decidable equality every notion above is decidable by
a sweep over the enumeration of a `FiniteAlgebra`{.AgdaRecord} of
[Setoid.Algebras.Finite][], as the conditions of [Lattices.Semidistributive][]
are: `IsBottom b`{.AgdaFunction} and `IsTop t`{.AgdaFunction} by one sweep
(`all¹?`{.AgdaFunction}, the one-variable case of the library's
`all²?`{.AgdaFunction}), the median identity at `a` by a sweep over pairs
(`all²?`{.AgdaFunction}), the existence of a complement by a sweep over
candidates (`exists?`{.AgdaFunction}), each candidate costing two more sweeps,
and direct indecomposability by `nontrivial?`{.AgdaFunction} of
[Setoid.Decompositions.Finite][] together with a sweep over the candidates for
a central element.  A lattice with `n` enumerated elements costs `n³`
instances of the median identity and `2n³` order comparisons for the
complements, each a few evaluations of the operations.

A negative verdict of `isDirectlyIndecomposable?`{.AgdaFunction} on a
nontrivial lattice says that some element is central and neither a bottom nor
a top, but names none; `properCentral`{.AgdaFunction} finds one, as
`modularFailure`{.AgdaFunction} of [Lattices.Modular][] finds a failing triple:
the refutation of the sweep is turned into an enumerated element at which the
instance fails (`¬∀⟶∃¬`{.AgdaFunction} of the standard library), and the
decidability of the instance's parts reads the failure as the three facts.

```agda
private
  -- A refuted implication with a decidable antecedent: the antecedent holds.
  antecedent : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {D : Type ℓ₂} → Dec A → ¬ (A → D) → A
  antecedent (yes a)   _   = a
  antecedent (no ¬a)  ¬h  = ⊥-elim (¬h λ a → ⊥-elim (¬a a))

module _ (𝑳 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
  open FiniteAlgebra 𝑭      using ( _≟_ ; card ; enum ; enum-sur )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳      using ( _≤_ ; IsBottom ; IsTop ; ≤-respˡ-≈ ; ≤-respʳ-≈ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; refl ; sym )

  private
    U : Type α
    U = 𝕌[ proj₁ 𝑳 ]

    infix 4 _≤?_
    _≤?_ : ∀ x y → Dec (x ≤ y)
    x ≤? y = (x ∧ y) ≟ x

    -- A sweep over one variable, in the shape of all²? of Setoid.Algebras.Finite.
    enum-all¹ : ∀ {ℓ} (P : U → Type ℓ) → (∀ {a a'} → a ≈ a' → P a → P a') → (∀ i → P (enum i)) → ∀ a → P a
    enum-all¹ P resp h a = resp (proj₂ (enum-sur a)) (h (proj₁ (enum-sur a)))

    all¹? : ∀ {ℓ} (P : U → Type ℓ) → (∀ {a a'} → a ≈ a' → P a → P a') → (∀ a → Dec (P a)) → Dec (∀ a → P a)
    all¹? P resp P? = map′ (enum-all¹ P resp) (λ h i → h (enum i)) (all? λ i → P? (enum i))

  isBottom? : ∀ b → Dec (IsBottom b)
  isBottom? b = all¹? (b ≤_) ≤-respʳ-≈ (b ≤?_)

  isTop? : ∀ t → Dec (IsTop t)
  isTop? t = all¹? (_≤ t) ≤-respˡ-≈ (_≤? t)

  isNeutral? : ∀ a → Dec (IsNeutral 𝑳 a)
  isNeutral? a = all²? 𝑭 (MedianAt 𝑳 a) (MedianAt-resp 𝑳 refl)
                   λ x y → ((a ∧ x) ∨ (x ∧ y) ∨ (y ∧ a)) ≟ ((a ∨ x) ∧ (x ∨ y) ∧ (y ∨ a))

  areComplements? : ∀ a a' → Dec (AreComplements 𝑳 a a')
  areComplements? a a' = isBottom? (a ∧ a') ×-dec isTop? (a ∨ a')

  isComplemented? : ∀ a → Dec (IsComplemented 𝑳 a)
  isComplemented? a = exists? 𝑭 (AreComplements 𝑳 a) (AreComplements-resp 𝑳 refl) (areComplements? a)

  isCentral? : ∀ a → Dec (IsCentral 𝑳 a)
  isCentral? a = isNeutral? a ×-dec isComplemented? a

  private
    -- The instance swept for indecomposability: a central element is a bound.
    Bound-at : U → Type (α ⊔ ρ)
    Bound-at a = IsCentral 𝑳 a → IsBottom a ⊎ IsTop a

    Bound-resp : ∀ {a a'} → a ≈ a' → Bound-at a → Bound-at a'
    Bound-resp a≈ h central = ⊎-map (IsBottom-resp 𝑳 a≈) (IsTop-resp 𝑳 a≈) (h (IsCentral-resp 𝑳 (sym a≈) central))

    bound-at? : ∀ a → Dec (Bound-at a)
    bound-at? a = isCentral? a →-dec (isBottom? a ⊎-dec isTop? a)

  isDirectlyIndecomposable? : Dec (IsDirectlyIndecomposable 𝑳)
  isDirectlyIndecomposable? = nontrivial? 𝑭 ×-dec all¹? Bound-at Bound-resp bound-at?

  -- A nontrivial lattice that is not directly indecomposable has a proper central element.
  properCentral : Nontrivial (proj₁ 𝑳) → ¬ IsDirectlyIndecomposable 𝑳 → ProperCentral 𝑳
  properCentral nt ¬ind = enum i , central , not-bottom , not-top
    where
    ¬all : ¬ (∀ i → Bound-at (enum i))
    ¬all h = ¬ind (nt , enum-all¹ Bound-at Bound-resp h)

    failing : ∃[ i ] ¬ Bound-at (enum i)
    failing = ¬∀⟶∃¬ card _ (λ i → bound-at? (enum i)) ¬all

    i : Fin card
    i = proj₁ failing

    -- From the failure of the implication: the element is central, and neither bound.
    central : IsCentral 𝑳 (enum i)
    central = antecedent (isCentral? (enum i)) (proj₂ failing)

    not-bottom : ¬ IsBottom (enum i)
    not-bottom b = proj₂ failing λ _ → inj₁ b

    not-top : ¬ IsTop (enum i)
    not-top t = proj₂ failing λ _ → inj₂ t
```

--------------------------------------

[Lattices.Central]: Lattices.Central.html
[Lattices.Central.Decomposition]: Lattices.Central.Decomposition.html
[Lattices.Semidistributive]: Lattices.Semidistributive.html
[Lattices.Modular]: Lattices.Modular.html
[Classical.Properties.Lattice]: Classical.Properties.Lattice.html
[Lattices.Dual]: Lattices.Dual.html
[Lattices.Product]: Lattices.Product.html
[Setoid.Algebras.Finite]: Setoid.Algebras.Finite.html
[Setoid.Decompositions.Finite]: Setoid.Decompositions.Finite.html
[Birkhoff (1948)]: https://bookstore.ams.org/coll-25
[Grätzer (1998)]: https://doi.org/10.1007/978-3-0348-7633-9
