---
layout: default
file: "src/Lattices/Bounded/Homomorphism.lagda.md"
title: "Lattices.Bounded.Homomorphism module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Bounded homomorphisms

This is the [Lattices.Bounded.Homomorphism][] module of the [agda-lattices][] library.

A lattice homomorphism `h : K → L` is *lower bounded* if for every `a ∈ L` the
set `{w ∈ K : a ≤ h w}` is empty or has a least element, written `β a`; it is
*upper bounded* if dually every `{w ∈ K : h w ≤ a}` is empty or has a greatest
element `α a`; and it is *bounded* if it is both ([Freese, Ježek, and Nation
(1995)][], Section II.1, p. 27, after McKenzie; Kostinsky, "Projective lattices
and bounded homomorphisms", *Pacific J. Math.* 40 (1972), Definition 2.3).  The
idea is the crucial one for the structure of free lattices: a finitely generated
lattice is a sublattice of a free lattice exactly when some epimorphism from a
free lattice onto it is bounded and it satisfies Whitman's condition (W), which
is Kostinsky's theorem ([Lattices.Kostinsky][]).

This module states the three notions as *data*: `LowerBounded h`{.AgdaRecord}
is a map `β` with the two laws that make `β a` the least element above `a`,
`a ≤ h (β a)` and `a ≤ h w → β a ≤ w`, and `UpperBounded h`{.AgdaRecord} is the
dual.  The book allows the set `{w : a ≤ h w}` to be empty; the records do not,
so they say "lower bounded" for the homomorphisms under which every element of
`L` lies below some value, which every epimorphism is, and the epimorphisms are
what the theorems are about.  (Kostinsky's Note 2.4 observes that the notions
are defined with respect to the whole codomain, not the range; for an
epimorphism the two agree.)  From the two laws alone, `β` is monotone and
preserves joins, `α` is monotone and preserves meets, and for an epimorphism
each picks a preimage (`β-section`{.AgdaFunction},
`α-section`{.AgdaFunction}), so that `β a ≤ α a`.  Bounded homomorphisms
compose, with `β` and `α` composing the other way round (Theorem 2.1).

A finitely generated lattice is *lower bounded* when some epimorphism onto it
from a finitely generated free lattice is lower bounded, and *upper bounded* and
*bounded* likewise (the book, p. 34, condition (1) of Theorem 2.13).  The sets
`D_k(L)` through which the book defines the same classes (its condition (3),
`D(L) = L`) are in [Lattices.Bounded.Covers][], and the two definitions are
compared there and in [Lattices.Bounded.Preimage][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Bounded.Homomorphism where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms.Basic          using ( hom )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Universal    using ( FL ; FL-extend ; FL-extend-hom )
open import Lattices.Semidistributive  using ( hom-preserves-∧ ; hom-preserves-∨ ; hom-preserves-≤ )

open Func using () renaming ( to to _⟨$⟩_ )

private variable αᴷ ρᴷ αᴸ ρᴸ αᴹ ρᴹ : Level
```
-->

#### The definitions

Fix lattices `𝑲`{.AgdaBound} and `𝑳`{.AgdaBound} and a homomorphism
`h`{.AgdaBound} of their underlying algebras, with `f` its underlying map; the
orders are the meet orders of [Classical.Properties.Lattice][].  The field
names follow the book: `β` is its `β_h`, `α` its `α_h`.

```agda
module _ (𝑲 : Lattice αᴷ ρᴷ) (𝑳 : Lattice αᴸ ρᴸ) (h : hom (proj₁ 𝑲) (proj₁ 𝑳)) where
  open Lattice-Order 𝑲  using () renaming ( _≤_ to _≤ᴷ_ )
  open Lattice-Order 𝑳  using ( _≤_ )

  private
    f : 𝕌[ proj₁ 𝑲 ] → 𝕌[ proj₁ 𝑳 ]
    f = proj₁ h ⟨$⟩_

  -- h is lower bounded: β a is the least w with a ≤ h w.
  record LowerBounded : Type (αᴷ ⊔ ρᴷ ⊔ αᴸ ⊔ ρᴸ) where
    field
      β        : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑲 ]
      β-above  : ∀ a → a ≤ f (β a)
      β-least  : ∀ a w → a ≤ f w → β a ≤ᴷ w

  -- h is upper bounded: α a is the greatest w with h w ≤ a.
  record UpperBounded : Type (αᴷ ⊔ ρᴷ ⊔ αᴸ ⊔ ρᴸ) where
    field
      α           : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑲 ]
      α-below     : ∀ a → f (α a) ≤ a
      α-greatest  : ∀ a w → f w ≤ a → w ≤ᴷ α a

  -- h is bounded: lower and upper bounded.
  Bounded : Type (αᴷ ⊔ ρᴷ ⊔ αᴸ ⊔ ρᴸ)
  Bounded = LowerBounded × UpperBounded
```

#### What the laws give

The map `β` is monotone, since `a ≤ a' ≤ h (β a')`; it therefore respects the
equality of `𝑳`{.AgdaBound}, and it is a setoid map
(`β-func`{.AgdaFunction}).  It preserves joins (`β-∨`{.AgdaFunction}): the join
`β a ∨ β a'` lies above `a ∨ a'` under `h`, so `β (a ∨ a')` lies below it, and
monotonicity gives the other inequality.  When `h` is onto, `h (β a)` is `a`
itself (`β-section`{.AgdaFunction}): `a` is some `h w`, so `β a ≤ w` and
`h (β a) ≤ h w = a`.  This is the book's remark that for an epimorphism, lower
boundedness says that each preimage set has a least element, and that `β` is a
join homomorphism from `L` into `K`.

```agda
  module LowerBoundedProperties (lb : LowerBounded) where
    open LowerBounded lb public
    open Lattice-Op 𝑲      using () renaming ( _∨_ to _∨ᴷ_ )
    open Lattice-Op 𝑳      using ( _∨_ )
    open Lattice-Order 𝑲   using () renaming ( ≤-antisym to ≤ᴷ-antisym ; ∨-least to ∨ᴷ-least )
    open Lattice-Order 𝑳   using ( ≤-trans ; ≤-reflexive ; ≤-antisym ; ≤-respʳ-≈
                                 ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
    open Setoid 𝔻[ proj₁ 𝑲 ]  using () renaming ( _≈_ to _≈ᴷ_ )
    open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; sym )

    -- β is monotone.
    β-mono : ∀ {a a'} → a ≤ a' → β a ≤ᴷ β a'
    β-mono {a} {a'} a≤a' = β-least a (β a') (≤-trans a≤a' (β-above a'))

    -- β respects the equality of 𝑳.
    β-cong : ∀ {a a'} → a ≈ a' → β a ≈ᴷ β a'
    β-cong e = ≤ᴷ-antisym (β-mono (≤-reflexive e)) (β-mono (≤-reflexive (sym e)))

    -- β as a map of setoids.
    β-func : Func 𝔻[ proj₁ 𝑳 ] 𝔻[ proj₁ 𝑲 ]
    β-func = record { to = β ; cong = β-cong }

    -- β preserves joins.
    β-∨ : ∀ a a' → β (a ∨ a') ≈ᴷ β a ∨ᴷ β a'
    β-∨ a a' = ≤ᴷ-antisym
      (β-least (a ∨ a') (β a ∨ᴷ β a')
        (≤-respʳ-≈ (sym (hom-preserves-∨ 𝑲 𝑳 h (β a) (β a')))
                   (∨-least (≤-trans (β-above a) ∨-upperˡ) (≤-trans (β-above a') ∨-upperʳ))))
      (∨ᴷ-least (β-mono ∨-upperˡ) (β-mono ∨-upperʳ))

    -- For an epimorphism, β a is a preimage of a.
    β-section : IsSurjective (proj₁ h) → ∀ a → f (β a) ≈ a
    β-section onto a with onto {a}
    ... | Image_∋_.eq w a≈fw =
      ≤-antisym (≤-trans (hom-preserves-≤ 𝑲 𝑳 h (β-least a w (≤-reflexive a≈fw)))
                         (≤-reflexive (sym a≈fw)))
                (β-above a)
```

The dual facts hold for `α`: it is monotone, it respects equality, it preserves
meets, and for an epimorphism `h (α a)` is `a` (`α-section`{.AgdaFunction}).

```agda
  module UpperBoundedProperties (ub : UpperBounded) where
    open UpperBounded ub public
    open Lattice-Op 𝑲      using () renaming ( _∧_ to _∧ᴷ_ )
    open Lattice-Op 𝑳      using ( _∧_ )
    open Lattice-Order 𝑲   using () renaming ( ≤-antisym to ≤ᴷ-antisym ; ∧-greatest to ∧ᴷ-greatest )
    open Lattice-Order 𝑳   using ( ≤-trans ; ≤-reflexive ; ≤-antisym ; ≤-respˡ-≈
                                 ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest )
    open Setoid 𝔻[ proj₁ 𝑲 ]  using () renaming ( _≈_ to _≈ᴷ_ )
    open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; sym )

    -- α is monotone.
    α-mono : ∀ {a a'} → a ≤ a' → α a ≤ᴷ α a'
    α-mono {a} {a'} a≤a' = α-greatest a' (α a) (≤-trans (α-below a) a≤a')

    -- α respects the equality of 𝑳.
    α-cong : ∀ {a a'} → a ≈ a' → α a ≈ᴷ α a'
    α-cong e = ≤ᴷ-antisym (α-mono (≤-reflexive e)) (α-mono (≤-reflexive (sym e)))

    -- α as a map of setoids.
    α-func : Func 𝔻[ proj₁ 𝑳 ] 𝔻[ proj₁ 𝑲 ]
    α-func = record { to = α ; cong = α-cong }

    -- α preserves meets.
    α-∧ : ∀ a a' → α (a ∧ a') ≈ᴷ α a ∧ᴷ α a'
    α-∧ a a' = ≤ᴷ-antisym
      (∧ᴷ-greatest (α-mono ∧-lowerˡ) (α-mono ∧-lowerʳ))
      (α-greatest (a ∧ a') (α a ∧ᴷ α a')
        (≤-respˡ-≈ (sym (hom-preserves-∧ 𝑲 𝑳 h (α a) (α a')))
                   (∧-greatest (≤-trans ∧-lowerˡ (α-below a)) (≤-trans ∧-lowerʳ (α-below a')))))

    -- For an epimorphism, α a is a preimage of a.
    α-section : IsSurjective (proj₁ h) → ∀ a → f (α a) ≈ a
    α-section onto a with onto {a}
    ... | Image_∋_.eq w a≈fw =
      ≤-antisym (α-below a)
                (≤-trans (≤-reflexive a≈fw)
                         (hom-preserves-≤ 𝑲 𝑳 h (α-greatest a w (≤-reflexive (sym a≈fw)))))
```

For a bounded epimorphism the two bounds are comparable: `β a ≤ α a`, since
`h (α a)` is `a`, so `α a` is among the elements `β a` is least below.

```agda
  module BoundedProperties (bd : Bounded) where
    open LowerBoundedProperties (proj₁ bd) public
    open UpperBoundedProperties (proj₂ bd) public
    open Lattice-Order 𝑳 using ( ≤-reflexive )
    open Setoid 𝔻[ proj₁ 𝑳 ] using ( sym )

    -- For an epimorphism, the least preimage lies below the greatest.
    β≤α : IsSurjective (proj₁ h) → ∀ a → β a ≤ᴷ α a
    β≤α onto a = β-least a (α a) (≤-reflexive (sym (α-section onto a)))
```

#### Homomorphisms with the same values

Two homomorphisms that agree on every element have the same bounds, since the
laws speak only of the values: a fact used to carry the bounds between a
homomorphism out of a free lattice and the extension of its restriction to the
generators, which agree by the uniqueness half of the universal property.

```agda
module _ (𝑲 : Lattice αᴷ ρᴷ) (𝑳 : Lattice αᴸ ρᴸ) (h h' : hom (proj₁ 𝑲) (proj₁ 𝑳))
         (h≈h' : ∀ w → Setoid._≈_ 𝔻[ proj₁ 𝑳 ] (proj₁ h ⟨$⟩ w) (proj₁ h' ⟨$⟩ w)) where
  open Lattice-Order 𝑳      using ( ≤-respˡ-≈ ; ≤-respʳ-≈ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( sym )

  -- The bounds of h bound h'.
  LowerBounded-resp : LowerBounded 𝑲 𝑳 h → LowerBounded 𝑲 𝑳 h'
  LowerBounded-resp lb = record
    { β        = β
    ; β-above  = λ a → ≤-respʳ-≈ (h≈h' (β a)) (β-above a)
    ; β-least  = λ a w a≤h'w → β-least a w (≤-respʳ-≈ (sym (h≈h' w)) a≤h'w)
    }
    where open LowerBounded lb

  UpperBounded-resp : UpperBounded 𝑲 𝑳 h → UpperBounded 𝑲 𝑳 h'
  UpperBounded-resp ub = record
    { α           = α
    ; α-below     = λ a → ≤-respˡ-≈ (h≈h' (α a)) (α-below a)
    ; α-greatest  = λ a w h'w≤a → α-greatest a w (≤-respˡ-≈ (sym (h≈h' w)) h'w≤a)
    }
    where open UpperBounded ub

  Bounded-resp : Bounded 𝑲 𝑳 h → Bounded 𝑲 𝑳 h'
  Bounded-resp (lb , ub) = LowerBounded-resp lb , UpperBounded-resp ub
```

#### Composition

Bounded homomorphisms compose (the book's Theorem 2.1), with the bounds
composing in the other order: for `f : K → L` and `g : L → M`, the least
preimage under `g ∘ f` of `c ∈ M` is `β_f (β_g c)`, and the greatest is
`α_f (α_g c)`.  `⊙-hom f g`{.AgdaFunction} of [Setoid.Homomorphisms.Properties][]
is "apply `f`, then `g`".

```agda
module _ (𝑲 : Lattice αᴷ ρᴷ) (𝑳 : Lattice αᴸ ρᴸ) (𝑴 : Lattice αᴹ ρᴹ)
         (f : hom (proj₁ 𝑲) (proj₁ 𝑳)) (g : hom (proj₁ 𝑳) (proj₁ 𝑴)) where
  open Lattice-Order 𝑴  using ( ≤-trans )

  -- Theorem 2.1: lower bounded homomorphisms compose.
  ⊙-lowerBounded : LowerBounded 𝑲 𝑳 f → LowerBounded 𝑳 𝑴 g → LowerBounded 𝑲 𝑴 (⊙-hom f g)
  ⊙-lowerBounded lf lg = record
    { β        = λ c → F.β (G.β c)
    ; β-above  = λ c → ≤-trans (G.β-above c) (hom-preserves-≤ 𝑳 𝑴 g (F.β-above (G.β c)))
    ; β-least  = λ c w c≤gfw → F.β-least (G.β c) w (G.β-least c (proj₁ f ⟨$⟩ w) c≤gfw)
    }
    where
    module F = LowerBounded lf
    module G = LowerBounded lg

  -- Theorem 2.1: upper bounded homomorphisms compose.
  ⊙-upperBounded : UpperBounded 𝑲 𝑳 f → UpperBounded 𝑳 𝑴 g → UpperBounded 𝑲 𝑴 (⊙-hom f g)
  ⊙-upperBounded uf ug = record
    { α           = λ c → F.α (G.α c)
    ; α-below     = λ c → ≤-trans (hom-preserves-≤ 𝑳 𝑴 g (F.α-below (G.α c))) (G.α-below c)
    ; α-greatest  = λ c w gfw≤c → F.α-greatest (G.α c) w (G.α-greatest c (proj₁ f ⟨$⟩ w) gfw≤c)
    }
    where
    module F = UpperBounded uf
    module G = UpperBounded ug

  -- Bounded homomorphisms compose.
  ⊙-bounded : Bounded 𝑲 𝑳 f → Bounded 𝑳 𝑴 g → Bounded 𝑲 𝑴 (⊙-hom f g)
  ⊙-bounded (lf , uf) (lg , ug) = ⊙-lowerBounded lf lg , ⊙-upperBounded uf ug
```

#### Bounded lattices

A lattice `𝑳`{.AgdaBound} is *finitely generated* when finitely many of its
elements generate it: an assignment `η : Fin n → L` whose induced homomorphism
`FL(n) → L` ([Lattices.Free.Universal][]) is onto
(`FinitelyGenerated`{.AgdaFunction}).  It is *lower bounded* when some such
epimorphism is lower bounded, *upper bounded* when some is upper bounded, and
*bounded* when some is bounded: condition (1) of the book's Theorem 2.13, read
with the free lattice on `n` generators, which loses nothing since every
finite set is in bijection with a `Fin n`.  The book proves that for a lower
bounded lattice *every* homomorphism from a finitely generated lattice into it
is lower bounded (condition (2)); [Lattices.Bounded.Preimage][] proves that for
the homomorphisms from finitely generated free lattices, through condition (3).

```agda
module _ (𝑳 : Lattice αᴸ ρᴸ) where

  -- 𝑳 is generated by n elements: the induced homomorphism FL(n) → 𝑳 is onto.
  FinitelyGenerated : Type (αᴸ ⊔ ρᴸ)
  FinitelyGenerated = Σ[ n ∈ ℕ ] Σ[ η ∈ (Fin n → 𝕌[ proj₁ 𝑳 ]) ] IsSurjective (FL-extend 𝑳 η)

  -- Theorem 2.13 (1): some epimorphism from a finitely generated free lattice is lower bounded.
  LowerBoundedLattice : Type (αᴸ ⊔ ρᴸ)
  LowerBoundedLattice = Σ[ n ∈ ℕ ] Σ[ η ∈ (Fin n → 𝕌[ proj₁ 𝑳 ]) ]
    IsSurjective (FL-extend 𝑳 η) × LowerBounded (FL (Fin n)) 𝑳 (FL-extend-hom 𝑳 η)

  -- Dually, some such epimorphism is upper bounded.
  UpperBoundedLattice : Type (αᴸ ⊔ ρᴸ)
  UpperBoundedLattice = Σ[ n ∈ ℕ ] Σ[ η ∈ (Fin n → 𝕌[ proj₁ 𝑳 ]) ]
    IsSurjective (FL-extend 𝑳 η) × UpperBounded (FL (Fin n)) 𝑳 (FL-extend-hom 𝑳 η)

  -- Some such epimorphism is bounded.
  BoundedLattice : Type (αᴸ ⊔ ρᴸ)
  BoundedLattice = Σ[ n ∈ ℕ ] Σ[ η ∈ (Fin n → 𝕌[ proj₁ 𝑳 ]) ]
    IsSurjective (FL-extend 𝑳 η) × Bounded (FL (Fin n)) 𝑳 (FL-extend-hom 𝑳 η)
```

The module checks in well under a second of its own.
