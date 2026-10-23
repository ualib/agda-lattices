---
layout: default
file: "src/Lattices/Examples/Mn.lagda.md"
title: "Lattices.Examples.Mn module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Worked example: the lattices `Mₙ`

This is the [Lattices.Examples.Mn][] module of the [agda-lattices][] library.

For each `n`, the lattice `Mₙ` has a bottom `⊥`, a top `⊤`, and `n` atoms
between them, any two of which meet to `⊥` and join to `⊤`.  `M₀` is the
two-element chain, `M₁` the three-element chain, `M₂` the four-element Boolean
lattice `2²`, and `M₃` the diamond of [Lattices.Examples.M3][].  Every `Mₙ`
has length two, so every `Mₙ` is modular; `Mₙ` is distributive exactly when
`n ≤ 2`, since three atoms `a`, `b`, `c` give
`a ∧ (b ∨ c) = a ∧ ⊤ = a` and `(a ∧ b) ∨ (a ∧ c) = ⊥ ∨ ⊥ = ⊥`.  `M₄`, the
lattice with four atoms, has a name of its own here: after `M₃`, it is the
smallest `Mₙ` that is modular and not distributive.

The module builds `M n`{.AgdaFunction} on `Fin (2 + n)`, numbered as in
[Lattices.Examples.M3][]: `0` is the bottom, the next `n` elements are the
atoms, and the last, `fromℕ (1 + n)`, is the top, so that `M 3`{.AgdaFunction}
and `M₃`{.AgdaFunction} have the same carrier and the same tables.  (The size
is written `2 + n` rather than `n + 2` because it then reduces to
`suc (suc n)`, which the definitions by cases need.)  The two operations are
functions by cases, not literal tables: the join of two different elements is
the other one if either is `⊥`, and `⊤` otherwise, and the meet is dual.  They
are given order-first, as the project's conventions ask of an order-determined
construction: the order `x ≼ y` holds when `x` is the bottom, `y` is the top,
or `x = y`; it is a partial order, the join and the meet are its suprema and
infima, and the standard library derives the eight lattice equations from
that, for every `n` at once
(`Relation.Binary.Lattice.Properties.Lattice`{.AgdaModule}).  The lattice is
then a table lattice of [Lattices.Table][], with its enumeration.

The verdicts for `n ≤ 4` are decided by evaluation with the procedures of
[Lattices.Modular][]; the failure of distributivity for every `n ≥ 3` is a
lemma (`M-not-distributive`{.AgdaFunction}); and `M 3`{.AgdaFunction} is
isomorphic to `M₃`{.AgdaFunction} by the identity on `Fin 5`, both ways.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.Mn where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; fromℕ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F )
open import Data.Fin.Properties                    using ( _≟_ ; all? )
open import Data.Nat.Base                          using ( ℕ ; _+_ ; _≤_ ; s≤s ; z≤n )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.Lattice                using ( Supremum ; Infimum )
                                                   renaming ( Lattice to OrderLattice
                                                            ; IsLattice to IsOrderLattice )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans
                                                         ; subst ; isEquivalence )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; from-yes ; from-no )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

import Algebra.Lattice.Bundles                     as AlgLatticeBundles
import Algebra.Lattice.Properties.Lattice          as AlgLatticeProperties
import Relation.Binary.Lattice.Properties.Lattice  as OrderLatticeProperties

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic     using ( Lattice )
open import Setoid.Algebras.Finite                 using ( FiniteAlgebra )
open import Setoid.Homomorphisms.Isomorphisms      using ( _≅_ ; mkiso )

-- Imports from this library ----------------------------------------------------
open import Lattices.Examples.M3                   using ( M₃ ; M₃-laws )
                                                   renaming ( _∧_ to _∧³_ ; _∨_ to _∨³_ )
open import Lattices.Modular                       using ( IsModular ; IsDistributive
                                                         ; isModular? ; isDistributive? )
open import Lattices.Table                         using ( LatticeTableLaws ; tableLattice
                                                         ; tableLattice-FiniteAlgebra ; tableHom )
```
-->

#### The elements and the order

The carrier of `M n`{.AgdaFunction} is `Fin (2 + n)`; its bottom
`⊥ᴹ`{.AgdaFunction} is `0` and its top `⊤ᴹ`{.AgdaFunction} is the last
element.  They differ, whatever `n` is (`⊥ᴹ≢⊤ᴹ`{.AgdaFunction}).  The order
`x ≼ y` is the disjunction of the three ways it can hold, `x` the bottom, `y`
the top, or `x` and `y` equal; it is reflexive, transitive and antisymmetric
by cases, the two impossible cases being exactly those in which an element
would be both the bottom and the top.

```agda
module _ {n : ℕ} where

  ⊥ᴹ ⊤ᴹ : Fin (2 + n)
  ⊥ᴹ = zero
  ⊤ᴹ = fromℕ (1 + n)

  ⊥ᴹ≢⊤ᴹ : ⊥ᴹ ≢ ⊤ᴹ
  ⊥ᴹ≢⊤ᴹ ()

  -- An element that is both the bottom and the top is impossible.
  not-both : ∀ {x} → x ≡ ⊥ᴹ → x ≡ ⊤ᴹ → ∀ {ℓ} {A : Type ℓ} → A
  not-both x⊥ x⊤ = ⊥-elim (⊥ᴹ≢⊤ᴹ (trans (sym x⊥) x⊤))

  infix 4 _≼_

  -- x ≼ y in Mₙ: x is the bottom, y is the top, or x = y.
  _≼_ : Fin (2 + n) → Fin (2 + n) → Type
  x ≼ y = x ≡ ⊥ᴹ ⊎ (y ≡ ⊤ᴹ ⊎ x ≡ y)

  ≼-refl : ∀ {x} → x ≼ x
  ≼-refl = inj₂ (inj₂ refl)

  ≼-reflexive : ∀ {x y} → x ≡ y → x ≼ y
  ≼-reflexive x≡y = inj₂ (inj₂ x≡y)

  ⊥ᴹ-least : ∀ {x y} → x ≡ ⊥ᴹ → x ≼ y
  ⊥ᴹ-least = inj₁

  ⊤ᴹ-greatest : ∀ {x y} → y ≡ ⊤ᴹ → x ≼ y
  ⊤ᴹ-greatest y⊤ = inj₂ (inj₁ y⊤)

  ≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
  ≼-trans (inj₁ x⊥)          _                   = inj₁ x⊥
  ≼-trans (inj₂ (inj₁ y⊤))   (inj₁ y⊥)           = not-both y⊥ y⊤
  ≼-trans (inj₂ (inj₁ y⊤))   (inj₂ (inj₁ z⊤))    = ⊤ᴹ-greatest z⊤
  ≼-trans (inj₂ (inj₁ y⊤))   (inj₂ (inj₂ y≡z))   = ⊤ᴹ-greatest (trans (sym y≡z) y⊤)
  ≼-trans (inj₂ (inj₂ x≡y))  y≼z                 = subst (_≼ _) (sym x≡y) y≼z

  ≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
  ≼-antisym (inj₁ x⊥)          (inj₁ y⊥)          = trans x⊥ (sym y⊥)
  ≼-antisym (inj₁ x⊥)          (inj₂ (inj₁ x⊤))   = not-both x⊥ x⊤
  ≼-antisym (inj₁ _)           (inj₂ (inj₂ y≡x))  = sym y≡x
  ≼-antisym (inj₂ (inj₁ y⊤))   (inj₁ y⊥)          = not-both y⊥ y⊤
  ≼-antisym (inj₂ (inj₁ y⊤))   (inj₂ (inj₁ x⊤))   = trans x⊤ (sym y⊤)
  ≼-antisym (inj₂ (inj₁ _))    (inj₂ (inj₂ y≡x))  = sym y≡x
  ≼-antisym (inj₂ (inj₂ x≡y))  _                  = x≡y
```

#### The operations

The join and the meet are defined by cases on three decisions, which are
arguments of the helpers `join`{.AgdaFunction} and `meet`{.AgdaFunction}: is
`x = y`, and is either argument the bottom (for the join) or the top (for the
meet)?  The operations `_∨_`{.AgdaFunction} and `_∧_`{.AgdaFunction} supply the
decisions of `_≟_`{.AgdaFunction} on `Fin`, so that on concrete elements they
compute.  The lemmas about them are proved about the helpers, by matching on the
decisions, which avoids a `with` on the goal.

```agda
  -- The join, by cases on x ≟ y, x ≟ ⊥ and y ≟ ⊥.
  join : (x y : Fin (2 + n)) → Dec (x ≡ y) → Dec (x ≡ ⊥ᴹ) → Dec (y ≡ ⊥ᴹ) → Fin (2 + n)
  join x y (yes _)  _        _        = x
  join x y (no _)   (yes _)  _        = y
  join x y (no _)   (no _)   (yes _)  = x
  join x y (no _)   (no _)   (no _)   = ⊤ᴹ

  -- The meet, by cases on x ≟ y, x ≟ ⊤ and y ≟ ⊤.
  meet : (x y : Fin (2 + n)) → Dec (x ≡ y) → Dec (x ≡ ⊤ᴹ) → Dec (y ≡ ⊤ᴹ) → Fin (2 + n)
  meet x y (yes _)  _        _        = x
  meet x y (no _)   (yes _)  _        = y
  meet x y (no _)   (no _)   (yes _)  = x
  meet x y (no _)   (no _)   (no _)   = ⊥ᴹ

  infixl 7 _∧_ _∨_

  _∨_ _∧_ : Fin (2 + n) → Fin (2 + n) → Fin (2 + n)
  x ∨ y = join x y (x ≟ y) (x ≟ ⊥ᴹ) (y ≟ ⊥ᴹ)
  x ∧ y = meet x y (x ≟ y) (x ≟ ⊤ᴹ) (y ≟ ⊤ᴹ)
```

#### Suprema and infima

`x ∨ y` is an upper bound of `x` and `y` in each of the four cases of
`join`{.AgdaFunction}, and it lies below every upper bound `z`.  Only the last
case needs an argument: if `x` and `y` are different and neither is the bottom,
their join is the top, and an upper bound `z` of both is the top too, since
`x ≼ z` with `x` not the bottom forces `z` to be the top or `x` itself, and
`y ≼ z` likewise, while `z` cannot be both `x` and `y`
(`two-below→⊤`{.AgdaFunction}).  The meet is dual
(`two-above→⊥`{.AgdaFunction}).

```agda
  private
    two-below→⊤ : ∀ {x y z} → x ≢ y → x ≢ ⊥ᴹ → y ≢ ⊥ᴹ → x ≼ z → y ≼ z → ⊤ᴹ ≼ z
    two-below→⊤ _    x≢⊥  _    (inj₁ x⊥)          _                   = ⊥-elim (x≢⊥ x⊥)
    two-below→⊤ _    _    _    (inj₂ (inj₁ z⊤))   _                   = ⊤ᴹ-greatest z⊤
    two-below→⊤ _    _    y≢⊥  (inj₂ (inj₂ _))    (inj₁ y⊥)           = ⊥-elim (y≢⊥ y⊥)
    two-below→⊤ _    _    _    (inj₂ (inj₂ _))    (inj₂ (inj₁ z⊤))    = ⊤ᴹ-greatest z⊤
    two-below→⊤ x≢y  _    _    (inj₂ (inj₂ x≡z))  (inj₂ (inj₂ y≡z))   =
      ⊥-elim (x≢y (trans x≡z (sym y≡z)))

    two-above→⊥ : ∀ {x y z} → x ≢ y → x ≢ ⊤ᴹ → y ≢ ⊤ᴹ → z ≼ x → z ≼ y → z ≼ ⊥ᴹ
    two-above→⊥ _    _    _    (inj₁ z⊥)          _                   = ⊥ᴹ-least z⊥
    two-above→⊥ _    x≢⊤  _    (inj₂ (inj₁ x⊤))   _                   = ⊥-elim (x≢⊤ x⊤)
    two-above→⊥ _    _    _    (inj₂ (inj₂ _))    (inj₁ z⊥)           = ⊥ᴹ-least z⊥
    two-above→⊥ _    _    y≢⊤  (inj₂ (inj₂ _))    (inj₂ (inj₁ y⊤))    = ⊥-elim (y≢⊤ y⊤)
    two-above→⊥ x≢y  _    _    (inj₂ (inj₂ z≡x))  (inj₂ (inj₂ z≡y))   =
      ⊥-elim (x≢y (trans (sym z≡x) z≡y))

    join-upperˡ : ∀ x y d₁ d₂ d₃ → x ≼ join x y d₁ d₂ d₃
    join-upperˡ x y (yes _)  _         _        = ≼-refl
    join-upperˡ x y (no _)   (yes x⊥)  _        = ⊥ᴹ-least x⊥
    join-upperˡ x y (no _)   (no _)    (yes _)  = ≼-refl
    join-upperˡ x y (no _)   (no _)    (no _)   = ⊤ᴹ-greatest refl

    join-upperʳ : ∀ x y d₁ d₂ d₃ → y ≼ join x y d₁ d₂ d₃
    join-upperʳ x y (yes x≡y)  _        _         = ≼-reflexive (sym x≡y)
    join-upperʳ x y (no _)     (yes _)  _         = ≼-refl
    join-upperʳ x y (no _)     (no _)   (yes y⊥)  = ⊥ᴹ-least y⊥
    join-upperʳ x y (no _)     (no _)   (no _)    = ⊤ᴹ-greatest refl

    join-least : ∀ x y d₁ d₂ d₃ z → x ≼ z → y ≼ z → join x y d₁ d₂ d₃ ≼ z
    join-least x y (yes _)    _          _          z x≼z _    = x≼z
    join-least x y (no _)     (yes _)    _          z _   y≼z  = y≼z
    join-least x y (no _)     (no _)     (yes _)    z x≼z _    = x≼z
    join-least x y (no x≢y)   (no x≢⊥)   (no y≢⊥)   z x≼z y≼z  = two-below→⊤ x≢y x≢⊥ y≢⊥ x≼z y≼z

    meet-lowerˡ : ∀ x y d₁ d₂ d₃ → meet x y d₁ d₂ d₃ ≼ x
    meet-lowerˡ x y (yes _)  _         _        = ≼-refl
    meet-lowerˡ x y (no _)   (yes x⊤)  _        = ⊤ᴹ-greatest x⊤
    meet-lowerˡ x y (no _)   (no _)    (yes _)  = ≼-refl
    meet-lowerˡ x y (no _)   (no _)    (no _)   = ⊥ᴹ-least refl

    meet-lowerʳ : ∀ x y d₁ d₂ d₃ → meet x y d₁ d₂ d₃ ≼ y
    meet-lowerʳ x y (yes x≡y)  _        _         = ≼-reflexive x≡y
    meet-lowerʳ x y (no _)     (yes _)  _         = ≼-refl
    meet-lowerʳ x y (no _)     (no _)   (yes y⊤)  = ⊤ᴹ-greatest y⊤
    meet-lowerʳ x y (no _)     (no _)   (no _)    = ⊥ᴹ-least refl

    meet-greatest : ∀ x y d₁ d₂ d₃ z → z ≼ x → z ≼ y → z ≼ meet x y d₁ d₂ d₃
    meet-greatest x y (yes _)    _          _          z z≼x _    = z≼x
    meet-greatest x y (no _)     (yes _)    _          z _   z≼y  = z≼y
    meet-greatest x y (no _)     (no _)     (yes _)    z z≼x _    = z≼x
    meet-greatest x y (no x≢y)   (no x≢⊤)   (no y≢⊤)   z z≼x z≼y  = two-above→⊥ x≢y x≢⊤ y≢⊤ z≼x z≼y

  ∨-supremum : Supremum _≼_ _∨_
  ∨-supremum x y = join-upperˡ x y d₁ d₂ d₃ , join-upperʳ x y d₁ d₂ d₃ , join-least x y d₁ d₂ d₃
    where
    d₁ : Dec (x ≡ y)
    d₁ = x ≟ y

    d₂ : Dec (x ≡ ⊥ᴹ)
    d₂ = x ≟ ⊥ᴹ

    d₃ : Dec (y ≡ ⊥ᴹ)
    d₃ = y ≟ ⊥ᴹ

  ∧-infimum : Infimum _≼_ _∧_
  ∧-infimum x y = meet-lowerˡ x y d₁ d₂ d₃ , meet-lowerʳ x y d₁ d₂ d₃ , meet-greatest x y d₁ d₂ d₃
    where
    d₁ : Dec (x ≡ y)
    d₁ = x ≟ y

    d₂ : Dec (x ≡ ⊤ᴹ)
    d₂ = x ≟ ⊤ᴹ

    d₃ : Dec (y ≡ ⊤ᴹ)
    d₃ = y ≟ ⊤ᴹ
```

#### The lattice laws, for every `n`

The order and its suprema and infima make an order-theoretic lattice of the
standard library (`M-orderLattice`{.AgdaFunction}), and
`Relation.Binary.Lattice.Properties.Lattice`{.AgdaModule} turns it into an
algebraic one, whose equations are the eight that
`LatticeTableLaws`{.AgdaFunction} asks for, up to the shape of the second
absorption law, which takes one commutation.  The equality is `_≡_`
throughout.  The same device builds the partition lattices of
[Classical.Structures.Lattice.Partitions][].

```agda
M-isOrderLattice : (n : ℕ) → IsOrderLattice _≡_ (_≼_ {n}) _∨_ _∧_
M-isOrderLattice n = record
  { isPartialOrder = record
      { isPreorder = record
          { isEquivalence  = isEquivalence
          ; reflexive      = ≼-reflexive
          ; trans          = ≼-trans
          }
      ; antisym = ≼-antisym
      }
  ; supremum  = ∨-supremum
  ; infimum   = ∧-infimum
  }

M-orderLattice : (n : ℕ) → OrderLattice 0ℓ 0ℓ 0ℓ
M-orderLattice n = record
  { Carrier    = Fin (2 + n)
  ; _≈_        = _≡_
  ; _≤_        = _≼_
  ; _∨_        = _∨_
  ; _∧_        = _∧_
  ; isLattice  = M-isOrderLattice n
  }

M-laws : (n : ℕ) → LatticeTableLaws (_∧_ {n}) (_∨_ {n})
M-laws n = (λ a b c → AL.∧-assoc a b c) , AL.∧-comm , AP.∧-idem
         , (λ a b c → AL.∨-assoc a b c) , AL.∨-comm , AP.∨-idem
         , AL.∧-absorbs-∨ , λ a b → trans (AL.∨-comm (a ∧ b) a) (AL.∨-absorbs-∧ a b)
  where
  module OP = OrderLatticeProperties (M-orderLattice n)
  module AL = AlgLatticeBundles.Lattice OP.algLattice
  module AP = AlgLatticeProperties OP.algLattice
```

#### The lattice and its finiteness

```agda
M : (n : ℕ) → Lattice 0ℓ 0ℓ
M n = tableLattice _∧_ _∨_ (M-laws n)

M-finite : (n : ℕ) → FiniteAlgebra (proj₁ (M n))
M-finite n = tableLattice-FiniteAlgebra _∧_ _∨_ (M-laws n)

-- The lattice with four atoms.
M₄ : Lattice 0ℓ 0ℓ
M₄ = M 4

M₄-finite : FiniteAlgebra (proj₁ M₄)
M₄-finite = M-finite 4
```

#### The verdicts for `n ≤ 4`

Each verdict is a decision of [Lattices.Modular][] evaluated on `M n`, which
sweeps `(n + 2)³` triples: at most `216`, for `M₄`.  A distributive lattice is
modular, so the first three need only one decision each.

```agda
M₀-distributive : IsDistributive (M 0)
M₀-distributive = from-yes (isDistributive? (M 0) (M-finite 0))

M₁-distributive : IsDistributive (M 1)
M₁-distributive = from-yes (isDistributive? (M 1) (M-finite 1))

M₂-distributive : IsDistributive (M 2)
M₂-distributive = from-yes (isDistributive? (M 2) (M-finite 2))

M-3-modular : IsModular (M 3)
M-3-modular = from-yes (isModular? (M 3) (M-finite 3))

M-3-not-distributive : ¬ IsDistributive (M 3)
M-3-not-distributive = from-no (isDistributive? (M 3) (M-finite 3))

M₄-modular : IsModular M₄
M₄-modular = from-yes (isModular? M₄ M₄-finite)

M₄-not-distributive : ¬ IsDistributive M₄
M₄-not-distributive = from-no (isDistributive? M₄ M₄-finite)
```

#### Three atoms break distributivity, for every `n ≥ 3`

When `n ≥ 3`, the elements `1`, `2` and `3` of `Fin (2 + n)` are atoms: none
of them is `0` or the top.  The distributive law at the three of them reads
`1 ∧ (2 ∨ 3) = (1 ∧ 2) ∨ (1 ∧ 3)`.  On the right, both meets are `0` and so is
their join, by evaluation.  On the left, `2 ∨ 3` evaluates to the top, but the
meet of `1` with the top does not evaluate when `n` is a variable, since the
decision whether the top equals itself is stuck on `fromℕ n`; the lemma
`∧-⊤ᴹ`{.AgdaFunction}, that the top is a unit for the meet, proved by cases on
the decisions, gives `1 ∧ ⊤ = 1`.  So the law would give `1 = 0`.

```agda
module _ {n : ℕ} where
  private
    meet-⊤ᴹ : ∀ x d₁ d₂ d₃ → meet {n} x ⊤ᴹ d₁ d₂ d₃ ≡ x
    meet-⊤ᴹ x (yes _)  _         _          = refl
    meet-⊤ᴹ x (no _)   (yes x⊤)  _          = sym x⊤
    meet-⊤ᴹ x (no _)   (no _)    (yes _)    = refl
    meet-⊤ᴹ x (no _)   (no _)    (no ¬⊤⊤)   = ⊥-elim (¬⊤⊤ refl)

  -- The top is a unit for the meet.
  ∧-⊤ᴹ : ∀ x → x ∧ ⊤ᴹ {n} ≡ x
  ∧-⊤ᴹ x = meet-⊤ᴹ x (x ≟ ⊤ᴹ) (x ≟ ⊤ᴹ) (⊤ᴹ ≟ ⊤ᴹ)

M-not-distributive : ∀ {n} → 3 ≤ n → ¬ IsDistributive (M n)
M-not-distributive {n} (s≤s (s≤s (s≤s z≤n))) d = 1≢0 (trans (sym (∧-⊤ᴹ 1F)) (d 1F 2F 3F))
  where
  1≢0 : _≢_ {A = Fin (2 + n)} 1F 0F
  1≢0 ()
```

#### `M 3` is `M₃`

`M 3`{.AgdaFunction} and `M₃`{.AgdaFunction} of [Lattices.Examples.M3][] have
the carrier `Fin 5` and the same numbering, and their operations agree on all
25 pairs, by evaluation.  So the identity map is a homomorphism each way
(`tableHom`{.AgdaFunction} of [Lattices.Table][]), and the two composites are
the identity, by `refl`.

```agda
private
  agree-∧ : ∀ a b → a ∧ b ≡ a ∧³ b
  agree-∧ = from-yes (all? λ a → all? λ b → (a ∧ b) ≟ (a ∧³ b))

  agree-∨ : ∀ a b → a ∨ b ≡ a ∨³ b
  agree-∨ = from-yes (all? λ a → all? λ b → (a ∨ b) ≟ (a ∨³ b))

M3≅M₃ : proj₁ (M 3) ≅ proj₁ M₃
M3≅M₃ = mkiso (tableHom (M-laws 3) M₃ (λ i → i) agree-∧ agree-∨)
              (tableHom M₃-laws (M 3) (λ i → i) (λ a b → sym (agree-∧ a b))
                                                 (λ a b → sym (agree-∨ a b)))
              (λ _ → refl) (λ _ → refl)
```
