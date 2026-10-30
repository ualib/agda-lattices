---
layout: default
file: "src/Lattices/Free/Extrema.lagda.md"
title: "Lattices.Free.Extrema module"
date: "2026-10-28"
author: "the agda-lattices development team"
---

### The least and greatest elements of a free lattice

This is the [Lattices.Free.Extrema][] module of the [agda-lattices][] library.

A free lattice on finitely many generators, at least one, has a least
element, the meet of the generators, and a greatest, their join; on none it
has no element at all ([Lattices.Free.Small][]), and on infinitely many it has
neither.  Constructively the statement is sharper: `FL(X)` has a least element
if and only if `X` has a finite nonempty enumeration
(`FL-bottom⇔enumeration`{.AgdaFunction}), and likewise a greatest element
(`FL-top⇔enumeration`{.AgdaFunction}).  So if no finite nonempty list contains
every generator, `FL(X)` has neither
(`no-enumeration→no-bottom`{.AgdaFunction},
`no-enumeration→no-top`{.AgdaFunction}).

One direction is an induction on terms: the meet of the generators of an
enumeration lies below each generator, so below every term
(`meet-least`{.AgdaFunction}), and dually (`join-greatest`{.AgdaFunction}).
The other reads an enumeration off a least element `b`: a term below a
generator `x` contains `x` (`below-generator`{.AgdaFunction}, by induction on
the derivation of Whitman's order, whose only rules with a generator on the
right are rules 1, 2 and 5), so every generator occurs in `b`, and the
generators occurring in `b` (`generators`{.AgdaFunction}) are a finite
nonempty list.  No equality of generators is decided.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Extrema where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-++⁺ˡ ; ∈-++⁺ʳ )
open import Data.List.Relation.Unary.Any           using ( here )
open import Data.Product                           using ( Σ-syntax ; _,_ )
open import Function                               using ( _⇔_ ; mk⇔ ; Equivalence )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( BottomOf ; TopOf )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Canonical.Basic  using ( ⋀⁺-lower ; ⋁⁺-upper )
                                           renaming ( ⋁⁺ to ⋁̇⁺ ; ⋀⁺ to ⋀̇⁺ )
open import Lattices.Free.Term             using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Universal        using ( FL ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Lattices.Free.Whitman          using ( _≤ʷ_ ; ∨≤ ; ℊ≤∧ ; ℊ≤ℊ ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ∧ˡ≤ℊ
                                                 ; ∧ʳ≤ℊ ; ≤∧ ; ≤ʷ-trans ; ∨̇-upperˡ ; ∧̇-lowerˡ )

private variable
  χ : Level
  X : Type χ
```
-->

#### The generators of a term

```agda
-- The generators occurring in a term, with repetitions.
generators : LatTerm X → List X
generators (ℊ x)    = x ∷ []
generators (s ∧̇ t)  = generators s ++ generators t
generators (s ∨̇ t)  = generators s ++ generators t

-- A term has a generator.
generators-∷ : (t : LatTerm X) → Σ[ g ∈ X ] Σ[ gs ∈ List X ] generators t ≡ g ∷ gs
generators-∷ (ℊ x)    = x , [] , refl
generators-∷ (s ∧̇ t)  =
  let (g , gs , e) = generators-∷ s in g , gs ++ generators t , cong (_++ generators t) e
generators-∷ (s ∨̇ t)  =
  let (g , gs , e) = generators-∷ s in g , gs ++ generators t , cong (_++ generators t) e

-- A term below a generator contains it.
below-generator : {w : LatTerm X} {x : X} → w ≤ʷ ℊ x → x ∈ generators w
below-generator (ℊ≤ℊ e)                = here (sym e)
below-generator (∨≤ p _)               = ∈-++⁺ˡ (below-generator p)
below-generator (∧ˡ≤ℊ p)               = ∈-++⁺ˡ (below-generator p)
below-generator (∧ʳ≤ℊ {s₁ = s₁} p)     = ∈-++⁺ʳ (generators s₁) (below-generator p)

-- A term above a generator contains it.
above-generator : {w : LatTerm X} {x : X} → ℊ x ≤ʷ w → x ∈ generators w
above-generator (ℊ≤ℊ e)                = here e
above-generator (ℊ≤∧ p _)              = ∈-++⁺ˡ (above-generator p)
above-generator (ℊ≤∨ˡ p)               = ∈-++⁺ˡ (above-generator p)
above-generator (ℊ≤∨ʳ {t₁ = t₁} p)     = ∈-++⁺ʳ (generators t₁) (above-generator p)
```

#### Bounds from an enumeration

```agda
module _ (g : X) (gs : List X) (enum : ∀ x → x ∈ g ∷ gs) where
  -- The meet of an enumeration of the generators lies below every term.
  meet-least : ∀ t → ⋀̇⁺ (ℊ g) (map ℊ gs) ≤ʷ t
  meet-least (ℊ x)    = ⋀⁺-lower (∈-map⁺ ℊ (enum x))
  meet-least (s ∧̇ t)  = ≤∧ (meet-least s) (meet-least t)
  meet-least (s ∨̇ t)  = ≤ʷ-trans (meet-least s) ∨̇-upperˡ

  -- The join of an enumeration of the generators lies above every term.
  join-greatest : ∀ t → t ≤ʷ ⋁̇⁺ (ℊ g) (map ℊ gs)
  join-greatest (ℊ x)    = ⋁⁺-upper (∈-map⁺ ℊ (enum x))
  join-greatest (s ∧̇ t)  = ≤ʷ-trans ∧̇-lowerˡ (join-greatest s)
  join-greatest (s ∨̇ t)  = ∨≤ (join-greatest s) (join-greatest t)
```

#### The characterization

```agda
-- FL(X) has a least element if and only if X has a finite nonempty enumeration.
FL-bottom⇔enumeration : BottomOf (FL X) ⇔ (Σ[ g ∈ X ] Σ[ gs ∈ List X ] (∀ x → x ∈ g ∷ gs))
FL-bottom⇔enumeration = mk⇔ to from
  where
  to : BottomOf (FL _) → Σ[ g ∈ _ ] Σ[ gs ∈ List _ ] (∀ x → x ∈ g ∷ gs)
  to (b , bottom) =
    let (g , gs , e) = generators-∷ b
    in  g , gs , λ x → subst (x ∈_) e (below-generator (≤→≤ʷ (bottom (ℊ x))))

  from : Σ[ g ∈ _ ] Σ[ gs ∈ List _ ] (∀ x → x ∈ g ∷ gs) → BottomOf (FL _)
  from (g , gs , enum) = ⋀̇⁺ (ℊ g) (map ℊ gs) , λ t → ≤ʷ→≤ (meet-least g gs enum t)

-- FL(X) has a greatest element if and only if X has a finite nonempty enumeration.
FL-top⇔enumeration : TopOf (FL X) ⇔ (Σ[ g ∈ X ] Σ[ gs ∈ List X ] (∀ x → x ∈ g ∷ gs))
FL-top⇔enumeration = mk⇔ to from
  where
  to : TopOf (FL _) → Σ[ g ∈ _ ] Σ[ gs ∈ List _ ] (∀ x → x ∈ g ∷ gs)
  to (b , top) =
    let (g , gs , e) = generators-∷ b
    in  g , gs , λ x → subst (x ∈_) e (above-generator (≤→≤ʷ (top (ℊ x))))

  from : Σ[ g ∈ _ ] Σ[ gs ∈ List _ ] (∀ x → x ∈ g ∷ gs) → TopOf (FL _)
  from (g , gs , enum) = ⋁̇⁺ (ℊ g) (map ℊ gs) , λ t → ≤ʷ→≤ (join-greatest g gs enum t)

-- If no finite list contains every generator, FL(X) has no least element.
no-enumeration→no-bottom : ¬ (Σ[ g ∈ X ] Σ[ gs ∈ List X ] (∀ x → x ∈ g ∷ gs)) → ¬ BottomOf (FL X)
no-enumeration→no-bottom ¬enum bottom = ¬enum (Equivalence.to FL-bottom⇔enumeration bottom)

-- If no finite list contains every generator, FL(X) has no greatest element.
no-enumeration→no-top : ¬ (Σ[ g ∈ X ] Σ[ gs ∈ List X ] (∀ x → x ∈ g ∷ gs)) → ¬ TopOf (FL X)
no-enumeration→no-top ¬enum top = ¬enum (Equivalence.to FL-top⇔enumeration top)
```

-----------------------------

[agda-lattices]: https://github.com/ualib/agda-lattices
[Lattices.Free.Extrema]: Lattices.Free.Extrema.html
[Lattices.Free.Small]: Lattices.Free.Small.html
