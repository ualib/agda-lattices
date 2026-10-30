---
layout: default
file: "src/Lattices/Free/Small.lagda.md"
title: "Lattices.Free.Small module"
date: "2026-10-28"
author: "the agda-lattices development team"
---

### The free lattices on at most two generators

This is the [Lattices.Free.Small][] module of the [agda-lattices][] library.

The free lattice `FL(X)` is finite when `X` has at most two elements: `FL(∅)`
has no element, `FL(1)` one, and `FL(2)` four, the generators `x` and `y`,
their meet and their join, ordered as the square `2 × 2`.  `FL(3)` is
infinite; it contains `FL(ω)` ([Freese, Ježek, and Nation (1995)][], Theorem
1.28; [Lattices.Free.Countable][]).  Lattice terms have no constants, so a
lattice term over the empty type has no generator to start from, and there is
no term at all (`FL-empty`{.AgdaFunction}); over a type with at most one
element every term equals each generator, by idempotence
(`FL-subsingleton`{.AgdaFunction}).

"`FL(X)` has exactly `k` elements" is an enumeration of `FL(X)` by
`Fin k`{.AgdaDatatype} (`Enumeration X k`{.AgdaRecord}), complete up to the
equality `_≈ʷ_`{.AgdaFunction} of `FL(X)` and without repetition.  The module
gives one for each of `FL(0)`, `FL(1)` and `FL(2)`
(`FL₀-enumeration`{.AgdaFunction}, `FL₁-enumeration`{.AgdaFunction},
`FL₂-enumeration`{.AgdaFunction}).  For `FL(2)` the four terms are closed under
meet and join up to `_≈ʷ_`{.AgdaFunction}, by at most 2 × 64 decisions of
Whitman's procedure on terms of rank at most 7 (`meet-closed`{.AgdaFunction},
`join-closed`{.AgdaFunction}), so every term equals one of them, by induction on
the term; and they are pairwise distinct, by 16 more decisions.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Small where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; any? )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( Σ-syntax ; _,_ ; ∃ )
open import Level                                  using ( Level )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable             using ( from-yes ; _→-dec_ )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Canonical.Basic  using  ( ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans
                                                  ; ∧̇-cong ; ∨̇-cong ; ∧̇-idem ; ∨̇-idem )
open import Lattices.Free.Term             using  ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman          using  ( _≈ʷ_ ; module Decision )

private variable
  χ : Level
  X : Type χ
```
-->

#### `FL(∅)` and `FL(1)`

```agda
-- Over a type with no element there is no lattice term: FL(∅) is empty.
FL-empty : ¬ X → ¬ LatTerm X
FL-empty ¬x (ℊ x)    = ¬x x
FL-empty ¬x (s ∧̇ t)  = FL-empty ¬x s
FL-empty ¬x (s ∨̇ t)  = FL-empty ¬x s

-- Over a type with at most one element, every term equals each generator.
FL-subsingleton : (∀ (x y : X) → x ≡ y) → (t : LatTerm X) (x : X) → t ≈ʷ ℊ x
FL-subsingleton one (ℊ y)    x = subst (λ z → ℊ y ≈ʷ ℊ z) (one y x) ≈ʷ-refl
FL-subsingleton one (s ∧̇ t)  x =
  ≈ʷ-trans (∧̇-cong (FL-subsingleton one s x) (FL-subsingleton one t x)) ∧̇-idem
FL-subsingleton one (s ∨̇ t)  x =
  ≈ʷ-trans (∨̇-cong (FL-subsingleton one s x) (FL-subsingleton one t x)) ∨̇-idem
```

#### Enumerations

```agda
-- FL(X) has exactly k elements: an enumeration, complete up to ≈ʷ and without repetition.
record Enumeration (X : Type χ) (k : ℕ) : Type χ where
  field
    element   : Fin k → LatTerm X
    complete  : ∀ t → Σ[ i ∈ Fin k ] t ≈ʷ element i
    distinct  : ∀ i j → element i ≈ʷ element j → i ≡ j

-- FL(0) has no element.
FL₀-enumeration : Enumeration (Fin 0) 0
FL₀-enumeration = record
  { element   = λ ()
  ; complete  = λ t → ⊥-elim (FL-empty (λ ()) t)
  ; distinct  = λ ()
  }

-- FL(1) has one element.
FL₁-enumeration : Enumeration (Fin 1) 1
FL₁-enumeration = record
  { element   = λ _ → ℊ 0F
  ; complete  = λ t → 0F , FL-subsingleton one t 0F
  ; distinct  = λ { 0F 0F _ → refl }
  }
  where
  one : ∀ (x y : Fin 1) → x ≡ y
  one 0F 0F = refl
```

#### `FL(2)`

The four elements of `FL(2)`, numbered from the bottom: `x ∧ y`, `x`, `y`,
`x ∨ y`.

```agda
private
  open Decision (_≟_ {2}) using ( _≈ʷ?_ )

  -- x ∧ y, x, y, x ∨ y.
  four : Fin 4 → LatTerm (Fin 2)
  four 0F = ℊ 0F ∧̇ ℊ 1F
  four 1F = ℊ 0F
  four 2F = ℊ 1F
  four 3F = ℊ 0F ∨̇ ℊ 1F

  -- The four elements are closed under meet, up to ≈ʷ.
  meet-closed : ∀ i j → ∃ λ k → four k ≈ʷ four i ∧̇ four j
  meet-closed = from-yes (all? λ i → all? λ j → any? λ k → four k ≈ʷ? four i ∧̇ four j)

  -- The four elements are closed under join, up to ≈ʷ.
  join-closed : ∀ i j → ∃ λ k → four k ≈ʷ four i ∨̇ four j
  join-closed = from-yes (all? λ i → all? λ j → any? λ k → four k ≈ʷ? four i ∨̇ four j)

  -- Every term over two generators equals one of the four.
  four-complete : ∀ t → Σ[ i ∈ Fin 4 ] t ≈ʷ four i
  four-complete (ℊ 0F)   = 1F , ≈ʷ-refl
  four-complete (ℊ 1F)   = 2F , ≈ʷ-refl
  four-complete (s ∧̇ t)  =
    let (i , si) = four-complete s
        (j , tj) = four-complete t
        (k , e)  = meet-closed i j
    in  k , ≈ʷ-trans (∧̇-cong si tj) (≈ʷ-sym e)
  four-complete (s ∨̇ t)  =
    let (i , si) = four-complete s
        (j , tj) = four-complete t
        (k , e)  = join-closed i j
    in  k , ≈ʷ-trans (∨̇-cong si tj) (≈ʷ-sym e)

  -- The four elements are pairwise distinct.
  four-distinct : ∀ i j → four i ≈ʷ four j → i ≡ j
  four-distinct = from-yes (all? λ i → all? λ j → four i ≈ʷ? four j →-dec i ≟ j)

-- FL(2) has four elements.
FL₂-enumeration : Enumeration (Fin 2) 4
FL₂-enumeration .Enumeration.element = four
FL₂-enumeration .Enumeration.complete = four-complete
FL₂-enumeration .Enumeration.distinct = four-distinct
```

-----------------------------

[Freese, Ježek, and Nation (1995)]: https://doi.org/10.1090/surv/042
[agda-lattices]: https://github.com/ualib/agda-lattices
[Lattices.Free.Small]: Lattices.Free.Small.html
[Lattices.Free.Countable]: Lattices.Free.Countable.html
