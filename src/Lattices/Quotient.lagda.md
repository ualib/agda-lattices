---
layout: default
file: "src/Lattices/Quotient.lagda.md"
title: "Lattices.Quotient module"
date: "2026-10-17"
author: "the agda-algebras development team"
---

### Quotients of a lattice

This is the [Lattices.Quotient][] module of the [agda-lattices][] library.

A congruence `ψ` of a lattice `𝑳`{.AgdaBound} is an equivalence relation
compatible with meet and join, and the quotient `𝑳 / ψ` is again a lattice:
the same elements and operations, with `ψ` as the equality.
agda-algebras builds the quotient of any algebra by a congruence
(`_╱_`{.AgdaFunction} of [Setoid.Congruences.Basic][]), with the carrier and
the interpretation of the operations unchanged, so the eight lattice laws of
`𝑳`{.AgdaBound} hold in the quotient as they stand: each holds up to the
equality of `𝑳`{.AgdaBound}, which `ψ` contains (`_╱ˡ_`{.AgdaFunction}).  The
meet and join of `𝑳 ╱ˡ ψ` are those of `𝑳`{.AgdaBound}, definitionally, and so
is the value of every lattice term.

The quotient of a finite lattice by a *decidable* congruence is finite
(`╱ˡ-finite`{.AgdaFunction}): the enumeration of `𝑳`{.AgdaBound} still
enumerates it, and the decision procedure of `ψ` decides its equality.  This is
the finiteness that the decisions of [Lattices.Semidistributive][] and the
record `NationsTheorem`{.AgdaRecord} of [Lattices.Nation][] take.  A congruence
whose membership is not decidable gives a quotient whose equality is not; the
decidable congruences are `DecCon`{.AgdaFunction} of
[Setoid.Congruences.Finite.Basic][].

Congruences are compared by mutual containment, `≑` of
[Setoid.Congruences.Lattice][], not by propositional equality.  Equivalent
congruences give isomorphic quotients; the half of that used here is that the
identity map embeds `𝑳 ╱ˡ φ` in `𝑳 ╱ˡ ψ` when `φ ≑ ψ`
(`≑→Embeds`{.AgdaFunction}), so that every condition preserved by sublattices
passes from one quotient to the other.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Quotient where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; id )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid ; IsEquivalence )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; cong₂ ) renaming ( refl to ≡refl )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice ; _⊨ˡᵃ_ ; module Lattice-Op )
open import Classical.Theories.Lattice          using ( Th-Lattice )
open import Overture.Terms                      using ( Term ; ℊ ; node )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] ; Algebra )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )
open import Setoid.Congruences.Basic            using ( Con ; _╱_ ; IsCongruence ; reflexive
                                                      ; is-equivalence )
open import Setoid.Congruences.Finite.Basic     using ( DecCon )
open import Setoid.Congruences.Lattice          using ( _≑_ )
open import Setoid.Homomorphisms.Basic          using ( mkhom ; compatible-map )
open import Setoid.Terms                        using ( module Environment )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Term  using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ ; module Evaluation )
open import Lattices.Nation     using ( Embeds )

open Algebra  using ( Interp )
open Func     using () renaming ( to to _⟨$⟩_ )

private variable α ρ ℓ χ : Level
```
-->

#### The quotient lattice

The algebra of `𝑳 ╱ˡ ψ` is agda-algebras' quotient algebra
`proj₁ 𝑳 ╱ ψ`, which keeps the carrier and the interpretation of the
operations.  A term therefore takes the same value in the quotient as in
`𝑳`{.AgdaBound}, up to the equality of `𝑳`{.AgdaBound} (`╱-⟦⟧`{.AgdaFunction},
by induction on the term; the two values are not the same by computation,
because the value of a compound term applies the operation to a function of
the argument position, which differs between the two evaluations until the
position is known).  Each law of `Th-Lattice` then holds in the quotient
(`╱-laws`{.AgdaFunction}): it holds in `𝑳`{.AgdaBound} up to `≈`, and `ψ`
contains `≈`.

```agda
module _ (𝑳 : Lattice α ρ) (ψ : Con (proj₁ 𝑳) ℓ) where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ) renaming ( refl to ≈refl ; sym to ≈sym )
  open Environment (proj₁ 𝑳)        using () renaming ( ⟦_⟧ to ⟦_⟧ᴸ )
  open Environment (proj₁ 𝑳 ╱ ψ)    using () renaming ( ⟦_⟧ to ⟦_⟧ᵠ )
  open IsEquivalence (is-equivalence (proj₂ ψ)) using () renaming ( trans to ψ-trans )

  -- A term takes the same value in the quotient algebra as in 𝑳, up to ≈.
  ╱-⟦⟧ : {X : Type χ} (t : Term X) (η : X → 𝕌[ proj₁ 𝑳 ]) → ⟦ t ⟧ᵠ ⟨$⟩ η ≈ ⟦ t ⟧ᴸ ⟨$⟩ η
  ╱-⟦⟧ (ℊ x)          η = ≈refl
  ╱-⟦⟧ (node f args)  η = Func.cong (Interp (proj₁ 𝑳)) (≡refl , λ i → ╱-⟦⟧ (args i) η)

  -- The lattice laws hold in the quotient algebra.
  ╱-laws : (proj₁ 𝑳 ╱ ψ) ⊨ˡᵃ Th-Lattice
  ╱-laws i η = ψ-trans (reflexive (proj₂ ψ) (╱-⟦⟧ (proj₁ (Th-Lattice i)) η))
                (ψ-trans (reflexive (proj₂ ψ) (proj₂ 𝑳 i η))
                         (reflexive (proj₂ ψ) (≈sym (╱-⟦⟧ (proj₂ (Th-Lattice i)) η))))

infixl 6 _╱ˡ_

-- The quotient of a lattice by a congruence.
_╱ˡ_ : (𝑳 : Lattice α ρ) → Con (proj₁ 𝑳) ℓ → Lattice α ℓ
𝑳 ╱ˡ ψ = proj₁ 𝑳 ╱ ψ , ╱-laws 𝑳 ψ
```

The meet and join of the quotient lattice are those of `𝑳`{.AgdaBound},
definitionally, so the value of a lattice term (`LatTerm`{.AgdaDatatype} of
[Lattices.Free.Term][]) in the quotient is its value in `𝑳`{.AgdaBound}, up to
propositional equality (`╱ˡ-⟦⟧`{.AgdaFunction}, by induction on the term).

```agda
module _ (𝑳 : Lattice α ρ) (ψ : Con (proj₁ 𝑳) ℓ) where
  open Evaluation 𝑳          using () renaming ( ⟦_⟧ to ⟦_⟧ᴸ )
  open Evaluation (𝑳 ╱ˡ ψ)   using () renaming ( ⟦_⟧ to ⟦_⟧ᵠ )
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )

  -- A lattice term has the same value in the quotient as in 𝑳.
  ╱ˡ-⟦⟧ : {X : Type χ} (t : LatTerm X) (η : X → 𝕌[ proj₁ 𝑳 ]) → ⟦ t ⟧ᵠ η ≡ ⟦ t ⟧ᴸ η
  ╱ˡ-⟦⟧ (ℊ x)    η = ≡refl
  ╱ˡ-⟦⟧ (s ∧̇ t)  η = cong₂ _∧_ (╱ˡ-⟦⟧ s η) (╱ˡ-⟦⟧ t η)
  ╱ˡ-⟦⟧ (s ∨̇ t)  η = cong₂ _∨_ (╱ˡ-⟦⟧ s η) (╱ˡ-⟦⟧ t η)
```

#### The quotient of a finite lattice by a decidable congruence

The enumeration of `𝑳`{.AgdaBound} still enumerates the quotient, since each
element is `ψ`-related to the enumerated element it equals, and the decision
procedure of `ψ` decides the quotient's equality.

```agda
module _ (𝑳 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
  open FiniteAlgebra 𝑭 using ( card ; enum ; enum-sur )

  -- The quotient of a finite lattice by a decidable congruence is finite.
  ╱ˡ-finite : (ψ : DecCon (proj₁ 𝑳) ℓ) → FiniteAlgebra (proj₁ (𝑳 ╱ˡ proj₁ ψ))
  ╱ˡ-finite ψ = record
    { _≟_       = proj₂ ψ
    ; card      = card
    ; enum      = enum
    ; enum-sur  = λ x → proj₁ (enum-sur x)
                      , IsCongruence.reflexive (proj₂ (proj₁ ψ)) (proj₂ (enum-sur x))
    }
```

#### Equivalent congruences

If `φ ≑ ψ`, the identity map from `𝑳 ╱ˡ φ` to `𝑳 ╱ˡ ψ` respects the two
equalities (`φ ⊆ ψ`), is injective (`ψ ⊆ φ`), and commutes with the
operations, which are the same on both sides.

```agda
module _ (𝑳 : Lattice α ρ) {φ ψ : Con (proj₁ 𝑳) ℓ} (φ≑ψ : φ ≑ ψ) where
  private
    -- The identity, as a map of setoids.
    idF : Func 𝔻[ proj₁ (𝑳 ╱ˡ φ) ] 𝔻[ proj₁ (𝑳 ╱ˡ ψ) ]
    idF = record { to = id ; cong = proj₁ φ≑ψ }

    idF-compatible : compatible-map (proj₁ (𝑳 ╱ˡ φ)) (proj₁ (𝑳 ╱ˡ ψ)) idF
    idF-compatible = IsCongruence.reflexive (proj₂ ψ) (Setoid.refl 𝔻[ proj₁ 𝑳 ])

  -- Equivalent congruences: the identity embeds one quotient in the other.
  ≑→Embeds : Embeds (𝑳 ╱ˡ φ) (𝑳 ╱ˡ ψ)
  ≑→Embeds = mkhom (proj₁ (𝑳 ╱ˡ φ)) (proj₁ (𝑳 ╱ˡ ψ)) idF idF-compatible , proj₂ φ≑ψ
```
