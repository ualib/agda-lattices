---
layout: default
file: "src/Lattices/Product.lagda.md"
title: "Lattices.Product module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Finite products of lattices

This is the [Lattices.Product][] module of the [agda-lattices][] library.

The product of two lattices is [Classical.Structures.Lattice.Product][] of the
Agda Universal Algebra Library.  This module supplies what a finite product
adds to it, as follows.

+  The one-element lattice `𝟏ˡ`{.AgdaFunction}, the empty product.
+  The binary product `𝑳₁ ×ˡ 𝑳₂` is finite when its factors are
   (`×ˡ-finite`{.AgdaFunction}: the enumeration is the standard library's
   bijection between `Fin (m * n)` and `Fin m × Fin n`), semidistributive when
   its factors are (`×ˡ-semidistributive`{.AgdaFunction}: the laws are
   universal Horn sentences, read componentwise), and its two projections are
   homomorphisms (`fst-hom`{.AgdaFunction}, `snd-hom`{.AgdaFunction}).
+  The product `Π m 𝓛`{.AgdaFunction} of a family of lattices indexed by
   `Fin m`, as nested binary products, with the same three properties, the
   projections `proj`{.AgdaFunction} as homomorphisms, tuples
   (`tuple`{.AgdaFunction}) from families of coordinates, and the order read
   coordinatewise (`Π-≤`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Product where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; combine ; remQuot )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Fin.Properties                    using ( remQuot-combine )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _*_ )
open import Data.Product                           using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit                              using ( ⊤ ; tt )
open import Function                               using ( Func ; _∘_ )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary.Decidable             using ( yes ; _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Operations                    using ( pair )
open import Classical.Properties.Lattice            using ( module Lattice-Order )
open import Classical.Signatures.Lattice            using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret          using ( interp-cong )
open import Classical.Structures.Lattice.Basic      using ( Lattice ; eqsToLattice )
open import Classical.Structures.Lattice.Product    using ( _×ˡ_ ; module LatticeProduct )
open import Lattices.Semidistributive               using ( IsSemidistributive )
open import Setoid.Algebras.Basic                   using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite                  using ( FiniteAlgebra )
open import Setoid.Homomorphisms.Basic              using ( hom ; mkhom ; compatible-map ; IsHom )

open Func renaming ( to to _⟨$⟩_ )

private variable α β ρ σ : Level
```
-->

#### The one-element lattice

```agda
-- The one-element lattice, finite and semidistributive.
𝟏ˡ : Lattice 0ℓ 0ℓ
𝟏ˡ = eqsToLattice ⊤ (λ _ _ → tt) (λ _ _ → tt)
       (λ _ _ _ → refl) (λ _ _ → refl) (λ _ → refl) (λ _ _ _ → refl) (λ _ _ → refl) (λ _ → refl)
       (λ _ _ → refl) (λ _ _ → refl)

𝟏ˡ-finite : FiniteAlgebra (proj₁ 𝟏ˡ)
𝟏ˡ-finite = record { _≟_ = λ _ _ → yes refl ; card = 1 ; enum = λ _ → tt ; enum-sur = λ _ → zero , refl }

𝟏ˡ-semidistributive : IsSemidistributive 𝟏ˡ
𝟏ˡ-semidistributive = (λ _ _ _ _ → refl) , (λ _ _ _ _ → refl)
```

#### Binary products

```agda
module Product (𝑳₁ : Lattice α ρ) (𝑳₂ : Lattice β σ) where
  open LatticeProduct 𝑳₁ 𝑳₂ public using ( ≤ₓ-fst ; ≤ₓ-snd ; ≤ₓ-pair )
  open Setoid 𝔻[ proj₁ 𝑳₁ ]  using () renaming ( refl to refl₁ )
  open Setoid 𝔻[ proj₁ 𝑳₂ ]  using () renaming ( refl to refl₂ )

  -- The projections are homomorphisms.
  fst-hom : hom (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₁)
  fst-hom = mkhom (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₁) (record { to = proj₁ ; cong = proj₁ }) compatible
    where
    compatible : compatible-map (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₁) (record { to = proj₁ ; cong = proj₁ })
    compatible {∧-Op} {a} = interp-cong (proj₁ 𝑳₁) ∧-Op λ { 0F → refl₁ ; 1F → refl₁ }
    compatible {∨-Op} {a} = interp-cong (proj₁ 𝑳₁) ∨-Op λ { 0F → refl₁ ; 1F → refl₁ }

  snd-hom : hom (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₂)
  snd-hom = mkhom (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₂) (record { to = proj₂ ; cong = proj₂ }) compatible
    where
    compatible : compatible-map (proj₁ (𝑳₁ ×ˡ 𝑳₂)) (proj₁ 𝑳₂) (record { to = proj₂ ; cong = proj₂ })
    compatible {∧-Op} {a} = interp-cong (proj₁ 𝑳₂) ∧-Op λ { 0F → refl₂ ; 1F → refl₂ }
    compatible {∨-Op} {a} = interp-cong (proj₁ 𝑳₂) ∨-Op λ { 0F → refl₂ ; 1F → refl₂ }

  -- A product of finite lattices is finite.
  ×ˡ-finite : FiniteAlgebra (proj₁ 𝑳₁) → FiniteAlgebra (proj₁ 𝑳₂) → FiniteAlgebra (proj₁ (𝑳₁ ×ˡ 𝑳₂))
  ×ˡ-finite F₁ F₂ = record
    { _≟_       = λ (x₁ , x₂) (y₁ , y₂) → (x₁ ≟₁ y₁) ×-dec (x₂ ≟₂ y₂)
    ; card      = card₁ * card₂
    ; enum      = enum
    ; enum-sur  = sur
    }
    where
    open FiniteAlgebra F₁ renaming ( _≟_ to _≟₁_ ; card to card₁ ; enum to enum₁ ; enum-sur to sur₁ )
    open FiniteAlgebra F₂ renaming ( _≟_ to _≟₂_ ; card to card₂ ; enum to enum₂ ; enum-sur to sur₂ )
    open Setoid 𝔻[ proj₁ (𝑳₁ ×ˡ 𝑳₂) ] using ( _≈_ )

    enum : Fin (card₁ * card₂) → 𝕌[ proj₁ (𝑳₁ ×ˡ 𝑳₂) ]
    enum i = enum₁ (proj₁ (remQuot {m = card₁} card₂ i)) , enum₂ (proj₂ (remQuot {m = card₁} card₂ i))

    sur : ∀ p → Σ[ i ∈ Fin (card₁ * card₂) ] enum i ≈ p
    sur (x , y) with sur₁ x | sur₂ y
    ... | j , e₁ | k , e₂ =
      combine j k , subst (λ q → (enum₁ (proj₁ q) , enum₂ (proj₂ q)) ≈ (x , y)) (sym (remQuot-combine {n = card₁} {k = card₂} j k)) (e₁ , e₂)

  -- A product of semidistributive lattices is semidistributive.
  ×ˡ-semidistributive : IsSemidistributive 𝑳₁ → IsSemidistributive 𝑳₂ → IsSemidistributive (𝑳₁ ×ˡ 𝑳₂)
  ×ˡ-semidistributive (j₁ , m₁) (j₂ , m₂) =
      (λ a b c (e₁ , e₂) → j₁ _ _ _ e₁ , j₂ _ _ _ e₂)
    , (λ a b c (e₁ , e₂) → m₁ _ _ _ e₁ , m₂ _ _ _ e₂)
```

#### Products over `Fin m`

```agda
-- The product of a family indexed by Fin m, and its properties.
Π : (m : ℕ) → (Fin m → Lattice 0ℓ 0ℓ) → Lattice 0ℓ 0ℓ
Π zero     𝓛 = 𝟏ˡ
Π (suc m)  𝓛 = 𝓛 zero ×ˡ Π m (𝓛 ∘ suc)

Π-finite : ∀ m (𝓛 : Fin m → Lattice 0ℓ 0ℓ) → (∀ j → FiniteAlgebra (proj₁ (𝓛 j))) → FiniteAlgebra (proj₁ (Π m 𝓛))
Π-finite zero     𝓛 F = 𝟏ˡ-finite
Π-finite (suc m)  𝓛 F = Product.×ˡ-finite (𝓛 zero) (Π m (𝓛 ∘ suc)) (F zero) (Π-finite m (𝓛 ∘ suc) (F ∘ suc))

Π-semidistributive : ∀ m (𝓛 : Fin m → Lattice 0ℓ 0ℓ) → (∀ j → IsSemidistributive (𝓛 j)) → IsSemidistributive (Π m 𝓛)
Π-semidistributive zero     𝓛 S = 𝟏ˡ-semidistributive
Π-semidistributive (suc m)  𝓛 S =
  Product.×ˡ-semidistributive (𝓛 zero) (Π m (𝓛 ∘ suc)) (S zero) (Π-semidistributive m (𝓛 ∘ suc) (S ∘ suc))

-- The j-th projection, as a map.
projMap : ∀ m (𝓛 : Fin m → Lattice 0ℓ 0ℓ) (j : Fin m) → 𝕌[ proj₁ (Π m 𝓛) ] → 𝕌[ proj₁ (𝓛 j) ]
projMap (suc m) 𝓛 zero     = proj₁
projMap (suc m) 𝓛 (suc j)  = projMap m (𝓛 ∘ suc) j ∘ proj₂

-- A tuple from a family of coordinates.
tuple : ∀ m (𝓛 : Fin m → Lattice 0ℓ 0ℓ) → (∀ j → 𝕌[ proj₁ (𝓛 j) ]) → 𝕌[ proj₁ (Π m 𝓛) ]
tuple zero     𝓛 f = tt
tuple (suc m)  𝓛 f = f zero , tuple m (𝓛 ∘ suc) (f ∘ suc)

projMap-tuple : ∀ m 𝓛 (f : ∀ j → 𝕌[ proj₁ (𝓛 j) ]) j → projMap m 𝓛 j (tuple m 𝓛 f) ≡ f j
projMap-tuple (suc m) 𝓛 f zero     = refl
projMap-tuple (suc m) 𝓛 f (suc j)  = projMap-tuple m (𝓛 ∘ suc) (f ∘ suc) j

-- The projections are homomorphisms.
proj : ∀ m (𝓛 : Fin m → Lattice 0ℓ 0ℓ) (j : Fin m) → hom (proj₁ (Π m 𝓛)) (proj₁ (𝓛 j))
proj (suc m) 𝓛 zero     = Product.fst-hom (𝓛 zero) (Π m (𝓛 ∘ suc))
proj (suc m) 𝓛 (suc j)  = mkhom (proj₁ (Π (suc m) 𝓛)) (proj₁ (𝓛 (suc j))) map compatible
  where
  inner = proj m (𝓛 ∘ suc) j
  map : Func 𝔻[ proj₁ (Π (suc m) 𝓛) ] 𝔻[ proj₁ (𝓛 (suc j)) ]
  map = record { to = λ x → proj₁ inner ⟨$⟩ proj₂ x ; cong = λ e → Func.cong (proj₁ inner) (proj₂ e) }
  open Setoid 𝔻[ proj₁ (𝓛 (suc j)) ] using () renaming ( refl to ≈refl ; trans to ≈trans )
  compatible : compatible-map (proj₁ (Π (suc m) 𝓛)) (proj₁ (𝓛 (suc j))) map
  compatible {∧-Op} {a} =
    ≈trans (IsHom.compatible (proj₂ inner) {∧-Op} {pair (proj₂ (a 0F)) (proj₂ (a 1F))})
           (interp-cong (proj₁ (𝓛 (suc j))) ∧-Op λ { 0F → ≈refl ; 1F → ≈refl })
  compatible {∨-Op} {a} =
    ≈trans (IsHom.compatible (proj₂ inner) {∨-Op} {pair (proj₂ (a 0F)) (proj₂ (a 1F))})
           (interp-cong (proj₁ (𝓛 (suc j))) ∨-Op λ { 0F → ≈refl ; 1F → ≈refl })

proj-map : ∀ m 𝓛 j x → proj₁ (proj m 𝓛 j) ⟨$⟩ x ≡ projMap m 𝓛 j x
proj-map (suc m) 𝓛 zero     x = refl
proj-map (suc m) 𝓛 (suc j)  x = proj-map m (𝓛 ∘ suc) j (proj₂ x)

-- The order of the product, from the coordinates.
Π-≤ : ∀ m 𝓛 x y → (∀ j → Lattice-Order._≤_ (𝓛 j) (projMap m 𝓛 j x) (projMap m 𝓛 j y))
    → Lattice-Order._≤_ (Π m 𝓛) x y
Π-≤ zero     𝓛 x y h = refl
Π-≤ (suc m)  𝓛 x y h = h zero , Π-≤ m (𝓛 ∘ suc) (proj₂ x) (proj₂ y) (h ∘ suc)
```

--------------------------------------

[Lattices.Product]: Lattices.Product.html
[Classical.Structures.Lattice.Product]: Classical.Structures.Lattice.Product.html
