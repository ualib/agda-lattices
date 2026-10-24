---
layout: default
file: "src/Lattices/Product.lagda.md"
title: "Lattices.Product module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Finite products of lattices

This is the [Lattices.Product][] module of the [agda-lattices][] library.

This module constructs the product of lattices and records the properties of
products that the library uses, as follows.

+  The **binary direct product** `𝑳₁ ×ˡ 𝑳₂`{.AgdaFunction} of lattices
   `𝑳₁`{.AgdaBound} and `𝑳₂`{.AgdaBound} over
   [`Sig-Lattice`][Classical.Signatures.Lattice]: the lattice on the product
   setoid whose meet and join act componentwise (`LatticeProduct`{.AgdaModule}).
   The construction mirrors the group case of agda-algebras
   ([Classical.Structures.Group.Product][]) but is assembled through the
   setoid-level builder `setoidEqsToLattice`{.AgdaFunction} of
   [Classical.Structures.Lattice.Basic][], whose interpretation clauses reduce
   definitionally; consequently each of the eight lattice equations for the
   product is *literally* the pair of the component equations, and no
   term-induction lemma is needed.  The induced meet order of
   [Classical.Properties.Lattice][] is the componentwise order, definitionally,
   and the three accessors `≤ₓ-fst`{.AgdaFunction}, `≤ₓ-snd`{.AgdaFunction} and
   `≤ₓ-pair`{.AgdaFunction} name the two projections and the pairing.
+  The one-element lattice `𝟏ˡ`{.AgdaFunction}, the empty product.
+  The binary product is finite when its factors are
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

The binary product came from agda-algebras, where it was the module
`Classical.Structures.Lattice.Product`, with its history.  Following
agda-algebras' discipline for an eventual
Cubical port, the underlying equivalence of the product is isolated in
`A×B`{.AgdaFunction}, the pointwise pair of the component equivalences, so that
it can be mechanically substituted on the port.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Product where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; combine ; remQuot )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Fin.Properties                    using ( remQuot-combine )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _*_ )
open import Data.Product                           using ( Σ-syntax ; _,_ ; _×_ ; proj₁ ; proj₂ )
open import Data.Unit                              using ( ⊤ ; tt )
open import Function                               using ( Func ; _∘_ )
open import Level                                  using ( Level ; 0ℓ ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary.Decidable             using ( yes ; _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Operations                    using ( pair )
open import Classical.Properties.Lattice            using ( module Lattice-Order )
open import Classical.Signatures.Lattice            using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret          using ( interp-cong )
open import Classical.Structures.Lattice.Basic      using ( Lattice ; module Lattice-Op ; eqsToLattice
                                                          ; setoidEqsToLattice )
open import Lattices.Semidistributive               using ( IsSemidistributive )
open import Setoid.Algebras.Basic                   using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite                  using ( FiniteAlgebra )
open import Setoid.Homomorphisms.Basic              using ( hom ; mkhom ; compatible-map ; IsHom )

open Func renaming ( to to _⟨$⟩_ )

private variable α β ρ σ : Level
```
-->

#### The product construction

`LatticeProduct`{.AgdaModule} `𝑳₁` `𝑳₂` packages the whole development for a fixed
pair of lattices; opening it provides the product setoid, the componentwise
operations with their congruences and equations, the product lattice, and the
characterization of its order.

```agda
module LatticeProduct (𝑳₁ : Lattice α ρ) (𝑳₂ : Lattice β σ) where
  private
    𝑨 = proj₁ 𝑳₁
    𝑩 = proj₁ 𝑳₂

  open Setoid 𝔻[ 𝑨 ] using ()
    renaming ( _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ; trans to trans₁ )
  open Setoid 𝔻[ 𝑩 ] using ()
    renaming ( _≈_ to _≈₂_ ; refl to refl₂ ; sym to sym₂ ; trans to trans₂ )

  open Lattice-Op 𝑳₁ using ()
    renaming ( _∧_ to _∧₁_ ; _∨_ to _∨₁_ ; ∧-cong to ∧₁-cong ; ∨-cong to ∨₁-cong
             ; ∧-assoc-law to ∧₁-assoc ; ∧-comm-law to ∧₁-comm ; ∧-idem-law to ∧₁-idem
             ; ∨-assoc-law to ∨₁-assoc ; ∨-comm-law to ∨₁-comm ; ∨-idem-law to ∨₁-idem
             ; absorbˡ-law to absorbˡ₁ ; absorbʳ-law to absorbʳ₁ )
  open Lattice-Op 𝑳₂ using ()
    renaming ( _∧_ to _∧₂_ ; _∨_ to _∨₂_ ; ∧-cong to ∧₂-cong ; ∨-cong to ∨₂-cong
             ; ∧-assoc-law to ∧₂-assoc ; ∧-comm-law to ∧₂-comm ; ∧-idem-law to ∧₂-idem
             ; ∨-assoc-law to ∨₂-assoc ; ∨-comm-law to ∨₂-comm ; ∨-idem-law to ∨₂-idem
             ; absorbˡ-law to absorbˡ₂ ; absorbʳ-law to absorbʳ₂ )
```

The carrier of the product is the pair type, and its equivalence is the pointwise
pair of the component equivalences, the isolated-equality locus for the Cubical
port.

```agda
  A×B : Setoid (α ⊔ β) (ρ ⊔ σ)
  A×B = record
    { Carrier        = 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
    ; _≈_            = λ p q → (proj₁ p ≈₁ proj₁ q) × (proj₂ p ≈₂ proj₂ q)
    ; isEquivalence  = record
        { refl   = refl₁ , refl₂
        ; sym    = λ e → sym₁ (proj₁ e) , sym₂ (proj₂ e)
        ; trans  = λ (d₁ , d₂) (e₁ , e₂) → trans₁ d₁ e₁ , trans₂ d₂ e₂
        }
    }

  open Setoid A×B using () renaming ( _≈_ to _≈ₓ_ )
```

Meet and join act componentwise.  The operations project rather than pattern-match
their arguments, so they reduce on any pair expression, matched or not.

```agda
  _∧ₓ_ : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
  p ∧ₓ q = (proj₁ p ∧₁ proj₁ q) , (proj₂ p ∧₂ proj₂ q)

  _∨ₓ_ : 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ] → 𝕌[ 𝑨 ] × 𝕌[ 𝑩 ]
  p ∨ₓ q = (proj₁ p ∨₁ proj₁ q) , (proj₂ p ∨₂ proj₂ q)
```

Congruence and the eight equations are all inherited componentwise: each proof is
the pair of the component proofs, applied at the projections.

```agda
  ∧ₓ-cong : ∀ {p q u v} → p ≈ₓ q → u ≈ₓ v → (p ∧ₓ u) ≈ₓ (q ∧ₓ v)
  ∧ₓ-cong e f = ∧₁-cong (proj₁ e) (proj₁ f) , ∧₂-cong (proj₂ e) (proj₂ f)

  ∨ₓ-cong : ∀ {p q u v} → p ≈ₓ q → u ≈ₓ v → (p ∨ₓ u) ≈ₓ (q ∨ₓ v)
  ∨ₓ-cong e f = ∨₁-cong (proj₁ e) (proj₁ f) , ∨₂-cong (proj₂ e) (proj₂ f)

  ∧ₓ-assoc : ∀ {p q r} → ((p ∧ₓ q) ∧ₓ r) ≈ₓ (p ∧ₓ (q ∧ₓ r))
  ∧ₓ-assoc = ∧₁-assoc , ∧₂-assoc

  ∧ₓ-comm : ∀ {p q} → (p ∧ₓ q) ≈ₓ (q ∧ₓ p)
  ∧ₓ-comm = ∧₁-comm , ∧₂-comm

  ∧ₓ-idem : ∀ {p} → (p ∧ₓ p) ≈ₓ p
  ∧ₓ-idem = ∧₁-idem , ∧₂-idem

  ∨ₓ-assoc : ∀ {p q r} → ((p ∨ₓ q) ∨ₓ r) ≈ₓ (p ∨ₓ (q ∨ₓ r))
  ∨ₓ-assoc = ∨₁-assoc , ∨₂-assoc

  ∨ₓ-comm : ∀ {p q} → (p ∨ₓ q) ≈ₓ (q ∨ₓ p)
  ∨ₓ-comm = ∨₁-comm , ∨₂-comm

  ∨ₓ-idem : ∀ {p} → (p ∨ₓ p) ≈ₓ p
  ∨ₓ-idem = ∨₁-idem , ∨₂-idem

  absorbˡₓ : ∀ {p q} → (p ∧ₓ (p ∨ₓ q)) ≈ₓ p
  absorbˡₓ = absorbˡ₁ , absorbˡ₂

  absorbʳₓ : ∀ {p q} → ((p ∧ₓ q) ∨ₓ p) ≈ₓ p
  absorbʳₓ = absorbʳ₁ , absorbʳ₂
```

Assembling through the setoid-level builder yields the product lattice.

```agda
  ×ˡ-Lattice : Lattice (α ⊔ β) (ρ ⊔ σ)
  ×ˡ-Lattice = setoidEqsToLattice A×B _∧ₓ_ _∨ₓ_ ∧ₓ-cong ∨ₓ-cong
    ∧ₓ-assoc ∧ₓ-comm ∧ₓ-idem ∨ₓ-assoc ∨ₓ-comm ∨ₓ-idem absorbˡₓ absorbʳₓ
```

#### The product order is the componentwise order

The meet order of `×ˡ-Lattice`{.AgdaFunction} at `(p , q)` unfolds definitionally
to the pair of the component meet orders, because the builder's interpretation
applies its argument tuple and the product setoid's equality is the pointwise pair.
The three accessors below are therefore projections and pairing, but we name them:
they are the interface through which consumers read the product order without
unfolding the builder.

```agda
  open Lattice-Order ×ˡ-Lattice using () renaming ( _≤_ to _≤ₓ_ )
  open Lattice-Order 𝑳₁ using () renaming ( _≤_ to _≤₁_ )
  open Lattice-Order 𝑳₂ using () renaming ( _≤_ to _≤₂_ )

  -- The product order projects to the first factor's order.
  ≤ₓ-fst : ∀ {p q} → p ≤ₓ q → proj₁ p ≤₁ proj₁ q
  ≤ₓ-fst = proj₁

  -- The product order projects to the second factor's order.
  ≤ₓ-snd : ∀ {p q} → p ≤ₓ q → proj₂ p ≤₂ proj₂ q
  ≤ₓ-snd = proj₂

  -- Componentwise order proofs pair into a product order proof.
  ≤ₓ-pair : ∀ {p q} → proj₁ p ≤₁ proj₁ q → proj₂ p ≤₂ proj₂ q → p ≤ₓ q
  ≤ₓ-pair e f = e , f
```

#### The product operator

The standalone binary operator, for consumers that need only the lattice.

```agda
infixr 7 _×ˡ_

_×ˡ_ : Lattice α ρ → Lattice β σ → Lattice (α ⊔ β) (ρ ⊔ σ)
𝑳₁ ×ˡ 𝑳₂ = LatticeProduct.×ˡ-Lattice 𝑳₁ 𝑳₂
```

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

#### Properties of binary products

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
[Classical.Signatures.Lattice]: Classical.Signatures.Lattice.html
[Classical.Structures.Group.Product]: Classical.Structures.Group.Product.html
[Classical.Structures.Lattice.Basic]: Classical.Structures.Lattice.Basic.html
[Classical.Properties.Lattice]: Classical.Properties.Lattice.html
