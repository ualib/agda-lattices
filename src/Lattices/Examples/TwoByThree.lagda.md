---
layout: default
file: "src/Lattices/Examples/TwoByThree.lagda.md"
title: "Lattices.Examples.TwoByThree module"
date: "2026-10-13"
author: "the agda-algebras development team"
---

### Worked example: the lattice `2 × 3` as a direct decomposition

This is the [Lattices.Examples.TwoByThree][] module of the [agda-lattices][] library.

The product of the two-element chain `2` and the three-element chain `3` is a
six-element distributive lattice.  This module checks that decomposition with
the direct-decomposition theory of agda-algebras' `Setoid.Decompositions`
(McKenzie, McNulty, and Taylor, *Algebras, Lattices, Varieties* I, §4.4 and
Chapter 5), every finite fact decided by evaluation, exactly as agda-algebras'
`Examples.Classical.Groups.CyclicGroup6` does for `ℤ/6ℤ ≅ ℤ/2ℤ × ℤ/3ℤ`.

+  The three lattices are given by their tables through [Lattices.Table][].
+  The two coordinate projections `2 × 3 → 2` and `2 × 3 → 3` are lattice
   homomorphisms (decided), and their kernels `θ₂` and `θ₃` are decidable
   congruences.
+  `θ₂` and `θ₃` form a factor pair (decided by `isFactorPair?`{.AgdaFunction}),
   so `2 × 3 ≅ 2 × 3 / θ₂ × 2 × 3 / θ₃ ≅ 2 × 3` by Theorem 4.29 and the first
   isomorphism theorem: the abstract product `_×ᴬ_`{.AgdaFunction} of the two
   chains is the table lattice we started from.
+  The chains have at most three elements, so they are directly indecomposable
   (`small→indecomposable`{.AgdaFunction}), and `θ₂`, `θ₃` are indecomposable
   congruences: `0 = θ₂ × θ₃` is the factorization of `2 × 3` into
   indecomposables.

Every lattice has a distributive congruence lattice (Funayama and Nakayama), so
every lattice has the strict refinement property (ALV Theorem 5.17,
Corollary 1), and this factorization is unique; neither fact is formalized here.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.TwoByThree where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; 0≢1+n )
open import Data.Nat.Properties                    using () renaming ( _≤?_ to _≤ⁿ?_ )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Data.Vec.Base                          using ( _∷_ ; [] )
open import Function                               using ( Func )
open import Level                                  using ( 0ℓ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Lattice  using ( Sig-Lattice ; ∧-Op ; ∨-Op )
open import Overture.Cayley               using ( Table ; ⟦_⟧ ; from-yes )
open import Setoid.Algebras               using ( Algebra ; 𝔻[_] ; _×ᴬ_ )
open import Setoid.Algebras.Finite        using ( FiniteAlgebra )
open import Setoid.Congruences.Basic      using ( Con ; _╱_ )
open import Setoid.Congruences.Finite     using ( DecCon )
open import Setoid.Congruences.Monolith   using ( Trivial )
open import Setoid.Decompositions         using ( IsFactorPair ; isFactorPair? ; factorPair→≅
                                                ; nontrivial? ; IsDirectlyIndecomposable
                                                ; factor-trivial ; small→indecomposable
                                                ; IsIndecomposable ; directly→indecomposable
                                                ; ≅-indecomposable )
open import Setoid.Functions              using ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms          using ( hom ; mkhom ; compatible-map ; kercon
                                                ; FirstIsoTheorem ; _≅_ ; ≅-sym ; ≅-trans
                                                ; ×ᴬ-≅ )

-- Imports from the agda-lattices library ---------------------------------------
open import Lattices.Table  using ( LatticeTableLaws ; latticeTableLaws? ; tableLattice
                                  ; tableLattice-FiniteAlgebra )

open Func using () renaming ( to to _⟨$⟩_ )
```
-->

#### The chains `2` and `3`

The chains are `Fin 2` and `Fin 3` with meet the minimum and join the maximum.

```agda
-- The two-element chain.
∧₂-table ∨₂-table : Table 2
∧₂-table = (0F ∷ 0F ∷ []) ∷ (0F ∷ 1F ∷ []) ∷ []
∨₂-table = (0F ∷ 1F ∷ []) ∷ (1F ∷ 1F ∷ []) ∷ []

_∧₂_ _∨₂_ : Fin 2 → Fin 2 → Fin 2
_∧₂_ = ⟦ ∧₂-table ⟧
_∨₂_ = ⟦ ∨₂-table ⟧

-- The three-element chain.
∧₃-table ∨₃-table : Table 3
∧₃-table = (0F ∷ 0F ∷ 0F ∷ []) ∷ (0F ∷ 1F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 2F ∷ []) ∷ []
∨₃-table = (0F ∷ 1F ∷ 2F ∷ []) ∷ (1F ∷ 1F ∷ 2F ∷ []) ∷ (2F ∷ 2F ∷ 2F ∷ []) ∷ []

_∧₃_ _∨₃_ : Fin 3 → Fin 3 → Fin 3
_∧₃_ = ⟦ ∧₃-table ⟧
_∨₃_ = ⟦ ∨₃-table ⟧
```

#### The lattice `2 × 3`

The carrier is `Fin 6`, the pair `(i , j)` numbered `3i + j`; meet and join are
taken coordinatewise.

| `∧` | 0 | 1 | 2 | 3 | 4 | 5 |   | `∨` | 0 | 1 | 2 | 3 | 4 | 5 |
|-----|---|---|---|---|---|---|---|-----|---|---|---|---|---|---|
| 0   | 0 | 0 | 0 | 0 | 0 | 0 |   | 0   | 0 | 1 | 2 | 3 | 4 | 5 |
| 1   | 0 | 1 | 1 | 0 | 1 | 1 |   | 1   | 1 | 1 | 2 | 4 | 4 | 5 |
| 2   | 0 | 1 | 2 | 0 | 1 | 2 |   | 2   | 2 | 2 | 2 | 5 | 5 | 5 |
| 3   | 0 | 0 | 0 | 3 | 3 | 3 |   | 3   | 3 | 4 | 5 | 3 | 4 | 5 |
| 4   | 0 | 1 | 1 | 3 | 4 | 4 |   | 4   | 4 | 4 | 5 | 4 | 4 | 5 |
| 5   | 0 | 1 | 2 | 3 | 4 | 5 |   | 5   | 5 | 5 | 5 | 5 | 5 | 5 |

```agda
∧-table ∨-table : Table 6
∧-table = (0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ 0F ∷ [])
        ∷ (0F ∷ 1F ∷ 1F ∷ 0F ∷ 1F ∷ 1F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 0F ∷ 1F ∷ 2F ∷ [])
        ∷ (0F ∷ 0F ∷ 0F ∷ 3F ∷ 3F ∷ 3F ∷ [])
        ∷ (0F ∷ 1F ∷ 1F ∷ 3F ∷ 4F ∷ 4F ∷ [])
        ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ []
∨-table = (0F ∷ 1F ∷ 2F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ (1F ∷ 1F ∷ 2F ∷ 4F ∷ 4F ∷ 5F ∷ [])
        ∷ (2F ∷ 2F ∷ 2F ∷ 5F ∷ 5F ∷ 5F ∷ [])
        ∷ (3F ∷ 4F ∷ 5F ∷ 3F ∷ 4F ∷ 5F ∷ [])
        ∷ (4F ∷ 4F ∷ 5F ∷ 4F ∷ 4F ∷ 5F ∷ [])
        ∷ (5F ∷ 5F ∷ 5F ∷ 5F ∷ 5F ∷ 5F ∷ [])
        ∷ []

_∧_ _∨_ : Fin 6 → Fin 6 → Fin 6
_∧_ = ⟦ ∧-table ⟧
_∨_ = ⟦ ∨-table ⟧
```

The three pairs of tables satisfy the lattice laws (decided), and give the
underlying `Sig-Lattice`{.AgdaFunction} algebras `𝑳₂`, `𝑳₃`, and `𝑳₆` with their
finiteness witnesses.

```agda
-- The lattice laws, decided.
laws₂ : LatticeTableLaws _∧₂_ _∨₂_
laws₂ = from-yes (latticeTableLaws? _∧₂_ _∨₂_)

laws₃ : LatticeTableLaws _∧₃_ _∨₃_
laws₃ = from-yes (latticeTableLaws? _∧₃_ _∨₃_)

laws₆ : LatticeTableLaws _∧_ _∨_
laws₆ = from-yes (latticeTableLaws? _∧_ _∨_)

-- The underlying algebras: the chains 2 and 3, and the lattice 2 × 3.
𝑳₂ 𝑳₃ 𝑳₆ : Algebra {𝑆 = Sig-Lattice} 0ℓ 0ℓ
𝑳₂ = proj₁ (tableLattice _∧₂_ _∨₂_ laws₂)
𝑳₃ = proj₁ (tableLattice _∧₃_ _∨₃_ laws₃)
𝑳₆ = proj₁ (tableLattice _∧_ _∨_ laws₆)

-- Their finiteness witnesses.
𝑭₂ : FiniteAlgebra 𝑳₂
𝑭₂ = tableLattice-FiniteAlgebra _∧₂_ _∨₂_ laws₂

𝑭₃ : FiniteAlgebra 𝑳₃
𝑭₃ = tableLattice-FiniteAlgebra _∧₃_ _∨₃_ laws₃

𝑭₆ : FiniteAlgebra 𝑳₆
𝑭₆ = tableLattice-FiniteAlgebra _∧_ _∨_ laws₆
```

#### The coordinate projections

The first coordinate of `3i + j` is `i` and the second is `j`; the projections
respect meet and join, which is decided over the carrier.

```agda
-- The first coordinate, onto 2.
π₂ : Fin 6 → Fin 2
π₂ 0F = 0F
π₂ 1F = 0F
π₂ 2F = 0F
π₂ 3F = 1F
π₂ 4F = 1F
π₂ 5F = 1F

-- The second coordinate, onto 3.
π₃ : Fin 6 → Fin 3
π₃ 0F = 0F
π₃ 1F = 1F
π₃ 2F = 2F
π₃ 3F = 0F
π₃ 4F = 1F
π₃ 5F = 2F

-- The projections respect meet and join (decided).
π₂-∧ : ∀ x y → π₂ (x ∧ y) ≡ π₂ x ∧₂ π₂ y
π₂-∧ = from-yes (all? λ x → all? λ y → π₂ (x ∧ y) ≟ π₂ x ∧₂ π₂ y)

π₂-∨ : ∀ x y → π₂ (x ∨ y) ≡ π₂ x ∨₂ π₂ y
π₂-∨ = from-yes (all? λ x → all? λ y → π₂ (x ∨ y) ≟ π₂ x ∨₂ π₂ y)

π₃-∧ : ∀ x y → π₃ (x ∧ y) ≡ π₃ x ∧₃ π₃ y
π₃-∧ = from-yes (all? λ x → all? λ y → π₃ (x ∧ y) ≟ π₃ x ∧₃ π₃ y)

π₃-∨ : ∀ x y → π₃ (x ∨ y) ≡ π₃ x ∨₃ π₃ y
π₃-∨ = from-yes (all? λ x → all? λ y → π₃ (x ∨ y) ≟ π₃ x ∨₃ π₃ y)
```

So the projections are homomorphisms of `Sig-Lattice`{.AgdaFunction} algebras.

```agda
-- The first projection is a lattice homomorphism 2 × 3 → 2.
π₂-hom : hom 𝑳₆ 𝑳₂
π₂-hom = mkhom 𝑳₆ 𝑳₂ F λ {f} {a} → compatible {f} {a}
  where
  F : Func 𝔻[ 𝑳₆ ] 𝔻[ 𝑳₂ ]
  F ⟨$⟩ x = π₂ x
  F .Func.cong = cong π₂

  compatible : compatible-map 𝑳₆ 𝑳₂ F
  compatible {∧-Op} {a} = π₂-∧ (a 0F) (a 1F)
  compatible {∨-Op} {a} = π₂-∨ (a 0F) (a 1F)

-- The second projection is a lattice homomorphism 2 × 3 → 3.
π₃-hom : hom 𝑳₆ 𝑳₃
π₃-hom = mkhom 𝑳₆ 𝑳₃ F λ {f} {a} → compatible {f} {a}
  where
  F : Func 𝔻[ 𝑳₆ ] 𝔻[ 𝑳₃ ]
  F ⟨$⟩ x = π₃ x
  F .Func.cong = cong π₃

  compatible : compatible-map 𝑳₆ 𝑳₃ F
  compatible {∧-Op} {a} = π₃-∧ (a 0F) (a 1F)
  compatible {∨-Op} {a} = π₃-∨ (a 0F) (a 1F)
```

#### The factor pair

The kernels of the projections, `θ₂` (same first coordinate) and `θ₃` (same
second coordinate), are decidable congruences, and `isFactorPair?`{.AgdaFunction}
decides that they form a factor pair.  Neither is total, so `2 × 3` is not
directly indecomposable.

```agda
-- The kernels of the projections.
θ₂ θ₃ : Con 𝑳₆ 0ℓ
θ₂ = kercon π₂-hom
θ₃ = kercon π₃-hom

-- They are decidable.
θ₂ᵈ θ₃ᵈ : DecCon 𝑳₆ 0ℓ
θ₂ᵈ = θ₂ , λ x y → π₂ x ≟ π₂ y
θ₃ᵈ = θ₃ , λ x y → π₃ x ≟ π₃ y

-- ⟨θ₂ , θ₃⟩ is a factor pair of 2 × 3 (decided).
θ₂θ₃-factorPair : IsFactorPair θ₂ θ₃
θ₂θ₃-factorPair = from-yes (isFactorPair? 𝑭₆ θ₂ᵈ θ₃ᵈ)

-- Neither factor is trivial.
θ₂-proper : ¬ Trivial (𝑳₆ ╱ θ₂)
θ₂-proper t = 0≢1+n (t 0F 3F)

θ₃-proper : ¬ Trivial (𝑳₆ ╱ θ₃)
θ₃-proper t = 0≢1+n (t 0F 1F)

-- So 2 × 3 is not directly indecomposable.
L6-decomposable : ¬ IsDirectlyIndecomposable 0ℓ 𝑳₆
L6-decomposable di = [ θ₂-proper , θ₃-proper ]′ (factor-trivial di θ₂ θ₃ θ₂θ₃-factorPair)
```

#### The decomposition and its factors

Theorem 4.29 and the first isomorphism theorem give `2 × 3 ≅ 2 ×ᴬ 3`.  The
chains are directly indecomposable by `small→indecomposable`{.AgdaFunction}, so
the kernels are indecomposable congruences.

```agda
-- ALV Theorem 4.29: 2 × 3 ≅ (2 × 3)/θ₂ × (2 × 3)/θ₃.
L6≅quotients : 𝑳₆ ≅ ((𝑳₆ ╱ θ₂) ×ᴬ (𝑳₆ ╱ θ₃))
L6≅quotients = factorPair→≅ θ₂ θ₃ θ₂θ₃-factorPair

-- The projections are onto.
π₂-onto : IsSurjective (proj₁ π₂-hom)
π₂-onto {0F} = Image_∋_.eq 0F refl
π₂-onto {1F} = Image_∋_.eq 3F refl

π₃-onto : IsSurjective (proj₁ π₃-hom)
π₃-onto {0F} = Image_∋_.eq 0F refl
π₃-onto {1F} = Image_∋_.eq 1F refl
π₃-onto {2F} = Image_∋_.eq 2F refl

-- The first isomorphism theorem identifies the quotients with the chains.
quotient₂≅L2 : (𝑳₆ ╱ θ₂) ≅ 𝑳₂
quotient₂≅L2 = FirstIsoTheorem π₂-hom π₂-onto

quotient₃≅L3 : (𝑳₆ ╱ θ₃) ≅ 𝑳₃
quotient₃≅L3 = FirstIsoTheorem π₃-hom π₃-onto

-- The table lattice 2 × 3 is the product of the chains.
L6≅L2×L3 : 𝑳₆ ≅ (𝑳₂ ×ᴬ 𝑳₃)
L6≅L2×L3 = ≅-trans L6≅quotients (×ᴬ-≅ quotient₂≅L2 quotient₃≅L3)

-- The chains are directly indecomposable.
L2-indecomposable : IsDirectlyIndecomposable 0ℓ 𝑳₂
L2-indecomposable = small→indecomposable 𝑭₂ (from-yes (2 ≤ⁿ? 3)) (from-yes (nontrivial? 𝑭₂))

L3-indecomposable : IsDirectlyIndecomposable 0ℓ 𝑳₃
L3-indecomposable = small→indecomposable 𝑭₃ (from-yes (3 ≤ⁿ? 3)) (from-yes (nontrivial? 𝑭₃))

-- So the kernels are indecomposable congruences of 2 × 3.
θ₂-indecomposable : IsIndecomposable θ₂
θ₂-indecomposable =
  directly→indecomposable θ₂ (≅-indecomposable (≅-sym quotient₂≅L2) L2-indecomposable)

θ₃-indecomposable : IsIndecomposable θ₃
θ₃-indecomposable =
  directly→indecomposable θ₃ (≅-indecomposable (≅-sym quotient₃≅L3) L3-indecomposable)
```
