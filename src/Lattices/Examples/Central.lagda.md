---
layout: default
file: "src/Lattices/Examples/Central.lagda.md"
title: "Lattices.Examples.Central module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Worked examples: central elements and direct decomposability decided

This is the [Lattices.Examples.Central][] module of the [agda-lattices][] library.

The decisions of [Lattices.Central][] are run on six small lattices, and the
theorem of [Lattices.Central.Decomposition][] is applied to the two that
decompose.

+  **`2 × 2`**, the four-element Boolean lattice, is `M 2`{.AgdaFunction} of
   [Lattices.Examples.Mn][]: bottom `0`, atoms `1` and `2`, top `3`.  It is
   not directly indecomposable; each atom is central, with the other as its
   complement; and the theorem gives `2 × 2 ≅ [0, 1] × [1, 3]`.
+  **`2 × 3`** is the six-element table lattice of
   [Lattices.Examples.TwoByThree][], the pair `(i , j)` numbered `3i + j`.
   It is not directly indecomposable.  Its central elements are `0`, `2`,
   `3` and `5`, the pairs `(0, 0)`, `(0, 2)`, `(1, 0)` and `(1, 1)`: every
   element of a distributive lattice is neutral, so what separates them from
   `1` and `4` is having a complement.  The center is the four-element Boolean
   algebra, since `2 × 3` has two indecomposable factors, and its atoms `2`
   and `3` give the factors: `[0, 3] ≅ 2` and `[3, 5] ≅ 3`.  The same lattice
   is then taken as the product `𝟐 ×ˡ 𝟑` of the two chains, with the finite
   structure of [Lattices.Product][], and decided again; there the central
   element `(1 , 0)` is also the one the backward theorem names.
+  **`M₃`** and **`N₅`** are directly indecomposable.  In `M₃` no atom is
   neutral, though each is complemented by either other atom.  In `N₅` the
   three middle elements are all complemented (`b` is a complement of `a` and
   of `c`), and none is neutral, as Grätzer notes after his Definition 2.1.
+  **The chains `2` and `3`** are directly indecomposable, as every chain
   with at least two elements is.

Every verdict is the value of a decision procedure, extracted by `from-yes`
or `from-no`.  The sweep for `isDirectlyIndecomposable?`{.AgdaFunction} on a
lattice of `n` elements decides `n` median identities of `n²` instances each
and searches `n` complements; on these lattices no decision costs more than
35 ms, and the module checks in 0.15 s of its own (measured 2026-10-22, with
`--profile=definitions` and `--profile=modules`).

The module is checked with `--lossy-unification`, which `--safe` accepts.
Without it, the two applications of `central-decomposition`{.AgdaFunction}
below are the whole cost: the type of the isomorphism names the table lattice
through the interval and product constructions, and unifying it with the
theorem's type unfolds the tables; at four elements that took 17 s and
1.6 GB, and at six elements it ran out of memory under an 8 GB cap.  The
decisions alone check in a moment either way.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}

module Lattices.Examples.Central where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F ; 5F )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Level                                  using ( 0ℓ )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic     using ( Lattice )
open import Classical.Properties.Lattice           using ( module Lattice-Order )
open import Setoid.Algebras.Finite                 using ( FiniteAlgebra )
open import Setoid.Homomorphisms.Isomorphisms      using ( _≅_ ; ≅-refl )

-- Imports from this library ----------------------------------------------------
open import Lattices.Central                using ( IsNeutral ; IsComplemented ; IsCentral
                                                  ; IsDirectlyIndecomposable ; ×ˡ-central
                                                  ; isBottom? ; isTop? ; isNeutral? ; isComplemented?
                                                  ; isCentral? ; isDirectlyIndecomposable? )
open import Lattices.Central.Decomposition  using ( central-decomposition ; module Recomposition )
open import Lattices.Examples.M3            using ( M₃ ; M₃-finite )
open import Lattices.Examples.Mn            using ( M ; M-finite )
open import Lattices.Examples.N5            using ( N₅ ; N₅-finite )
open import Lattices.Examples.TwoByThree    using ( _∧₂_ ; _∨₂_ ; laws₂ ; _∧₃_ ; _∨₃_ ; laws₃
                                                  ; _∧_ ; _∨_ ; laws₆ )
open import Lattices.Product                using ( _×ˡ_ ; module Product )
open import Lattices.Interval               using ( _[_,_] )
open import Lattices.Table                  using ( tableLattice ; tableLattice-FiniteAlgebra )
```
-->

#### The lattices

[Lattices.Examples.TwoByThree][] keeps the chains and `2 × 3` as algebras over
the lattice signature; here they are the lattices the tables make.

```agda
𝟐 𝟑 𝟐×𝟑 : Lattice 0ℓ 0ℓ
𝟐 = tableLattice _∧₂_ _∨₂_ laws₂
𝟑 = tableLattice _∧₃_ _∨₃_ laws₃
𝟐×𝟑 = tableLattice _∧_ _∨_ laws₆

𝟐-finite : FiniteAlgebra (proj₁ 𝟐)
𝟐-finite = tableLattice-FiniteAlgebra _∧₂_ _∨₂_ laws₂

𝟑-finite : FiniteAlgebra (proj₁ 𝟑)
𝟑-finite = tableLattice-FiniteAlgebra _∧₃_ _∨₃_ laws₃

𝟐×𝟑-finite : FiniteAlgebra (proj₁ 𝟐×𝟑)
𝟐×𝟑-finite = tableLattice-FiniteAlgebra _∧_ _∨_ laws₆

-- The product of the chains, with the finite structure of Lattices.Product.
𝟐×ˡ𝟑-finite : FiniteAlgebra (proj₁ (𝟐 ×ˡ 𝟑))
𝟐×ˡ𝟑-finite = Product.×ˡ-finite 𝟐 𝟑 𝟐-finite 𝟑-finite
```

#### `2 × 2`

The atom `1` is central, and the lattice decomposes along it.

```agda
M2-decomposable : ¬ IsDirectlyIndecomposable (M 2)
M2-decomposable = from-no (isDirectlyIndecomposable? (M 2) (M-finite 2))

M2-central : IsCentral (M 2) 1F
M2-central = from-yes (isCentral? (M 2) (M-finite 2) 1F)

M2≅[0,1]×[1,3] : proj₁ (M 2) ≅ proj₁ (M 2 [ 0F , 1F ] ×ˡ M 2 [ 1F , 3F ])
M2≅[0,1]×[1,3] = central-decomposition (M 2)
  (from-yes (isBottom? (M 2) (M-finite 2) 0F)) (from-yes (isTop? (M 2) (M-finite 2) 3F)) M2-central
```

#### `2 × 3` as a table

The center is `{0, 2, 3, 5}`; `1` and `4` are neutral and not complemented.
The decomposition along the atom `3 = (1 , 0)` of the center has the factors
`[0, 3]`, the two-element chain `{0, 3}`, and `[3, 5]`, the three-element
chain `{3, 4, 5}`.

```agda
𝟐×𝟑-decomposable : ¬ IsDirectlyIndecomposable 𝟐×𝟑
𝟐×𝟑-decomposable = from-no (isDirectlyIndecomposable? 𝟐×𝟑 𝟐×𝟑-finite)

𝟐×𝟑-central-0 : IsCentral 𝟐×𝟑 0F
𝟐×𝟑-central-0 = from-yes (isCentral? 𝟐×𝟑 𝟐×𝟑-finite 0F)

𝟐×𝟑-central-2 : IsCentral 𝟐×𝟑 2F
𝟐×𝟑-central-2 = from-yes (isCentral? 𝟐×𝟑 𝟐×𝟑-finite 2F)

𝟐×𝟑-central-3 : IsCentral 𝟐×𝟑 3F
𝟐×𝟑-central-3 = from-yes (isCentral? 𝟐×𝟑 𝟐×𝟑-finite 3F)

𝟐×𝟑-central-5 : IsCentral 𝟐×𝟑 5F
𝟐×𝟑-central-5 = from-yes (isCentral? 𝟐×𝟑 𝟐×𝟑-finite 5F)

𝟐×𝟑-neutral-1 : IsNeutral 𝟐×𝟑 1F
𝟐×𝟑-neutral-1 = from-yes (isNeutral? 𝟐×𝟑 𝟐×𝟑-finite 1F)

𝟐×𝟑-not-complemented-1 : ¬ IsComplemented 𝟐×𝟑 1F
𝟐×𝟑-not-complemented-1 = from-no (isComplemented? 𝟐×𝟑 𝟐×𝟑-finite 1F)

𝟐×𝟑-not-complemented-4 : ¬ IsComplemented 𝟐×𝟑 4F
𝟐×𝟑-not-complemented-4 = from-no (isComplemented? 𝟐×𝟑 𝟐×𝟑-finite 4F)

𝟐×𝟑≅[0,3]×[3,5] : proj₁ 𝟐×𝟑 ≅ proj₁ (𝟐×𝟑 [ 0F , 3F ] ×ˡ 𝟐×𝟑 [ 3F , 5F ])
𝟐×𝟑≅[0,3]×[3,5] = central-decomposition 𝟐×𝟑
  (from-yes (isBottom? 𝟐×𝟑 𝟐×𝟑-finite 0F)) (from-yes (isTop? 𝟐×𝟑 𝟐×𝟑-finite 5F)) 𝟐×𝟑-central-3
```

#### `2 × 3` as a product of chains

The sweep runs on the product lattice through the finite structure of
[Lattices.Product][].  The central element `(1 , 0)` is both decided and given
by `×ˡ-central`{.AgdaFunction}; and the backward theorem, at the identity
isomorphism, refutes indecomposability without a sweep, from the bounds of
the chains and the fact that neither chain is trivial.

```agda
𝟐×ˡ𝟑-decomposable : ¬ IsDirectlyIndecomposable (𝟐 ×ˡ 𝟑)
𝟐×ˡ𝟑-decomposable = from-no (isDirectlyIndecomposable? (𝟐 ×ˡ 𝟑) 𝟐×ˡ𝟑-finite)

𝟐×ˡ𝟑-central : IsCentral (𝟐 ×ˡ 𝟑) (1F , 0F)
𝟐×ˡ𝟑-central = from-yes (isCentral? (𝟐 ×ˡ 𝟑) 𝟐×ˡ𝟑-finite (1F , 0F))

𝟐-bottom : Lattice-Order.IsBottom 𝟐 0F
𝟐-bottom = from-yes (isBottom? 𝟐 𝟐-finite 0F)

𝟐-top : Lattice-Order.IsTop 𝟐 1F
𝟐-top = from-yes (isTop? 𝟐 𝟐-finite 1F)

𝟑-bottom : Lattice-Order.IsBottom 𝟑 0F
𝟑-bottom = from-yes (isBottom? 𝟑 𝟑-finite 0F)

𝟑-top : Lattice-Order.IsTop 𝟑 2F
𝟑-top = from-yes (isTop? 𝟑 𝟑-finite 2F)

𝟐×ˡ𝟑-central′ : IsCentral (𝟐 ×ˡ 𝟑) (1F , 0F)
𝟐×ˡ𝟑-central′ = ×ˡ-central 𝟐 𝟑 𝟐-bottom 𝟐-top 𝟑-bottom 𝟑-top

𝟐×ˡ𝟑-decomposable′ : ¬ IsDirectlyIndecomposable (𝟐 ×ˡ 𝟑)
𝟐×ˡ𝟑-decomposable′ =
  Recomposition.decomposable (𝟐 ×ˡ 𝟑) 𝟐 𝟑 ≅-refl 𝟐-bottom 𝟐-top 𝟑-bottom 𝟑-top (λ ()) (λ ())
```

#### `M₃`, `N₅`, and the chains

In `M₃` (elements `⊥, a, b, c, ⊤` numbered `0` to `4`) the atom `a = 1` is
complemented and not neutral; in `N₅` (`⊥ < a < c < ⊤` and `⊥ < b < ⊤`,
numbered `0, 1, 3, 4` and `2`) each middle element is complemented and not
neutral.

```agda
M₃-indecomposable : IsDirectlyIndecomposable M₃
M₃-indecomposable = from-yes (isDirectlyIndecomposable? M₃ M₃-finite)

M₃-a-not-neutral : ¬ IsNeutral M₃ 1F
M₃-a-not-neutral = from-no (isNeutral? M₃ M₃-finite 1F)

M₃-a-complemented : IsComplemented M₃ 1F
M₃-a-complemented = from-yes (isComplemented? M₃ M₃-finite 1F)

N₅-indecomposable : IsDirectlyIndecomposable N₅
N₅-indecomposable = from-yes (isDirectlyIndecomposable? N₅ N₅-finite)

N₅-a-not-neutral : ¬ IsNeutral N₅ 1F
N₅-a-not-neutral = from-no (isNeutral? N₅ N₅-finite 1F)

N₅-b-not-neutral : ¬ IsNeutral N₅ 2F
N₅-b-not-neutral = from-no (isNeutral? N₅ N₅-finite 2F)

N₅-c-not-neutral : ¬ IsNeutral N₅ 3F
N₅-c-not-neutral = from-no (isNeutral? N₅ N₅-finite 3F)

N₅-a-complemented : IsComplemented N₅ 1F
N₅-a-complemented = from-yes (isComplemented? N₅ N₅-finite 1F)

N₅-b-complemented : IsComplemented N₅ 2F
N₅-b-complemented = from-yes (isComplemented? N₅ N₅-finite 2F)

N₅-c-complemented : IsComplemented N₅ 3F
N₅-c-complemented = from-yes (isComplemented? N₅ N₅-finite 3F)

𝟐-indecomposable : IsDirectlyIndecomposable 𝟐
𝟐-indecomposable = from-yes (isDirectlyIndecomposable? 𝟐 𝟐-finite)

𝟑-indecomposable : IsDirectlyIndecomposable 𝟑
𝟑-indecomposable = from-yes (isDirectlyIndecomposable? 𝟑 𝟑-finite)
```

--------------------------------------

[Lattices.Examples.Central]: Lattices.Examples.Central.html
[Lattices.Central]: Lattices.Central.html
[Lattices.Central.Decomposition]: Lattices.Central.Decomposition.html
[Lattices.Examples.Mn]: Lattices.Examples.Mn.html
[Lattices.Examples.TwoByThree]: Lattices.Examples.TwoByThree.html
[Lattices.Product]: Lattices.Product.html
