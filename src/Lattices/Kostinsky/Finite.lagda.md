---
layout: default
file: "src/Lattices/Kostinsky/Finite.lagda.md"
title: "Lattices.Kostinsky.Finite module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### The finite case: a finite bounded lattice with (W) is a sublattice of a free lattice

This is the [Lattices.Kostinsky.Finite][] module of the [agda-lattices][] library.

[Freese, Ježek, and Nation (1995)][], Lemma 5.35, (3) implies (2): a finite
bounded lattice satisfying Whitman's condition (W) is a sublattice of a free
lattice.  This is the finite case of Kostinsky's theorem ([Lattices.Kostinsky][])
and the step of the proof of Nation's theorem (Theorem 5.55) that follows
Nation's own argument; the book reaches it through Corollaries 5.9 to 5.11,
and the record `NationsTheorem`{.AgdaRecord} of [Lattices.Nation][] rests on
it.  This module proves it in two forms.

+  **For a lattice with a finite enumeration** (a `FiniteAlgebra`{.AgdaRecord}
   of its algebra): if `D(L) = L = Dᵈ(L)` ([Lattices.Bounded.Covers][]) and
   `L` satisfies (W), then `L` embeds in `FL(card)`, the free lattice on as
   many generators as the enumeration has, and hence in `FL(3)` by Whitman's
   Theorem 1.28 ([Lattices.Free.Countable][]).  The enumeration is the
   epimorphism `FL(card) → L`, the decidable equality decides the order,
   [Lattices.Bounded.Preimage][] turns `D(L) = L = Dᵈ(L)` into the least and
   greatest preimages, and Kostinsky's proof gives the section.  An empty
   lattice embeds in the empty free lattice `FL(0)`, vacuously.
+  **For a table lattice** ([Lattices.Table][]) with
   [Lattices.Bounded.Finite][]'s boundedness, the absence of a D-cycle and of
   a dual cycle (the right-hand side of the book's Corollary 2.39): no D-cycle
   gives `D(L) = L`, by well-founded induction along the relation `D` with the
   minimal join covers of that module, whose members are dependencies of the
   element covered and so have smaller D-rank
   (`lowerBounded→D-total`{.AgdaFunction}, one half of Corollary 2.39); the
   dual table lattice gives `Dᵈ(L) = L` the same way; and the first form
   applies with the identity enumeration (`table-embeds`{.AgdaFunction},
   `table-embedsFL3`{.AgdaFunction}).  The other half of Corollary 2.39, that
   `D(L) = L` excludes a D-cycle, is not proved here.

The hypotheses are decidable on a table lattice: `bounded?`{.AgdaFunction} of
[Lattices.Bounded.Finite][] and `satisfiesW?`{.AgdaFunction} of
[Lattices.Semidistributive][] decide them, so a positive verdict on a concrete
table yields an explicit embedding into `FL(3)`, with no hypothesis.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Kostinsky.Finite where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; suc )
open import Data.Fin.Patterns                      using ( 0F )
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Relation.Unary.All           using ( All ; head )
open import Data.List.Relation.Unary.Any           using ( Any )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product                           using ( ∃ ; Σ-syntax ; _×_ ; _,_ ; proj₁ )
open import Function                               using ( flip )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; cong ; subst )
open import Relation.Nullary                       using ( Dec )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )
open import Setoid.Functions                    using ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms.Basic          using ( mkhom )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Covers     using ( D ; D-total ; Dᵈ-total ; D-≤ ; _≪_ )
open import Lattices.Bounded.Preimage   using ( bounded )
open import Lattices.Dual               using ( dualLattice )
open import Lattices.Free.Countable     using ( finite-embedding )
open import Lattices.Free.Term          using ( ℊ )
open import Lattices.Free.Universal     using ( FL ; FL-extend )
open import Lattices.Generation         using ( _≤⋁_ ; ≤⋁⁺ )
                                        renaming ( ⋁⁺ to ⋁⁺ᴸ ; ⋁⁺-upper to ⋁⁺ᴸ-upper ; ⋁⁺-least to ⋁⁺ᴸ-least )
open import Lattices.Kostinsky          using ( module HardDirection )
open import Lattices.Nation             using ( Embeds )
open import Lattices.Semidistributive   using ( SatisfiesW )
open import Lattices.Table              using ( LatticeTableLaws ; tableLattice )

import Lattices.Bounded.Finite as Finite

private variable αᴸ ρᴸ αᴹ ρᴹ αᴺ ρᴺ : Level
```
-->

#### Lattices with a finite enumeration

Embeddings compose, and an empty lattice embeds in `FL(0)`: every component
of the embedding is a function out of the empty carrier.

```agda
module _ (𝑳 : Lattice αᴸ ρᴸ) where
  open Lattice-Op 𝑳         using ( _∧_ )
  open Lattice-Order 𝑳      using ( _≤_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ) renaming ( sym to ≈sym )

  -- Embeddings compose.
  Embeds-trans : {𝑴 : Lattice αᴹ ρᴹ} {𝑵 : Lattice αᴺ ρᴺ} → Embeds 𝑳 𝑴 → Embeds 𝑴 𝑵 → Embeds 𝑳 𝑵
  Embeds-trans (j , j-inj) (h , h-inj) = ⊙-hom j h , λ e → j-inj (h-inj e)

  -- An empty lattice embeds in FL(0).
  empty-embeds : (𝕌[ proj₁ 𝑳 ] → ⊥) → Embeds 𝑳 (FL (Fin 0))
  empty-embeds e =
    mkhom (proj₁ 𝑳) (proj₁ (FL (Fin 0)))
          (record { to = λ a → ⊥-elim (e a) ; cong = λ {a} _ → ⊥-elim (e a) })
          (λ { {∧-Op} {a} → ⊥-elim (e (a 0F)) ; {∨-Op} {a} → ⊥-elim (e (a 0F)) })
    , λ {a} _ → ⊥-elim (e a)
```

For an enumeration of `n` elements that hits every element, the extension of
the enumeration is an epimorphism `FL(n) → 𝑳`.  With `n = 0` the lattice is
empty; otherwise `D(L) = L = Dᵈ(L)` and the decided order give the bounds, and
Kostinsky's hard direction embeds `𝑳`{.AgdaBound} in `FL(n)`.

```agda
  module _ (_≤?_ : ∀ a b → Dec (a ≤ b)) where

    -- Lemma 5.35, (3) ⇒ (2), for an enumeration of n elements.
    embeds-of-enum : ∀ n (enum : Fin n → 𝕌[ proj₁ 𝑳 ]) → (∀ a → ∃ λ i → enum i ≈ a)
                   → D-total 𝑳 → Dᵈ-total 𝑳 → SatisfiesW 𝑳 → Embeds 𝑳 (FL (Fin n))
    embeds-of-enum zero     enum sur _  _   _ = empty-embeds λ a → no-element (proj₁ (sur a))
      where
      no-element : Fin 0 → ⊥
      no-element ()
    embeds-of-enum (suc m)  enum sur dt dtᵈ W =
      HardDirection.embeds 𝑳 enum onto (bounded 𝑳 _≤?_ enum onto dt dtᵈ) W
      where
      onto : IsSurjective (FL-extend 𝑳 enum)
      onto {a} = let (i , e) = sur a in Image_∋_.eq (ℊ i) (≈sym e)
```

A `FiniteAlgebra`{.AgdaRecord} supplies the enumeration and the decidable
equality, which decides the order.  The embedding lands in `FL(card)`, and in
`FL(3)` through Theorem 1.28.

```agda
  module _ (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
    open FiniteAlgebra 𝑭 using ( _≟_ ; card ; enum ; enum-sur )

    private
      _≤?_ : ∀ a b → Dec (a ≤ b)
      a ≤? b = (a ∧ b) ≟ a

    -- Lemma 5.35, (3) ⇒ (2): a finite lattice with D(L) = L = Dᵈ(L) and (W) embeds in FL(card).
    finite-embeds : D-total 𝑳 → Dᵈ-total 𝑳 → SatisfiesW 𝑳 → Embeds 𝑳 (FL (Fin card))
    finite-embeds = embeds-of-enum _≤?_ card enum enum-sur

    -- And in FL(3), by Theorem 1.28.
    finite-embedsFL3 : D-total 𝑳 → Dᵈ-total 𝑳 → SatisfiesW 𝑳 → Embeds 𝑳 (FL (Fin 3))
    finite-embedsFL3 dt dtᵈ W =
      Embeds-trans {𝑴 = FL (Fin card)} {𝑵 = FL (Fin 3)} (finite-embeds dt dtᵈ W) (finite-embedding card)
```

#### Table lattices: no D-cycle gives `D(L) = L`

Fix a table lattice on `Fin (suc n)`, with [Lattices.Bounded.Finite][]'s join
dependency relation `D`, its D-rank `ρ` on a lattice with no D-cycle, and its
minimal join covers.  The joins of nonempty lists of [Lattices.Generation][]
and the list joins of that module agree (`⋁⁺≤⋁`{.AgdaFunction},
`⋁≤⋁⁺`{.AgdaFunction}).  Then every `a` lies in `D_{ρ(a)+1}(L)`, by
well-founded induction along `D`: a nontrivial join cover `S` of `a` refines
to a minimal one, `Q`, of elements `q` with `a D q`, each of which lies in
`D_{ρ(q)+1} ⊆ D_{ρ(a)}` by the induction hypothesis and the descent of the
rank; `Q` is empty only when `a` is the least element, which has no nontrivial
cover.

```agda
module TableD {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
              (laws : LatticeTableLaws _∧_ _∨_) where
  private
    T : Lattice 0ℓ 0ℓ
    T = tableLattice _∧_ _∨_ laws

  open Finite.JoinDependency laws
    using ( _D_ ; LowerBounded ; D-acc ; ρ ; ρ-decreasing ; minimal-cover ; MinimalJoinCover
          ; ⋁ ; ∨*-upper ; ∨*-least ; ⊥ᴸ ; ⊥ᴸ-least ; _≤_ ; ≤-trans )

  -- The two forms of the join of a nonempty list agree.
  ⋁⁺≤⋁ : ∀ s ss → ⋁⁺ᴸ T s ss ≤ ⋁ (s ∷ ss)
  ⋁⁺≤⋁ s ss = ⋁⁺ᴸ-least T {b = s} {bs = ss} λ u∈ → ∨*-upper {cs = s ∷ ss} {z = ⊥ᴸ} u∈

  ⋁≤⋁⁺ : ∀ s ss → ⋁ (s ∷ ss) ≤ ⋁⁺ᴸ T s ss
  ⋁≤⋁⁺ s ss = ∨*-least {cs = s ∷ ss} {z = ⊥ᴸ} (All.tabulate {xs = s ∷ ss} λ u∈ → ⋁⁺ᴸ-upper T {b = s} {bs = ss} u∈) (⊥ᴸ-least _)

  -- With no D-cycle, every a lies in D_{ρ(a)+1}: well-founded induction along D.
  no-cycle→D : (lb : LowerBounded) → ∀ a → Acc (flip _D_) a → D T (suc (ρ lb a)) a
  no-cycle→D lb a (acc rs) S (≤⋁⁺ {s} {ss} a≤S) nt =
    from-cover (MinimalJoinCover.cover C) (MinimalJoinCover.joins C)
               (MinimalJoinCover.refines C) (MinimalJoinCover.dependencies C)
    where
    C : MinimalJoinCover a (s ∷ ss)
    C = minimal-cover a (s ∷ ss) (≤-trans a≤S (⋁⁺≤⋁ s ss)) nt

    -- The minimal cover is the refinement; its members, dependencies of a, lie in D_{ρ(a)}.
    from-cover : (Q : List (Fin (suc n))) → a ≤ ⋁ Q → All (λ q → Any (q ≤_) (s ∷ ss)) Q → All (a D_) Q
               → Σ[ Q′ ∈ List (Fin (suc n)) ] (_≪_ T Q′ (s ∷ ss)) × All (D T (ρ lb a)) Q′ × _≤⋁_ T a Q′
    from-cover []        a≤⊥  _    _     = ⊥-elim (head nt (≤-trans a≤⊥ (⊥ᴸ-least s)))
    from-cover (q ∷ qs)  a≤Q  Q≪S  deps  =
      q ∷ qs , Q≪S
      , All.map (λ {u} aDu → D-≤ T (ρ lb a) (ρ-decreasing lb aDu) (no-cycle→D lb u (rs aDu))) deps
      , ≤⋁⁺ (≤-trans a≤Q (⋁≤⋁⁺ q qs))

  -- Corollary 2.39, one half: a finite lattice with no D-cycle has D(L) = L.
  lowerBounded→D-total : LowerBounded → D-total T
  lowerBounded→D-total lb a = suc (ρ lb a) , no-cycle→D lb a (D-acc lb a)
```

#### Table lattices: the dual, and the embedding

The dual of a pair of tables is the pair swapped, and its join dependency
relation is the meet dependency relation of the original
([Lattices.Bounded.Finite][]); its lattice has the carrier and the operations
of the dual lattice of [Lattices.Dual][], so membership
in the sets `D_k` transfers between the two (`D-same`{.AgdaFunction}), and
the absence of a dual cycle gives `Dᵈ(L) = L`.  With both halves, the finite
case of Kostinsky's theorem for a table lattice follows from the enumeration
form with the identity enumeration.

```agda
module _ {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
         (laws : LatticeTableLaws _∧_ _∨_) where
  private
    T : Lattice 0ℓ 0ℓ
    T = tableLattice _∧_ _∨_ laws

    -- The dual table lattice, and the dual lattice of T: the same carrier and operations.
    Tᵈ : Lattice 0ℓ 0ℓ
    Tᵈ = tableLattice _∨_ _∧_ (Finite.dual-laws laws)

    Tᵒ : Lattice 0ℓ 0ℓ
    Tᵒ = dualLattice T

    -- Their joins of nonempty lists agree.
    ⋁⁺-same : ∀ s ss → ⋁⁺ᴸ Tᵈ s ss ≡ ⋁⁺ᴸ Tᵒ s ss
    ⋁⁺-same s []         = refl
    ⋁⁺-same s (s' ∷ ss)  = cong (s ∧_) (⋁⁺-same s' ss)

    -- Membership in D_k transfers from the dual table lattice to the dual lattice.
    D-same : ∀ k {a} → D Tᵈ k a → D Tᵒ k a
    D-same zero     jp = jp
    D-same (suc k)  d  S (≤⋁⁺ {s} {ss} p) nt =
      let (Q , Q≪S , allQ , a≤Q) = d S (≤⋁⁺ (subst (Lattice-Order._≤_ Tᵈ _) (sym (⋁⁺-same s ss)) p)) nt
      in Q , Q≪S , All.map (D-same k) allQ , convert a≤Q
      where
      convert : ∀ {a Q} → _≤⋁_ Tᵈ a Q → _≤⋁_ Tᵒ a Q
      convert (≤⋁⁺ {t} {ts} q) = ≤⋁⁺ (subst (Lattice-Order._≤_ Tᵒ _) (⋁⁺-same t ts) q)

  -- Corollary 2.39, one half, dualized: a finite lattice with no dual cycle has Dᵈ(L) = L.
  upperBounded→Dᵈ-total : Finite.UpperBounded laws → Dᵈ-total T
  upperBounded→Dᵈ-total ub a =
    let (k , d) = TableD.lowerBounded→D-total (Finite.dual-laws laws) ub a in k , D-same k d

  -- Lemma 5.35, (3) ⇒ (2), for a table lattice: bounded with (W) embeds in FL(suc n).
  table-embeds : Finite.Bounded laws → SatisfiesW T → Embeds T (FL (Fin (suc n)))
  table-embeds (lb , ub) W =
    embeds-of-enum T (Finite.JoinDependency._≤?_ laws) (suc n) (λ i → i) (λ a → a , refl)
                   (TableD.lowerBounded→D-total laws lb) (upperBounded→Dᵈ-total ub) W

  -- And in FL(3).
  table-embedsFL3 : Finite.Bounded laws → SatisfiesW T → Embeds T (FL (Fin 3))
  table-embedsFL3 bd W = Embeds-trans T {𝑴 = FL (Fin (suc n))} {𝑵 = FL (Fin 3)} (table-embeds bd W) (finite-embedding (suc n))
```

The module checks in about a second of its own.
