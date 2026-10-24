---
layout: default
file: "src/Lattices/Nation/Kappa.lagda.md"
title: "Lattices.Nation.Kappa module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### The map κ and Jónsson's relations in a finite semidistributive lattice

This is the [Lattices.Nation.Kappa][] module of the [agda-lattices][] library.

In a finite lattice `L`, a join irreducible element `a` has one lower cover
`a₋`, and `K(a)` is the set of elements above `a₋` and not above `a`
([Freese, Ježek, and Nation (1995)][], p. 49).  When `K(a)` has a largest
element, that element is `κ(a)`; and a finite lattice satisfies (SD∧) exactly
when `κ(a)` exists for every join irreducible `a` (Theorem 2.56, p. 50).  On
`κ` Jónsson defined the relations `A` and `B` on the join irreducible elements
(p. 51), whose union `C` is the relation whose cycles Nation's theorem is
about.  This module develops that vocabulary, FJN Section II.5 read for a
finite lattice, on the table lattices of [Lattices.Table][], under the finite
D theory of [Lattices.Bounded.Finite][] and the library's own semidistributive
laws at the table lattice.  It supplies the following:

+  **`κ`** (`κ`{.AgdaFunction}), defined for every element as the join of
   `K(a)` over the base `a₋`.  Under (SD∧), for `a` join irreducible, `a` meets
   `κ(a)` in `a₋` (`a∧κ`{.AgdaFunction}): the meet semidistributive law, folded
   along the list `K(a)`, is the half of Theorem 2.56 the proof uses, and the
   other half is not needed.  So `κ(a)` is the largest element of `K(a)`
   (`a≰κ`{.AgdaFunction}, `K≤κ`{.AgdaFunction}), and Lemma 2.57 (p. 51) reads
   `u ≤ κ(a)` exactly when `a ≰ a₋ ∨ u` (`≤κ→`{.AgdaFunction},
   `→≤κ`{.AgdaFunction}).
+  **The upper cover of `κ(a)`** (`κ<→≤`{.AgdaFunction},
   `below-cover`{.AgdaFunction}): every element strictly above `κ(a)` is above
   `a`, so `a ∨ κ(a)` is the one upper cover of `κ(a)` (p. 50); and, by (SD∨),
   an element below `a ∨ κ(a)` and not below `κ(a)` is above `a`.
+  **Jónsson's relations** (`_A_`{.AgdaFunction}, `_B_`{.AgdaFunction},
   `_C_`{.AgdaFunction}), decided, each carrying the join irreducibility of
   its two arguments, so that a C-cycle is a sequence of join irreducible
   elements by its type; the subdivisions `A₁`, `A₂`, `B₁`, `B₂` of p. 110,
   exhaustive (`A→A₁⊎A₂`{.AgdaFunction}, `B→B₁⊎B₂`{.AgdaFunction}); the
   rewriting of `B` through `κ` (p. 51 and p. 109: `a B b` exactly when
   `a ≠ b`, `b₋ ≤ κ(a)` and `b ≰ κ(a)`); and Lemma 2.58 (`B→≤κ`{.AgdaFunction}),
   `a B b` implies `a ≤ κ(b)`.  The book proves Lemma 2.58 by the strong form
   of (SD∨), Theorem 1.21; here the binary law suffices, applied with the
   common joinand `a₋ ∨ b₋`.
+  **Duality** (`KappaDuality`{.AgdaModule}).  The dual of a table lattice is
   the pair of tables swapped (`dual-laws`{.AgdaFunction}), so the dual
   lattice's `κ`, `A`, `B` and `C` are the same definitions at the swapped
   tables, with the swapped pair of semidistributive laws.  The module relates
   the two instances: `x⁺`, the dual's `x₋`, is the meet of the elements
   strictly above `x`; `κ(a)` has one upper
   cover, namely `a ∨ κ(a)` (`κ⁺`{.AgdaFunction}); `κᵈ(κ(a)) = a` for every join
   irreducible `a` (`κᵈκ`{.AgdaFunction}, the half of Corollary 2.55 the proofs
   use, so `κ` is injective on `J(L)`); and Nation's duality, Lemma 2.63
   (p. 53): `a A b` exactly when `κ(a) Bᵈ κ(b)`, and `a B b` exactly when
   `κ(a) Aᵈ κ(b)`.

Everything is a decision or a case split on one, and nothing classical is
used.    Nation's paper ("Finite sublattices of a free lattice", 1982) states the
same vocabulary in its Section 1 (Lemma 1.1 is Lemma 2.57 with `κ(p)* = p ∨ κ(p)`,
and Lemma 1.3 is Lemma 2.63); the module follows the book's order.

The module checks in 2.0 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Kappa where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; filter ; allFin )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-allFin )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; ¬? ; _×-dec_ ; _⊎-dec_
                                                         ; decidable-stable )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Finite    using ( module JoinDependency ; dual-laws )
open import Lattices.Nation.Order      using ( module Order )
open import Lattices.Semidistributive  using ( IsSemidistributive )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

#### The lattice, and the order lemmas the development uses

The rest of the module is about one table lattice on `Fin (suc n)`, given by its
tables and their laws, with both semidistributive laws as the library states
them at that lattice.  `Kappa`{.AgdaModule} opens `JoinDependency laws` of
[Lattices.Bounded.Finite][] publicly, so that a client of the vocabulary opens
one module and sees the order, the lower covers, the D relation and `κ` together;
and opens [Lattices.Nation.Order][] publicly for the monotonicity and absorption
lemmas the proofs use at every turn.

```agda
module Kappa {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
             (laws : LatticeTableLaws _∧_ _∨_)
             (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open JoinDependency laws public
  open Order laws public

  -- The two semidistributive laws, with the table lattice's equality, which is _≡_.
  sd∨ : ∀ a b c → a ∨ b ≡ a ∨ c → a ∨ b ≡ a ∨ (b ∧ c)
  sd∨ = proj₁ sd

  sd∧ : ∀ a b c → a ∧ b ≡ a ∧ c → a ∧ b ≡ a ∧ (b ∨ c)
  sd∧ = proj₂ sd
```

#### `K(a)` and `κ(a)`

`K a`{.AgdaFunction} lists the elements above `a ₋` and not above `a`, and
`κ a`{.AgdaFunction} is their join over the base `a ₋`, so that `κ a` is `a ₋`
itself when the list is empty.  Nothing here needs `a` to be join irreducible;
the theorems below do.

```agda
  -- Membership in K a is decidable.
  K? : ∀ a u → Dec (a ₋ ≤ u × ¬ a ≤ u)
  K? a u = a ₋ ≤? u ×-dec ¬? (a ≤? u)

  -- K a: the elements above a ₋ and not above a (FJN p. 49).
  K : Fin (suc n) → List (Fin (suc n))
  K a = filter (K? a) (allFin (suc n))

  ∈K⁺ : ∀ {a u} → a ₋ ≤ u → ¬ a ≤ u → u ∈ K a
  ∈K⁺ {a} {u} a₋≤u a≰u = ∈-filter⁺ (K? a) (∈-allFin u) (a₋≤u , a≰u)

  ∈K⁻ : ∀ {a u} → u ∈ K a → a ₋ ≤ u × ¬ a ≤ u
  ∈K⁻ {a} u∈ = proj₂ (∈-filter⁻ (K? a) u∈)

  -- κ a: the join of K a over the base a ₋.
  κ : Fin (suc n) → Fin (suc n)
  κ a = K a ∨* a ₋

  ₋≤κ : ∀ a → a ₋ ≤ κ a
  ₋≤κ a = ∨*-base (K a)

  K≤κ : ∀ {a u} → u ∈ K a → u ≤ κ a
  K≤κ {a} u∈ = ∨*-upper {cs = K a} u∈
```

#### Theorem 2.56, the half that is used, and Lemma 2.57

Fix a join irreducible `a`.  Every `u` in `K a` meets `a` in `a ₋`
(`K-meet`{.AgdaFunction}): the meet lies below `a` and differs from it, so it
lies below the one lower cover, and it lies above `a ₋` by the choice of `u`.
The meet semidistributive law then folds along the list: if `a ∧ c = a ₋ = a ∧ r`
then `a ∧ (c ∨ r) = a ∧ c` (`meet-fold`{.AgdaFunction}), so `a ∧ κ a = a ₋`
(`a∧κ`{.AgdaFunction}), and `a ≰ κ a` since `a ≠ a ₋`.  So `κ a` lies in `K a`
and above every member of it: it is the largest element of `K(a)`, which is the
book's `κ(a)`, and this is the direction of Theorem 2.56 that the development
uses.  Lemma 2.57 follows: `u ≤ κ a` if and only if `a ≰ (a ₋) ∨ u`, since `(a ₋) ∨ u`
lies in `K a` exactly when `a ≰ (a ₋) ∨ u`.

```agda
  module _ {a : Fin (suc n)} (one : HasOneLowerCover a) where

    -- A member of K a meets a in a ₋.
    K-meet : ∀ {u} → u ∈ K a → a ∧ u ≡ a ₋
    K-meet {u} u∈ = ≤-antisym (<→≤₋′ ∧-lowerˡ (proj₂ (∈K⁻ u∈))) (∧-greatest (₋≤ a) (proj₁ (∈K⁻ u∈)))

    -- (SD∧), folded: a meets a join of elements each meeting a in a ₋ in a ₋.
    meet-fold : ∀ cs {z} → All (λ u → a ∧ u ≡ a ₋) cs → a ∧ z ≡ a ₋ → a ∧ (cs ∨* z) ≡ a ₋
    meet-fold []        []          z≡ = z≡
    meet-fold (c ∷ cs)  (c≡ ∷ cs≡)  z≡ =
      trans (sym (sd∧ a c (cs ∨* _) (trans c≡ (sym (meet-fold cs cs≡ z≡))))) c≡

    -- a ∧ κ a ≡ a ₋.
    a∧κ : a ∧ κ a ≡ a ₋
    a∧κ = meet-fold (K a) (All.tabulate K-meet) (≤-antisym ∧-lowerʳ (∧-greatest (₋≤ a) ≤-refl))

    -- a ≰ κ a: κ a lies in K a.
    a≰κ : ¬ a ≤ κ a
    a≰κ a≤κ = proj₂ one (sym (trans (sym a≤κ) a∧κ))

    -- Lemma 2.57: u ≤ κ a if and only if a ≰ (a ₋) ∨ u.
    ≤κ→ : ∀ {u} → u ≤ κ a → ¬ a ≤ (a ₋) ∨ u
    ≤κ→ u≤κ a≤ = a≰κ (≤-trans a≤ (∨-least (₋≤κ a) u≤κ))

    →≤κ : ∀ {u} → ¬ a ≤ (a ₋) ∨ u → u ≤ κ a
    →≤κ a≰ = ≤-trans ∨-upperʳ (K≤κ (∈K⁺ ∨-upperˡ a≰))

    -- The contrapositive forms.
    ≰κ→ : ∀ {u} → ¬ u ≤ κ a → a ≤ (a ₋) ∨ u
    ≰κ→ {u} u≰κ = decidable-stable (a ≤? (a ₋) ∨ u) λ a≰ → u≰κ (→≤κ a≰)

    →≰κ : ∀ {u} → a ≤ (a ₋) ∨ u → ¬ u ≤ κ a
    →≰κ a≤ u≤κ = ≤κ→ u≤κ a≤
```

#### The upper cover of `κ(a)`

An element `v` strictly above `κ a` is above `a`: otherwise `v` lies in `K a`,
hence below `κ a` (`κ<→≤`{.AgdaFunction}).  So every element strictly above
`κ a` is above `a ∨ κ a`, which is therefore the one upper cover of `κ a`, the
book's `κ(a)*` (p. 50); the duality section below says so in the dual's
vocabulary.  Conversely, an element `v` below `a ∨ κ a` and not below `κ a` is
above `a` (`below-cover`{.AgdaFunction}): `κ a ∨ v` is strictly above `κ a`,
hence equals `κ a ∨ a`, and (SD∨) gives `κ a ∨ a = κ a ∨ (a ∧ v)`; if `a ≰ v`,
then `a ∧ v` lies below `a ₋`, hence below `κ a`, and `a ≤ κ a` would follow.

```agda
    -- An element strictly above κ a is above a.
    κ<→≤ : ∀ {v} → κ a < v → a ≤ v
    κ<→≤ {v} (κ≤v , κ≢v) =
      decidable-stable (a ≤? v) λ a≰v → κ≢v (≤-antisym κ≤v (K≤κ (∈K⁺ (≤-trans (₋≤κ a) κ≤v) a≰v)))

    -- An element below a ∨ κ a and not below κ a is above a.
    below-cover : ∀ {v} → v ≤ a ∨ κ a → ¬ v ≤ κ a → a ≤ v
    below-cover {v} v≤ v≰κ = decidable-stable (a ≤? v) λ a≰v →
      a≰κ (≤-from-∨ (trans ∨-comm-law (trans (sd∨ (κ a) a v κa≡κv) (∨-absorbʳ (≤-trans (<→≤₋′ ∧-lowerˡ a≰v) (₋≤κ a))))))
      where
      κ<κ∨v : κ a < κ a ∨ v
      κ<κ∨v = ∨-upperˡ , λ e → v≰κ (≤-from-∨ (trans ∨-comm-law (sym e)))

      κa≡κv : κ a ∨ a ≡ κ a ∨ v
      κa≡κv = ≤-antisym (∨-least ∨-upperˡ (κ<→≤ κ<κ∨v)) (∨-least ∨-upperˡ (≤-trans v≤ ∨-comm-≤))
        where
        ∨-comm-≤ : a ∨ κ a ≤ κ a ∨ a
        ∨-comm-≤ = ∨-least ∨-upperʳ ∨-upperˡ
```

#### Jónsson's relations

The relations are those of FJN p. 51, on the join irreducible elements, which
each relation carries in its type: `a A b` when `b < a ≤ b ∨ κ b`, and `a B b`
when `a ≠ b`, `a ≤ (a ₋) ∨ b` and `a ≰ (a ₋) ∨ (b ₋)`; `C` is their union.  The
subdivisions are those of p. 110: `A₁` when `a ∧ κ b` lies strictly above `b ₋`,
`A₂` when it equals `b ₋`, `B₁` when `b ₋ ≰ a`, `B₂` when `b ₋ < a`.  Each pair
is exhaustive, since `b ₋ ≤ a ∧ κ b` whenever `a A b`, and `b ₋ ≠ a` whenever
`a B b` (a join irreducible `a` with `a = b ₋ < b` would lie below `(a ₋) ∨ (b ₋)`).

```agda
  infix 4 _A_ _B_ _C_ _A?_ _B?_ _C?_ _A₁_ _A₂_ _B₁_ _B₂_

  -- a A b: b < a ≤ b ∨ κ b, both join irreducible.
  _A_ : Fin (suc n) → Fin (suc n) → Type
  a A b = HasOneLowerCover a × HasOneLowerCover b × b < a × a ≤ b ∨ κ b

  -- a B b: a ≠ b, a ≤ (a ₋) ∨ b and a ≰ (a ₋) ∨ (b ₋), both join irreducible.
  _B_ : Fin (suc n) → Fin (suc n) → Type
  a B b = HasOneLowerCover a × HasOneLowerCover b × a ≢ b × a ≤ (a ₋) ∨ b × ¬ a ≤ (a ₋) ∨ (b ₋)

  -- a C b: a A b or a B b.
  _C_ : Fin (suc n) → Fin (suc n) → Type
  a C b = a A b ⊎ a B b

  _A?_ : ∀ a b → Dec (a A b)
  a A? b = hasOneLowerCover? a ×-dec hasOneLowerCover? b ×-dec b <? a ×-dec a ≤? b ∨ κ b

  _B?_ : ∀ a b → Dec (a B b)
  a B? b = hasOneLowerCover? a ×-dec hasOneLowerCover? b ×-dec ¬? (a ≟ b)
           ×-dec a ≤? (a ₋) ∨ b ×-dec ¬? (a ≤? (a ₋) ∨ (b ₋))

  _C?_ : ∀ a b → Dec (a C b)
  a C? b = a A? b ⊎-dec a B? b

  -- The subdivisions of p. 110.
  _A₁_ _A₂_ _B₁_ _B₂_ : Fin (suc n) → Fin (suc n) → Type
  a A₁ b = a A b × b ₋ < a ∧ κ b
  a A₂ b = a A b × a ∧ κ b ≡ b ₋
  a B₁ b = a B b × ¬ b ₋ ≤ a
  a B₂ b = a B b × b ₋ < a

  -- The join irreducibility each relation carries.
  A-irr : ∀ {a b} → a A b → HasOneLowerCover a × HasOneLowerCover b
  A-irr (ia , ib , _) = ia , ib

  B-irr : ∀ {a b} → a B b → HasOneLowerCover a × HasOneLowerCover b
  B-irr (ia , ib , _) = ia , ib

  C-irr : ∀ {a b} → a C b → HasOneLowerCover a × HasOneLowerCover b
  C-irr (inj₁ aAb) = A-irr aAb
  C-irr (inj₂ aBb) = B-irr aBb

  -- a A b puts b strictly below a, and a not below κ b.
  A→< : ∀ {a b} → a A b → b < a
  A→< (_ , _ , b<a , _) = b<a

  A→≰κ : ∀ {a b} → a A b → ¬ a ≤ κ b
  A→≰κ (_ , ib , b<a , _) a≤κ = a≰κ ib (≤-trans (proj₁ b<a) a≤κ)

  -- The subdivisions of A are exhaustive.
  A→A₁⊎A₂ : ∀ {a b} → a A b → a A₁ b ⊎ a A₂ b
  A→A₁⊎A₂ {a} {b} aAb@(_ , ib , b<a , _) with a ∧ κ b ≟ b ₋
  ... | yes e  = inj₂ (aAb , e)
  ... | no ne  = inj₁ (aAb , ∧-greatest (≤-trans (₋≤ b) (proj₁ b<a)) (₋≤κ b) , λ e → ne (sym e))
```

The remarks on p. 51 and p. 109 rewrite `a B b` through `κ`: `a ≤ (a ₋) ∨ b` is
`b ≰ κ a` and `a ≰ (a ₋) ∨ (b ₋)` is `b ₋ ≤ κ a`, both by Lemma 2.57.  In that form
`a B b` says `a ≠ b`, `b ₋ ≤ κ a` and `b ≰ κ a`, and the two elements are
incomparable: `a ≤ b` would put `a` below `b ₋` and so below `(a ₋) ∨ (b ₋)`, and
`b ≤ a` would put `b` below `a ₋` and so `a ≤ (a ₋) ∨ b = a ₋`.

```agda
  -- a B b in the form of p. 109: b ₋ ≤ κ a and b ≰ κ a.
  B→₋≤κ : ∀ {a b} → a B b → b ₋ ≤ κ a
  B→₋≤κ (ia , _ , _ , _ , a≰) = →≤κ ia a≰

  B→≰κ : ∀ {a b} → a B b → ¬ b ≤ κ a
  B→≰κ (ia , _ , _ , a≤ , _) = →≰κ ia a≤

  -- The converse: a ≠ b, b ₋ ≤ κ a and b ≰ κ a give a B b.
  B-from-κ : ∀ {a b} → HasOneLowerCover a → HasOneLowerCover b → a ≢ b → b ₋ ≤ κ a → ¬ b ≤ κ a → a B b
  B-from-κ ia ib a≢b b₋≤κ b≰κ = ia , ib , a≢b , ≰κ→ ia b≰κ , ≤κ→ ia b₋≤κ

  -- The two elements of a B b are incomparable.
  B→≰ : ∀ {a b} → a B b → ¬ a ≤ b
  B→≰ (ia , ib , a≢b , a≤ , a≰) a≤b = a≰ (≤∨ʳ (<→≤₋′ a≤b a≢b))

  B→≱ : ∀ {a b} → a B b → ¬ b ≤ a
  B→≱ {a} {b} (ia , ib , a≢b , a≤ , a≰) b≤a =
    proj₂ ia (sym (≤-antisym (≤-trans a≤ (∨-least ≤-refl (<→≤₋′ b≤a (λ b≡a → a≢b (sym b≡a))))) (₋≤ a)))

  -- The subdivisions of B are exhaustive.
  B→B₁⊎B₂ : ∀ {a b} → a B b → a B₁ b ⊎ a B₂ b
  B→B₁⊎B₂ {a} {b} aBb with b ₋ ≤? a
  ... | no b₋≰a   = inj₁ (aBb , b₋≰a)
  ... | yes b₋≤a  = inj₂ (aBb , b₋≤a , λ b₋≡a → B→≰ aBb (subst (_≤ b) b₋≡a (₋≤ b)))
```

#### Lemma 2.58

If `a B b` then `a ≤ κ b`.  The book's proof applies the strong form of (SD∨),
Theorem 1.21, to `a ∨ b = a ∨ b₋ = a₋ ∨ b`; the binary law suffices.  Suppose
`a ≰ κ b`, so that `b ≤ (b ₋) ∨ a` by Lemma 2.57 for `b`.  With `u = (a ₋) ∨ (b ₋)`,
both `u ∨ a` and `u ∨ b` equal `a ∨ (b ₋)`, which equals `(a ₋) ∨ b`, since each of
`a ≤ (a ₋) ∨ b` and `b ≤ (b ₋) ∨ a` puts one side below the other.  So
`u ∨ a = u ∨ (a ∧ b)` by (SD∨).  But `a ∧ b` lies strictly below `a`, since `a`
and `b` are incomparable, hence below `a ₋ ≤ u`; so `u ∨ a = u`, that is,
`a ≤ (a ₋) ∨ (b ₋)`, against `a B b`.

```agda
  -- Lemma 2.58: a B b implies a ≤ κ b.
  B→≤κ : ∀ {a b} → a B b → a ≤ κ b
  B→≤κ {a} {b} aBb@(ia , ib , a≢b , a≤ , a≰) = decidable-stable (a ≤? κ b) contra
    where
    u : Fin (suc n)
    u = (a ₋) ∨ (b ₋)

    -- a ∧ b lies below a ₋, hence below u.
    a∧b≤u : a ∧ b ≤ u
    a∧b≤u = ≤∨ˡ (<→≤₋′ ∧-lowerˡ (B→≰ aBb))

    contra : ¬ a ≤ κ b → ⊥
    contra a≰κb = a≰ (≤-from-∨ (trans ∨-comm-law (trans (sd∨ u a b ua≡ub) (∨-absorbʳ a∧b≤u))))
      where
      b≤ : b ≤ (b ₋) ∨ a
      b≤ = ≰κ→ ib a≰κb

      a≤′ : a ≤ u ∨ b
      a≤′ = ≤-trans a≤ (∨-mono ∨-upperˡ ≤-refl)

      b≤′ : b ≤ u ∨ a
      b≤′ = ≤-trans b≤ (∨-least (≤∨ˡ ∨-upperʳ) ∨-upperʳ)

      -- u ∨ a = a ∨ b ₋ = a ₋ ∨ b = u ∨ b.
      ua≡ub : u ∨ a ≡ u ∨ b
      ua≡ub = ≤-antisym (∨-least ∨-upperˡ a≤′) (∨-least ∨-upperˡ b≤′)
```

#### Duality

`KappaDuality`{.AgdaModule} relates `Kappa laws sd` to its instance at the
dual tables, `Kappa (dual-laws laws) (swap sd)`, named `ᵈ`.  The dual lattice's
meet is the join of the original, so its order `a ≤ᵈ b`, which is `a ∨ b ≡ a`,
is the converse of the order of the original ([Lattices.Nation.Order][]'s
`≤ᵈ→`{.AgdaFunction} and `→≤ᵈ`{.AgdaFunction}); its `x ₋` is the meet of the elements strictly above `x`,
written `x ⁺`{.AgdaFunction}; its join irreducible elements are the elements with
one upper cover, the book's `M(L)`; and its `κ`, `A`, `B` and `C` are the
book's `κᵈ`, `Aᵈ`, `Bᵈ` and `Cᵈ`.

```agda
module KappaDuality {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                    (laws : LatticeTableLaws _∧_ _∨_)
                    (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  module ᵈ = Kappa (dual-laws laws) (swap sd)

  infix 10 _⁺

  -- x ⁺: the meet of the elements strictly above x, the dual's x ₋.
  _⁺ : Fin (suc n) → Fin (suc n)
  x ⁺ = x ᵈ.₋

  -- M(L): the elements with one upper cover.
  HasOneUpperCover : Fin (suc n) → Type
  HasOneUpperCover = ᵈ.HasOneLowerCover

```

For a join irreducible `a`, `κ a ⁺` is `a ∨ κ a` (`κ⁺`{.AgdaFunction}): every
element strictly above `κ a` is above `a ∨ κ a` (`κ<→≤`{.AgdaFunction}), which
is itself strictly above `κ a`.  So `κ a` has one upper cover
(`κ-oneUpperCover`{.AgdaFunction}), and `κᵈ (κ a) = a`
(`κᵈκ`{.AgdaFunction}): `a` lies in the dual's `K (κ a)`, being below `κ a ⁺` and
not below `κ a`, so `κᵈ (κ a) ≤ a`; and `κᵈ (κ a)` lies below `κ a ⁺ = a ∨ κ a`
and not below `κ a`, so it is above `a` by `below-cover`{.AgdaFunction}.

```agda
  module _ {a : Fin (suc n)} (one : HasOneLowerCover a) where

    -- κ a ⁺ ≡ a ∨ κ a.
    κ⁺≤ : κ a ⁺ ≤ a ∨ κ a
    κ⁺≤ = ≤ᵈ→ (ᵈ.<→≤₋ (→<ᵈ (∨-upperʳ , λ e → a≰κ one (≤-from-∨ (sym e)))))

    κ⁺≥ : a ∨ κ a ≤ κ a ⁺
    κ⁺≥ = ≤ᵈ→ (ᵈ.∨*-least (All.tabulate λ {v} v∈ →
            →≤ᵈ (∨-least (κ<→≤ one (<ᵈ→ (ᵈ.∈below⁻ v∈))) (proj₁ (<ᵈ→ (ᵈ.∈below⁻ v∈)))))
            (ᵈ.⊥ᴸ-least (a ∨ κ a)))

    κ⁺ : κ a ⁺ ≡ a ∨ κ a
    κ⁺ = ≤-antisym κ⁺≤ κ⁺≥

    -- κ a has one upper cover.
    κ-oneUpperCover : HasOneUpperCover (κ a)
    κ-oneUpperCover = ᵈ.₋≤ (κ a) , λ e → a≰κ one (≤-trans ∨-upperˡ (subst ((a ∨ κ a) ≤_) e κ⁺≥))

    -- κᵈ (κ a) ≡ a: the half of Corollary 2.55 the proofs use.
    κᵈκ : ᵈ.κ (κ a) ≡ a
    κᵈκ = ≤-antisym
      (≤ᵈ→ (ᵈ.K≤κ (ᵈ.∈K⁺ (→≤ᵈ (≤-trans ∨-upperˡ κ⁺≥)) λ e → a≰κ one (≤ᵈ→ e))))
      (below-cover one (≤-trans (≤ᵈ→ (ᵈ.₋≤κ (κ a))) κ⁺≤) λ v≤κ → ᵈ.a≰κ κ-oneUpperCover (→≤ᵈ v≤κ))

  -- κ is injective on the join irreducible elements.
  κ-injective : ∀ {a b} → HasOneLowerCover a → HasOneLowerCover b → κ a ≡ κ b → a ≡ b
  κ-injective ia ib e = trans (sym (κᵈκ ia)) (trans (cong ᵈ.κ e) (κᵈκ ib))
```

Lemma 2.63 (p. 53), Nation's duality.  In the dual's vocabulary, `κ a Bᵈ κ b`
says that `κ a ≠ κ b`, that `(κ a ⁺) ∧ κ b ≤ κ a` and that
`(κ a ⁺) ∧ (κ b ⁺) ≰ κ a`; with `κ a ⁺ = a ∨ κ a` and `below-cover`, the second says
`a ≰ κ b` and the third says `a ≤ b ∨ κ b`, and together with
`κ a ≠ κ b` they say `b < a ≤ b ∨ κ b`, which is `a A b`.  And `κ a Aᵈ κ b` says
`κ a < κ b` and `κ b ∧ κᵈ (κ b) ≤ κ a`, where `κ b ∧ κᵈ (κ b) = κ b ∧ b = b ₋`;
by Lemma 2.57 for `b`, `κ a ≤ κ b` with `b ₋ ≤ κ a` says `b ≰ κ a`, and so the
two say `a ≠ b`, `b ₋ ≤ κ a` and `b ≰ κ a`, which is `a B b` in the form of
p. 109.

```agda
  module _ {a b : Fin (suc n)} where

    -- Lemma 2.63 (1): a A b if and only if κ a Bᵈ κ b.
    A→Bᵈ : a A b → κ a ᵈ.B κ b
    A→Bᵈ aAb@(ia , ib , b<a , a≤) =
      κ-oneUpperCover ia , κ-oneUpperCover ib
      , (λ e → proj₂ b<a (sym (κ-injective ia ib e)))
      , →≤ᵈ (subst (λ x → x ∧ κ b ≤ κ a) (sym (κ⁺ ia)) t≤κ)
      , λ e → a≰κ ia (≤-trans (∧-greatest ∨-upperˡ a≤)
                       (≤ᵈ→ (subst₂ (λ x y → κ a ᵈ.≤ x ∧ y) (κ⁺ ia) (κ⁺ ib) e)))
      where
      t≤κ : (a ∨ κ a) ∧ κ b ≤ κ a
      t≤κ = decidable-stable ((a ∨ κ a) ∧ κ b ≤? κ a) λ t≰κ →
        A→≰κ aAb (≤-trans (below-cover ia ∧-lowerˡ t≰κ) ∧-lowerʳ)

    Bᵈ→A : HasOneLowerCover a → HasOneLowerCover b → κ a ᵈ.B κ b → a A b
    Bᵈ→A ia ib (_ , _ , κa≢κb , κa≤ᵈ , κa≰ᵈ) = ia , ib , (b≤a , λ b≡a → κa≢κb (cong κ (sym b≡a))) , a≤
      where
      a≰κb : ¬ a ≤ κ b
      a≰κb a≤κb = a≰κ ia (≤-trans (∧-greatest ∨-upperˡ a≤κb)
                             (≤ᵈ→ (subst (λ x → κ a ᵈ.≤ x ∧ κ b) (κ⁺ ia) κa≤ᵈ)))

      a≤ : a ≤ b ∨ κ b
      a≤ = ≤-trans (below-cover ia ∧-lowerˡ λ s≤κ → κa≰ᵈ (→≤ᵈ (subst₂ (λ x y → x ∧ y ≤ κ a) (sym (κ⁺ ia)) (sym (κ⁺ ib)) s≤κ)))
                   ∧-lowerʳ

      b≤a : b ≤ a
      b≤a = below-cover ib a≤ a≰κb

    -- Lemma 2.63 (2): a B b if and only if κ a Aᵈ κ b.
    B→Aᵈ : a B b → κ a ᵈ.A κ b
    B→Aᵈ aBb@(ia , ib , a≢b , _ , _) =
      κ-oneUpperCover ia , κ-oneUpperCover ib
      , →<ᵈ (→≤κ ib (λ b≤ → B→≰κ aBb (≤-trans b≤ (∨-least (B→₋≤κ aBb) ≤-refl))) , λ e → a≢b (κ-injective ia ib e))
      , →≤ᵈ (subst (λ x → κ b ∧ x ≤ κ a) (sym (κᵈκ ib)) (≤-trans (≤-reflexive′ (trans ∧-comm-law (a∧κ ib))) (B→₋≤κ aBb)))

    Aᵈ→B : HasOneLowerCover a → HasOneLowerCover b → κ a ᵈ.A κ b → a B b
    Aᵈ→B ia ib (_ , _ , κb<ᵈκa , κa≤ᵈ) = B-from-κ ia ib a≢b b₋≤κa b≰κa
      where
      κa<κb : κ a < κ b
      κa<κb = <ᵈ→ κb<ᵈκa

      a≢b : a ≢ b
      a≢b refl = proj₂ κa<κb refl

      b₋≤κa : b ₋ ≤ κ a
      b₋≤κa = ≤-trans (∧-greatest (₋≤κ b) (₋≤ b)) (≤ᵈ→ (subst (λ x → κ a ᵈ.≤ κ b ∧ x) (κᵈκ ib) κa≤ᵈ))

      b≰κa : ¬ b ≤ κ a
      b≰κa b≤κa = a≰κ ib (≤-trans b≤κa (proj₁ κa<κb))
```

The other half of Corollary 2.55, `κ (κᵈ b) = b` for every `b` with one upper
cover, is the same lemma at the dual tables: the definitions of `κ`, of the
order and of the covers depend on the tables alone, not on their laws, so the
instance of `KappaDuality` at `dual-laws laws` speaks of the same `κ`.

```agda
module _ {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
         (laws : LatticeTableLaws _∧_ _∨_)
         (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open KappaDuality laws sd using ( module ᵈ ; HasOneUpperCover )

  -- κ (κᵈ b) ≡ b for b with one upper cover: Corollary 2.55's other half, by duality.
  κκᵈ : ∀ {b} → HasOneUpperCover b → κ (ᵈ.κ b) ≡ b
  κκᵈ = KappaDuality.κᵈκ (dual-laws laws) (swap sd)
```
