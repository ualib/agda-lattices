---
layout: default
file: "src/Lattices/Breadth.lagda.md"
title: "Lattices.Breadth module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Jónsson and Kiefer's breadth bound

This is the [Lattices.Breadth][] module of the [agda-lattices][] library.

A lattice has *breadth at most `n`* if every element that is the join of a
finite set `S` is the join of a subset of `S` with at most `n` members
([Freese, Ježek, and Nation (1995)][], p. 24).  Jónsson and Kiefer ("Finite
sublattices of a free lattice", Canad. J. Math. 14, 1962) showed that a finite
lattice satisfying Whitman's condition (W) has breadth at most 4, so that the
finite sublattices of free lattices satisfy a nontrivial lattice equation.
This module proves the following:

+  **Theorem 1.30** (Jónsson and Kiefer).  In a lattice satisfying (W), let
   `a₁, a₂, a₃, v` satisfy (1) `aᵢ ≰ aⱼ ∨ aₖ ∨ v` whenever
   `{i, j, k} = {1, 2, 3}`, (2) `v ≰ aᵢ` for each `i`, and (3) `v` is meet
   irreducible.  Then `FL(3)` is a sublattice of the lattice.
+  **Corollary 1.31**.  A finite lattice satisfying (W) has breadth at most 4.
+  **The 4-distributive law** holds in every lattice of breadth at most 4
   (the book's p. 25, "not hard to see"), hence in every finite lattice
   satisfying (W).

Every case split below is on a sum that (W) returns, on the decidable equality
of `Fin 3`{.AgdaDatatype}, or, in a finite lattice, on its decidable order.
The finiteness contradiction is the standard library's finite pigeonhole: an
embedding of `FL(3)` composed with Whitman's strict chain of Example 1.24
([Lattices.Free.WhitmanChains][]) injects `ℕ` into the lattice.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Breadth where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; toℕ )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.Fin.Properties                    using ( _≟_ ; pigeonhole )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; length ; removeAt )
open import Data.List.Membership.Propositional     using ( _∈_ ; _─_ )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ )
open import Data.List.Relation.Binary.Sublist.Propositional
                                                   using ( _⊆_ ; [] ; _∷_ ; _∷ʳ_ )
open import Data.List.Relation.Binary.Sublist.Propositional.Properties
                                                   using ( Any-resp-⊆ )
open import Data.List.Relation.Unary.Any           using ( here ; there )
open import Data.Nat.Base                          using ( ℕ ; s≤s ; z≤n )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; cong ; sym )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; map′ )

import Data.Nat.Base        as Nat
import Data.Nat.Properties  as Nat

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Lattices.Free.Universal             using ( FL )
open import Lattices.Free.Whitman               using ( _≈ʷ_ )
open import Lattices.Free.WhitmanChains         using ( ascending-reflects )
open import Lattices.Free.WhitmanPolynomials    using ( ascending )
open import Lattices.Generation
  using  ( ⋁⁺ ; _≤⋁_ ; ≤⋁⁺ ; ⋁⁺-upper ; ⋁⁺-least ; ≤-≤⋁ ; ∨-≤⋁ ; ≤⋁-⊆ ; ≤⋁-elim ; ≤⋁-nonempty
         ; ∈→≤⋁ ; ⋁⁺-≤⋁
         ; FreelyGenerates ; bound→JoinCondition ; bound→MeetCondition ; freelyGenerates→≤ )
open import Lattices.Semidistributive           using ( SatisfiesW ; W-irreducible )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )

open Func using () renaming ( to to _⟨$⟩_ )

private variable
  α ρ ℓ : Level
```
-->

#### The three indices

Theorem 1.30 speaks of three elements and, for each, the two others.  The
indices are those of `Fin 3`{.AgdaDatatype}, and the two others of `i` are
`other₁ i` and `other₂ i`, in cyclic order; every index is `i`
or one of them (`others`{.AgdaFunction}).  The three indices are distinct.

```agda
-- The two other indices, in cyclic order.
other₁ other₂ : Fin 3 → Fin 3
other₁ 0F = 1F
other₁ 1F = 2F
other₁ 2F = 0F
other₂ 0F = 2F
other₂ 1F = 0F
other₂ 2F = 1F

-- Every index is i or one of its others.
others : (i j : Fin 3) → j ≡ i ⊎ (j ≡ other₁ i ⊎ j ≡ other₂ i)
others 0F 0F = inj₁ refl
others 0F 1F = inj₂ (inj₁ refl)
others 0F 2F = inj₂ (inj₂ refl)
others 1F 0F = inj₂ (inj₂ refl)
others 1F 1F = inj₁ refl
others 1F 2F = inj₂ (inj₁ refl)
others 2F 0F = inj₂ (inj₁ refl)
others 2F 1F = inj₂ (inj₂ refl)
others 2F 2F = inj₁ refl

-- The others of i differ from i and from each other.
other₁≢ : (i : Fin 3) → ¬ (other₁ i ≡ i)
other₁≢ 0F ()
other₁≢ 1F ()
other₁≢ 2F ()

other₂≢ : (i : Fin 3) → ¬ (other₂ i ≡ i)
other₂≢ 0F ()
other₂≢ 1F ()
other₂≢ 2F ()

other₂≢other₁ : (i : Fin 3) → ¬ (other₂ i ≡ other₁ i)
other₂≢other₁ 0F ()
other₂≢other₁ 1F ()
other₂≢other₁ 2F ()
```

#### Meet irreducibility from (W)

An element `v` is *meet irreducible* (`MeetIrreducible`{.AgdaFunction}) if it
is a meet only trivially: `v ≈ d ∧ e` implies `v ≈ d` or `v ≈ e`.  In a
lattice satisfying (W), every element is join irreducible or meet irreducible
([Freese, Ježek, and Nation (1995)][], Corollary 1.9), which
[Lattices.Semidistributive][] proves as `W-irreducible`{.AgdaFunction}.
Corollary 1.31 needs it in this form: a proper join, `v ≈ b ∨ c` with
`v ≉ b` and `v ≉ c`, is meet irreducible
(`proper-join→meet-irreducible`{.AgdaFunction}).

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )

  private
    L : Type α
    L = 𝕌[ proj₁ 𝑳 ]

  -- v is a meet only trivially.
  MeetIrreducible : L → Type (α ⊔ ρ)
  MeetIrreducible v = ∀ {d e} → v ≈ d ∧ e → v ≈ d ⊎ v ≈ e

  -- Corollary 1.9 in the form Corollary 1.31 uses: a proper join is meet irreducible.
  proper-join→meet-irreducible : SatisfiesW 𝑳 → {v b c : L} → v ≈ b ∨ c → ¬ (v ≈ b) → ¬ (v ≈ c)
                               → MeetIrreducible v
  proper-join→meet-irreducible W v≈b∨c v≉b v≉c v≈d∧e =
    [ (λ q → q) , [ (λ e → ⊥-elim (v≉b e)) , (λ e → ⊥-elim (v≉c e)) ]′ ]′ (W-irreducible 𝑳 W v≈b∨c v≈d∧e)
```

#### Theorem 1.30

Fix a lattice `𝑳`{.AgdaBound} satisfying (W), a family `a` of three elements
and an element `v` with the theorem's hypotheses (the module
`JonssonKiefer`{.AgdaModule}): `h₁`, that `a i ≰ a j ∨ a k ∨ v` for the two
others `j` and `k` of `i`; `h₂`, that `v ≰ a i`; and `h₃`, that `v` is meet
irreducible.  The book puts, for the two others `j` and `k` of `i`,

    bᵢ = aᵢ ∨ ((aⱼ ∨ v) ∧ (aₖ ∨ v)),

and calls the meet `mᵢ = (aⱼ ∨ v) ∧ (aₖ ∨ v)` below.  Both `v ≤ mᵢ` and
`v ≤ bᵢ` hold (`v≤m`{.AgdaFunction}, `v≤b`{.AgdaFunction}).  The first two
lemmas read `h₁` at a single other index: `aⱼ ∨ v` lies below `aⱼ ∨ aₖ ∨ v`
(`other∨v≤`{.AgdaFunction}), so `aᵢ ≰ aⱼ ∨ v` for `j ≠ i`
(`a≰a∨v`{.AgdaFunction}), and in particular `aᵢ ≰ v` (`a≰v`{.AgdaFunction}).

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-trans ; ≤-antisym ; ≤-respʳ-≈ ; ∧-greatest
                                   ; ∧-lowerˡ ; ∧-lowerʳ ; ∨-least ; ∨-upperˡ ; ∨-upperʳ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ) renaming ( sym to ≈sym )

  private
    L : Type α
    L = 𝕌[ proj₁ 𝑳 ]

  module JonssonKiefer (W : SatisfiesW 𝑳) (a : Fin 3 → L) (v : L)
                       (h₁ : ∀ i → ¬ (a i ≤ a (other₁ i) ∨ a (other₂ i) ∨ v))
                       (h₂ : ∀ i → ¬ (v ≤ a i))
                       (h₃ : MeetIrreducible 𝑳 v) where

    -- The meetand of bᵢ, and bᵢ.
    m b : Fin 3 → L
    m i = (a (other₁ i) ∨ v) ∧ (a (other₂ i) ∨ v)
    b i = a i ∨ m i

    v≤m : (i : Fin 3) → v ≤ m i
    v≤m i = ∧-greatest ∨-upperʳ ∨-upperʳ

    v≤b : (i : Fin 3) → v ≤ b i
    v≤b i = ≤-trans (v≤m i) ∨-upperʳ

    -- Another member joined with v lies below the join in hypothesis (1).
    other∨v≤ : (i j : Fin 3) → ¬ (j ≡ i) → a j ∨ v ≤ a (other₁ i) ∨ a (other₂ i) ∨ v
    other∨v≤ i j j≢i with others i j
    ... | inj₁ j≡i          = ⊥-elim (j≢i j≡i)
    ... | inj₂ (inj₁ refl)  = ∨-least (≤-trans ∨-upperˡ ∨-upperˡ) ∨-upperʳ
    ... | inj₂ (inj₂ refl)  = ∨-least (≤-trans ∨-upperʳ ∨-upperˡ) ∨-upperʳ

    -- Hypothesis (1) at one other index: aᵢ ≰ aⱼ ∨ v.
    a≰a∨v : (i j : Fin 3) → ¬ (j ≡ i) → ¬ (a i ≤ a j ∨ v)
    a≰a∨v i j j≢i p = h₁ i (≤-trans p (other∨v≤ i j j≢i))

    -- In particular aᵢ ≰ v.
    a≰v : (i : Fin 3) → ¬ (a i ≤ v)
    a≰v i p = a≰a∨v i (other₁ i) (other₁≢ i) (≤-trans p ∨-upperʳ)
```

**The `bᵢ` are join irredundant**.  For `j ≠ i`, the meet `mⱼ` lies below
`aₖ ∨ v` for either other `k` of `j` (`m≤a∨v`{.AgdaFunction}), so `bⱼ` lies
below `aⱼ ∨ aₖ ∨ v` for the two others of `i` (`b≤`{.AgdaFunction}), and
`bᵢ ≤ bⱼ ∨ bₖ` would give `aᵢ ≤ bᵢ ≤ aⱼ ∨ aₖ ∨ v`, against `h₁`
(`join-irredundant`{.AgdaFunction}).  In particular the `bᵢ` are pairwise
incomparable (`b≰b`{.AgdaFunction}).

```agda
    -- mᵢ lies below aⱼ ∨ v for j ≠ i.
    m≤a∨v : (i j : Fin 3) → ¬ (j ≡ i) → m i ≤ a j ∨ v
    m≤a∨v i j j≢i with others i j
    ... | inj₁ j≡i          = ⊥-elim (j≢i j≡i)
    ... | inj₂ (inj₁ refl)  = ∧-lowerˡ
    ... | inj₂ (inj₂ refl)  = ∧-lowerʳ

    -- bⱼ lies below the join in hypothesis (1) at i, for j ≠ i.
    b≤ : (i j : Fin 3) → ¬ (j ≡ i) → b j ≤ a (other₁ i) ∨ a (other₂ i) ∨ v
    b≤ i j j≢i with others i j
    ... | inj₁ j≡i          = ⊥-elim (j≢i j≡i)
    ... | inj₂ (inj₁ refl)  =
      ∨-least (≤-trans ∨-upperˡ (other∨v≤ i (other₁ i) (other₁≢ i)))
              (≤-trans (m≤a∨v (other₁ i) (other₂ i) (other₂≢other₁ i)) (other∨v≤ i (other₂ i) (other₂≢ i)))
    ... | inj₂ (inj₂ refl)  =
      ∨-least (≤-trans ∨-upperˡ (other∨v≤ i (other₂ i) (other₂≢ i)))
              (≤-trans (m≤a∨v (other₂ i) (other₁ i) (λ e → other₂≢other₁ i (sym e)))
                       (other∨v≤ i (other₁ i) (other₁≢ i)))

    -- The bᵢ are join irredundant.
    join-irredundant : (i : Fin 3) → ¬ (b i ≤ b (other₁ i) ∨ b (other₂ i))
    join-irredundant i p =
      h₁ i (≤-trans ∨-upperˡ (≤-trans p (∨-least (b≤ i (other₁ i) (other₁≢ i)) (b≤ i (other₂ i) (other₂≢ i)))))

    -- In particular they are pairwise incomparable.
    b≰b : (i j : Fin 3) → ¬ (j ≡ i) → ¬ (b i ≤ b j)
    b≰b i j j≢i p with others i j
    ... | inj₁ j≡i          = j≢i j≡i
    ... | inj₂ (inj₁ refl)  = join-irredundant i (≤-trans p ∨-upperˡ)
    ... | inj₂ (inj₂ refl)  = join-irredundant i (≤-trans p ∨-upperʳ)
```

**The `bᵢ` are meet irredundant**, by the book's three applications of (W),
one lemma each, read from the last to the first.  Take `k`, with others
`i = other₁ k` and `j = other₂ k` (for `k = 3` these are the book's `1` and
`2`).

+  *The third* (`m≰a∨v`{.AgdaFunction}): `mᵢ ≰ aᵢ ∨ v`.  Apply (W) to
   `(aⱼ ∨ v) ∧ (aₖ ∨ v) ≤ aᵢ ∨ v`, for the two others of `i`.  Neither meetand
   lies below `aᵢ ∨ v`, by `h₁`; the meet does not lie below `aᵢ`, since `v`
   lies below it, by `h₂`; and if it lies below `v`, then `v` equals it, so by
   `h₃` equals `aⱼ ∨ v` or `aₖ ∨ v`, and `aⱼ ≤ v` or `aₖ ≤ v`, against `h₁`.
+  *The second* (`bb≰a∨v`{.AgdaFunction}): `bᵢ ∧ bⱼ ≰ aᵢ ∨ v`, for `j ≠ i`.
   Apply (W).  If `bᵢ ≤ aᵢ ∨ v`, then `mᵢ ≤ aᵢ ∨ v`, against the third; if
   `bⱼ ≤ aᵢ ∨ v`, then `aⱼ ≤ aᵢ ∨ v`, against `h₁`; the meet does not lie
   below `aᵢ`, by `h₂`; and if it lies below `v`, then `v = bᵢ ∧ bⱼ`, so by
   `h₃` equals `bᵢ` or `bⱼ`, and `aᵢ ≤ v` or `aⱼ ≤ v`.
+  *The first* (`meet-irredundant`{.AgdaFunction}): `bᵢ ∧ bⱼ ≰ bₖ`.  Apply (W)
   to `bᵢ ∧ bⱼ ≤ aₖ ∨ mₖ`.  Neither `bᵢ` nor `bⱼ` lies below `bₖ`; the meet does
   not lie below `aₖ`, by `h₂`; and if it lies below `mₖ`, it lies below
   `aᵢ ∨ v`, against the second.

```agda
    -- The third application of (W).
    m≰a∨v : (i : Fin 3) → ¬ (m i ≤ a i ∨ v)
    m≰a∨v i p with W (a (other₁ i) ∨ v) (a (other₂ i) ∨ v) (a i) v p
    ... | inj₁ (inj₁ q) = a≰a∨v (other₁ i) i (λ e → other₁≢ i (sym e)) (≤-trans ∨-upperˡ q)
    ... | inj₁ (inj₂ q) = a≰a∨v (other₂ i) i (λ e → other₂≢ i (sym e)) (≤-trans ∨-upperˡ q)
    ... | inj₂ (inj₁ q) = h₂ i (≤-trans (v≤m i) q)
    ... | inj₂ (inj₂ q) =
      [ (λ e → a≰v (other₁ i) (≤-respʳ-≈ (≈sym e) ∨-upperˡ))
      , (λ e → a≰v (other₂ i) (≤-respʳ-≈ (≈sym e) ∨-upperˡ)) ]′ (h₃ (≤-antisym (v≤m i) q))

    -- The second application of (W).
    bb≰a∨v : (i j : Fin 3) → ¬ (j ≡ i) → ¬ (b i ∧ b j ≤ a i ∨ v)
    bb≰a∨v i j j≢i p with W (b i) (b j) (a i) v p
    ... | inj₁ (inj₁ q) = m≰a∨v i (≤-trans ∨-upperʳ q)
    ... | inj₁ (inj₂ q) = a≰a∨v j i (λ e → j≢i (sym e)) (≤-trans ∨-upperˡ q)
    ... | inj₂ (inj₁ q) = h₂ i (≤-trans (∧-greatest (v≤b i) (v≤b j)) q)
    ... | inj₂ (inj₂ q) =
      [ (λ e → a≰v i (≤-respʳ-≈ (≈sym e) ∨-upperˡ))
      , (λ e → a≰v j (≤-respʳ-≈ (≈sym e) ∨-upperˡ)) ]′ (h₃ (≤-antisym (∧-greatest (v≤b i) (v≤b j)) q))

    -- The first application of (W): the bᵢ are meet irredundant.
    meet-irredundant : (k : Fin 3) → ¬ (b (other₁ k) ∧ b (other₂ k) ≤ b k)
    meet-irredundant k p with W (b (other₁ k)) (b (other₂ k)) (a k) (m k) p
    ... | inj₁ (inj₁ q) = b≰b (other₁ k) k (λ e → other₁≢ k (sym e)) q
    ... | inj₁ (inj₂ q) = b≰b (other₂ k) k (λ e → other₂≢ k (sym e)) q
    ... | inj₂ (inj₁ q) = h₂ k (≤-trans (∧-greatest (v≤b (other₁ k)) (v≤b (other₂ k))) q)
    ... | inj₂ (inj₂ q) = bb≰a∨v (other₁ k) (other₂ k) (other₂≢other₁ k) (≤-trans q ∧-lowerˡ)
```

**The `bᵢ` generate `FL(3)`**.  The book closes by citing Corollary 1.13, which
is for subsets of a free lattice; the step needed is Corollary 1.12 in `𝑳`,
which [Lattices.Generation][] proves for any lattice with (W).  For each `i`,
`bⱼ ∨ bₖ` lies above the two others and not above `bᵢ`, and `bⱼ ∧ bₖ` lies below
them and not below `bᵢ`, so the family satisfies the join condition and the meet
condition (`b-free`{.AgdaFunction}), and `FL(3)` is a sublattice of `𝑳` by the
homomorphism it induces (`FL3≤`{.AgdaFunction}).

```agda
    -- The bᵢ freely generate.
    b-free : FreelyGenerates 𝑳 b
    b-free = bound→JoinCondition 𝑳 b _≟_ join-bound , bound→MeetCondition 𝑳 b _≟_ meet-bound
      where
      join-bound : ∀ i → Σ[ r ∈ L ] ((∀ j → j ≡ i ⊎ b j ≤ r) × ¬ (b i ≤ r))
      join-bound i = b (other₁ i) ∨ b (other₂ i) , others≤ , join-irredundant i
        where
        others≤ : ∀ j → j ≡ i ⊎ b j ≤ b (other₁ i) ∨ b (other₂ i)
        others≤ j with others i j
        ... | inj₁ e            = inj₁ e
        ... | inj₂ (inj₁ refl)  = inj₂ ∨-upperˡ
        ... | inj₂ (inj₂ refl)  = inj₂ ∨-upperʳ

      meet-bound : ∀ i → Σ[ r ∈ L ] ((∀ j → j ≡ i ⊎ r ≤ b j) × ¬ (r ≤ b i))
      meet-bound i = b (other₁ i) ∧ b (other₂ i) , ≤others , meet-irredundant i
        where
        ≤others : ∀ j → j ≡ i ⊎ b (other₁ i) ∧ b (other₂ i) ≤ b j
        ≤others j with others i j
        ... | inj₁ e            = inj₁ e
        ... | inj₂ (inj₁ refl)  = inj₂ ∧-lowerˡ
        ... | inj₂ (inj₂ refl)  = inj₂ ∧-lowerʳ

    -- Theorem 1.30: FL(3) is a sublattice of 𝑳.
    FL3≤ : proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ 𝑳
    FL3≤ = freelyGenerates→≤ 𝑳 b _≟_ W b-free

  -- Theorem 1.30 (Jónsson and Kiefer), as a function of its hypotheses.
  theorem-1-30 : SatisfiesW 𝑳 → (a : Fin 3 → L) (v : L)
               → (∀ i → ¬ (a i ≤ a (other₁ i) ∨ a (other₂ i) ∨ v)) → (∀ i → ¬ (v ≤ a i))
               → MeetIrreducible 𝑳 v → proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ 𝑳
  theorem-1-30 W a v h₁ h₂ h₃ = JonssonKiefer.FL3≤ W a v h₁ h₂ h₃
```

#### A finite lattice does not contain `FL(3)`

A finite lattice admits no injection of `ℕ` (`no-injection`{.AgdaFunction}):
send the first `card + 1` naturals through the injection and the enumeration's
section, which is a map `Fin (card + 1) → Fin card`; the standard library's
`pigeonhole`{.AgdaFunction} finds two indices `i < j` with the same image, and
then the two naturals have equal values, so are equal, against `i < j`.  Whitman's
ascending chain of Example 1.24 is an injection of `ℕ` into `FL(3)`
(`ascending-injective`{.AgdaFunction}, from `ascending-reflects`{.AgdaFunction}
used both ways), so a finite lattice has no sublattice isomorphic to `FL(3)`
(`finite→¬FL3≤`{.AgdaFunction}).

```agda
-- Whitman's ascending chain is injective.
ascending-injective : {m n : ℕ} → ascending m ≈ʷ ascending n → m ≡ n
ascending-injective {m} {n} (p , q) = Nat.≤-antisym (ascending-reflects m n p) (ascending-reflects n m q)

module _ (𝑳 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
  open FiniteAlgebra 𝑭       using ( card ; enum ; enum-sur )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; reflexive ) renaming ( sym to ≈sym ; trans to ≈trans )

  -- A finite lattice admits no injection of ℕ.
  no-injection : (g : ℕ → 𝕌[ proj₁ 𝑳 ]) → (∀ {m n} → g m ≈ g n → m ≡ n) → ⊥
  no-injection g inj =
    let (i , j , i<j , fi≡fj) = pigeonhole (Nat.n<1+n card) f
    in Nat.<-irrefl (inj (≈trans (≈sym (proj₂ (enum-sur (g (toℕ i)))))
                                 (≈trans (reflexive (cong enum fi≡fj)) (proj₂ (enum-sur (g (toℕ j)))))))
                    i<j
    where
    f : Fin (Nat.suc card) → Fin card
    f k = proj₁ (enum-sur (g (toℕ k)))

  -- A finite lattice has no sublattice isomorphic to FL(3).
  finite→¬FL3≤ : ¬ (proj₁ (FL (Fin 3)) IsSubalgebraOf proj₁ 𝑳)
  finite→¬FL3≤ (h , inj) = no-injection (λ n → proj₁ h ⟨$⟩ ascending n) (λ e → ascending-injective (inj e))
```

#### Breadth

`Breadth≤ 𝑳 n`{.AgdaFunction} says that the join of every nonempty finite list
`S` is the join of a nonempty sublist `T` with at most `n` members.  The book
quantifies over finite sets, which may be empty; a lattice need not have a least
element, and the empty join, where it exists, is the join of the empty subset,
so nothing is lost by taking `S` nonempty.  A sublist is
`_⊆_`{.AgdaDatatype} of the standard library: the members of `S` kept, in order.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )

  -- The join of every nonempty finite list is the join of a sublist of at most n members.
  Breadth≤ : ℕ → Type (α ⊔ ρ)
  Breadth≤ n = (s : 𝕌[ proj₁ 𝑳 ]) (ss : List 𝕌[ proj₁ 𝑳 ])
    → Σ[ t ∈ 𝕌[ proj₁ 𝑳 ] ] Σ[ ts ∈ List 𝕌[ proj₁ 𝑳 ] ]
        ((t ∷ ts) ⊆ (s ∷ ss) × length (t ∷ ts) Nat.≤ n × ⋁⁺ 𝑳 t ts ≈ ⋁⁺ 𝑳 s ss)
```

A list is *irredundant* (`Irredundant`{.AgdaFunction}) if no member lies below
the join of the others, where the others of the member at position `p` are the
list with that position removed (`T ─ p`).

In a finite lattice the order is decidable, and every nonempty list has an
irredundant sublist with the same join.  The construction, `reduce`, passes
over the list once, carrying a context `C` of the members already kept: it drops
a member `x` when `x` lies below the join of `C` and the members not yet seen,
and keeps it otherwise.  A kept member was not below the join of everything
that could end up beside it, so it is not below the join of what does; a dropped
member lies below the join of what remains, so the join does not change.  Its
result is a record, `Reduced C S`{.AgdaRecord}, carrying the sublist `T` of `S`
and these invariants: irredundance relative to `C` (`irr`), the agreement of the
upper bounds of `C ++ T` and `C ++ S` (`cover`), and that `C ++ T` is nonempty
when `C ++ S` is (`inhabited`).

```agda
module _ (𝑳 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
  open FiniteAlgebra 𝑭       using () renaming ( _≟_ to _≟ᴸ_ )
  open Lattice-Op 𝑳          using ( _∧_ )
  open Lattice-Order 𝑳       using ( _≤_ )

  private
    L : Type α
    L = 𝕌[ proj₁ 𝑳 ]

  -- In a finite lattice, a ≤⋁ G is decidable.
  _≤⋁?_ : (a : L) (G : List L) → Dec (_≤⋁_ 𝑳 a G)
  a ≤⋁? []        = no λ ()
  a ≤⋁? (g ∷ gs)  = map′ (≤⋁⁺ {𝑳 = 𝑳}) (λ { (≤⋁⁺ p) → p }) ((a ∧ ⋁⁺ 𝑳 g gs) ≟ᴸ a)

  -- Membership moves across one member.
  move : {x f : L} (C D : List L) → f ∈ C ++ x ∷ D → f ∈ x ∷ (C ++ D)
  move C D f∈ with ∈-++⁻ C f∈
  ... | inj₁ f∈C          = there (∈-++⁺ˡ f∈C)
  ... | inj₂ (here refl)  = here refl
  ... | inj₂ (there f∈D)  = there (∈-++⁺ʳ C f∈D)

  unmove : {x f : L} (C D : List L) → f ∈ x ∷ (C ++ D) → f ∈ C ++ x ∷ D
  unmove C D (here refl)  = ∈-++⁺ʳ C (here refl)
  unmove C D (there f∈) with ∈-++⁻ C f∈
  ... | inj₁ f∈C  = ∈-++⁺ˡ f∈C
  ... | inj₂ f∈D  = ∈-++⁺ʳ C (there f∈D)

  -- The result of reducing S in the context C.
  record Reduced (C S : List L) : Type (α ⊔ ρ) where
    field
      T          : List L
      sub        : T ⊆ S
      irr        : ∀ {x} (p : x ∈ T) → ¬ (_≤⋁_ 𝑳 x (C ++ (T ─ p)))
      cover      : ∀ {u} → (∀ {f} → f ∈ C ++ T → f ≤ u) → ∀ {f} → f ∈ C ++ S → f ≤ u
      inhabited  : ∀ {y} → y ∈ C ++ S → Σ[ z ∈ L ] z ∈ C ++ T
```

Dropping `x`, when `x ≤⋁ (C ++ S)`, keeps every invariant of the reduction of
`S` (`drop`{.AgdaFunction}); the only new member of `C ++ x ∷ S` lies below the
join of `C ++ S`, so below every upper bound of it.  Keeping `x`, when
`x ≰⋁ (C ++ S)`, after reducing `S` in the context `x ∷ C`, gives the
invariants for `x ∷ T` (`keep`{.AgdaFunction}): `x` is not below the join of
`C ++ T`, which lies below the join of `C ++ S`, and a later member's others in
`C ++ x ∷ T` are its others in `(x ∷ C) ++ T`.

```agda
  -- Drop x, which lies below the join of the rest.
  drop : (C : List L) (x : L) (S : List L) → _≤⋁_ 𝑳 x (C ++ S) → Reduced C S → Reduced C (x ∷ S)
  drop C x S x≤ R = record { T = T ; sub = x ∷ʳ sub ; irr = irr ; cover = cover′
                           ; inhabited = λ _ → inhabited (proj₂ (≤⋁-nonempty 𝑳 x≤)) }
    where
    open Reduced R
    cover′ : ∀ {u} → (∀ {f} → f ∈ C ++ T → f ≤ u) → ∀ {f} → f ∈ C ++ x ∷ S → f ≤ u
    cover′ ub f∈ with ∈-++⁻ C f∈
    ... | inj₁ f∈C          = cover ub (∈-++⁺ˡ f∈C)
    ... | inj₂ (here refl)  = ≤⋁-elim 𝑳 x≤ (cover ub)
    ... | inj₂ (there f∈S)  = cover ub (∈-++⁺ʳ C f∈S)

  -- Keep x, which does not lie below the join of the rest.
  keep : (C : List L) (x : L) (S : List L) → ¬ (_≤⋁_ 𝑳 x (C ++ S)) → Reduced (x ∷ C) S
       → Reduced C (x ∷ S)
  keep C x S x≰ R = record { T = x ∷ T ; sub = refl ∷ sub ; irr = irr′ ; cover = cover′
                           ; inhabited = λ _ → x , ∈-++⁺ʳ C (here refl) }
    where
    open Reduced R
    irr′ : ∀ {y} (p : y ∈ x ∷ T) → ¬ (_≤⋁_ 𝑳 y (C ++ ((x ∷ T) ─ p)))
    irr′ (here refl) y≤ =
      x≰ (≤⋁-⊆ 𝑳 y≤ λ f∈ → [ ∈-++⁺ˡ , (λ f∈T → ∈-++⁺ʳ C (Any-resp-⊆ sub f∈T)) ]′ (∈-++⁻ C f∈))
    irr′ (there q) y≤ = irr q (≤⋁-⊆ 𝑳 y≤ (move C (T ─ q)))

    cover′ : ∀ {u} → (∀ {f} → f ∈ C ++ x ∷ T → f ≤ u) → ∀ {f} → f ∈ C ++ x ∷ S → f ≤ u
    cover′ ub f∈ = cover (λ g∈ → ub (unmove C T g∈)) (move C S f∈)

  -- Reduce S in the context C.
  reduce : (C S : List L) → Reduced C S
  reduce C []       = record { T = [] ; sub = [] ; irr = λ () ; cover = λ ub → ub
                             ; inhabited = λ {y} y∈ → y , y∈ }
  reduce C (x ∷ S)  with x ≤⋁? (C ++ S)
  ... | yes x≤  = drop C x S x≤ (reduce C S)
  ... | no x≰   = keep C x S x≰ (reduce (x ∷ C) S)
```

#### Corollary 1.31

Let `𝑳` be finite and satisfy (W), and let `a₁ ∷ a₂ ∷ ⋯` be an irredundant
list.  If it has at least five members, put `v = a₄ ∨ ⋯ ∨ aₙ`, the join of
`a₄ ∷ a₅ ∷ ⋯`.  Then `a₁, a₂, a₃, v` satisfy the hypotheses of Theorem 1.30:
(1) and (2) by irredundance (`v ≤ aᵢ` would put `a₄` below another member), and
(3) because `v = a₄ ∨ (a₅ ∨ ⋯)` is a proper join (each joinand equal to `v`
would put `a₅` or `a₄` below the others), hence meet irreducible.  So `FL(3)` is
a sublattice of `𝑳`, which is finite, a contradiction
(`irredundant→short`{.AgdaFunction}).  The irredundant sublist that
`reduce` returns therefore has at most four members, and its join is that of
the list (`breadth≤4`{.AgdaFunction}).

```agda
  -- No member of an irredundant list lies below the join of the others.
  Irredundant : List L → Type (α ⊔ ρ)
  Irredundant T = ∀ {x} (p : x ∈ T) → ¬ (_≤⋁_ 𝑳 x (T ─ p))

  module _ (W : SatisfiesW 𝑳) where
    open Lattice-Op 𝑳          using ( _∨_ )
    open Lattice-Order 𝑳       using ( ≤-trans ; ≤-antisym ; ≤-reflexive ; ∨-least ; ∨-upperˡ ; ∨-upperʳ )
    open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ) renaming ( refl to ≈refl )

    -- An irredundant list in a finite lattice with (W) has at most four members.
    irredundant→short : (t : L) (ts : List L) → Irredundant (t ∷ ts) → length (t ∷ ts) Nat.≤ 4
    irredundant→short t []                          _ = s≤s z≤n
    irredundant→short t (_ ∷ [])                    _ = s≤s (s≤s z≤n)
    irredundant→short t (_ ∷ _ ∷ [])                _ = s≤s (s≤s (s≤s z≤n))
    irredundant→short t (_ ∷ _ ∷ _ ∷ [])            _ = s≤s (s≤s (s≤s (s≤s z≤n)))
    irredundant→short a₁ (a₂ ∷ a₃ ∷ a₄ ∷ a₅ ∷ rest) irr =
      ⊥-elim (finite→¬FL3≤ 𝑳 𝑭 (theorem-1-30 𝑳 W a v h₁ h₂ h₃))
      where
      a : Fin 3 → L
      a 0F = a₁
      a 1F = a₂
      a 2F = a₃

      v : L
      v = ⋁⁺ 𝑳 a₄ (a₅ ∷ rest)

      -- v lies below the join of any two members followed by a₄, a₅, ….
      v≤ : {x y : L} → _≤⋁_ 𝑳 v (x ∷ y ∷ a₄ ∷ a₅ ∷ rest)
      v≤ = ⋁⁺-≤⋁ 𝑳 {b = a₄} {bs = a₅ ∷ rest} λ f∈ → there (there f∈)

      -- Two members, and v, lie below the join of a list containing them.
      pair∨v≤ : {x y : L} {G : List L} → x ∈ G → y ∈ G → _≤⋁_ 𝑳 v G → _≤⋁_ 𝑳 (x ∨ y ∨ v) G
      pair∨v≤ x∈ y∈ v≤G = ∨-≤⋁ 𝑳 (∨-≤⋁ 𝑳 (∈→≤⋁ 𝑳 x∈) (∈→≤⋁ 𝑳 y∈)) v≤G

      -- Hypothesis (1): each of a₁, a₂, a₃ is not below the join of the others.
      h₁ : ∀ i → ¬ (a i ≤ a (other₁ i) ∨ a (other₂ i) ∨ v)
      h₁ 0F p = irr (here refl) (≤-≤⋁ 𝑳 p (pair∨v≤ (here refl) (there (here refl)) v≤))
      h₁ 1F p = irr (there (here refl)) (≤-≤⋁ 𝑳 p (pair∨v≤ (there (here refl)) (here refl) v≤))
      h₁ 2F p = irr (there (there (here refl))) (≤-≤⋁ 𝑳 p (pair∨v≤ (here refl) (there (here refl)) v≤))

      -- Each of a₁, a₂, a₃ is among the others of a₄.
      a∈others₄ : ∀ i → a i ∈ a₁ ∷ a₂ ∷ a₃ ∷ a₅ ∷ rest
      a∈others₄ 0F = here refl
      a∈others₄ 1F = there (here refl)
      a∈others₄ 2F = there (there (here refl))

      -- Hypothesis (2): v ≤ aᵢ would put a₄ below the others.
      h₂ : ∀ i → ¬ (v ≤ a i)
      h₂ i q = irr (there (there (there (here refl)))) (≤-≤⋁ 𝑳 (≤-trans ∨-upperˡ q) (∈→≤⋁ 𝑳 (a∈others₄ i)))

      -- a₅ lies below v.
      a₅≤v : a₅ ≤ v
      a₅≤v = ≤-trans (⋁⁺-upper 𝑳 {b = a₅} {bs = rest} (here refl)) ∨-upperʳ

      -- v is not a₄: else a₅ lies below a₄.
      v≉a₄ : ¬ (v ≈ a₄)
      v≉a₄ e = irr (there (there (there (there (here refl)))))
        (≤-≤⋁ 𝑳 (≤-trans a₅≤v (≤-reflexive e)) (∈→≤⋁ 𝑳 (there (there (there (here refl))))))

      -- v is not the join of a₅, …: else a₄ lies below it.
      v≉rest : ¬ (v ≈ ⋁⁺ 𝑳 a₅ rest)
      v≉rest e = irr (there (there (there (here refl))))
        (≤-≤⋁ 𝑳 (≤-trans ∨-upperˡ (≤-reflexive e))
                (⋁⁺-≤⋁ 𝑳 {b = a₅} {bs = rest} λ f∈ → there (there (there f∈))))

      -- Hypothesis (3): v is a proper join, hence meet irreducible.
      h₃ : MeetIrreducible 𝑳 v
      h₃ = proper-join→meet-irreducible 𝑳 W ≈refl v≉a₄ v≉rest

    -- From the reduction: a nonempty irredundant sublist with the same join.
    short-sublist : (s : L) (ss : List L) (T : List L) → T ⊆ (s ∷ ss) → Irredundant T
                  → (∀ {u} → (∀ {f} → f ∈ T → f ≤ u) → ∀ {f} → f ∈ s ∷ ss → f ≤ u)
                  → Σ[ z ∈ L ] z ∈ T
                  → Σ[ t ∈ L ] Σ[ ts ∈ List L ]
                      ((t ∷ ts) ⊆ (s ∷ ss) × length (t ∷ ts) Nat.≤ 4 × ⋁⁺ 𝑳 t ts ≈ ⋁⁺ 𝑳 s ss)
    short-sublist s ss []        _    _   _      (_ , ())
    short-sublist s ss (t ∷ ts)  sub  irr cover  _ =
      t , ts , sub , irredundant→short t ts irr
        , ≤-antisym (⋁⁺-least 𝑳 {b = t} {bs = ts} λ f∈ → ⋁⁺-upper 𝑳 {b = s} {bs = ss} (Any-resp-⊆ sub f∈))
                    (⋁⁺-least 𝑳 {b = s} {bs = ss} (cover (⋁⁺-upper 𝑳 {b = t} {bs = ts})))

    -- Corollary 1.31: a finite lattice satisfying (W) has breadth at most 4.
    breadth≤4 : Breadth≤ 𝑳 4
    breadth≤4 s ss = short-sublist s ss T sub irr cover (inhabited (here refl))
      where open Reduced (reduce [] (s ∷ ss))
```

#### The 4-distributive law

The *4-distributive law* (`IsFourDistributive`{.AgdaFunction}) is the
inequality

    x ∧ (x₁ ∨ x₂ ∨ x₃ ∨ x₄ ∨ x₅)  ≤  ⋁ᵢ (x ∧ ⋁_{j ≠ i} xⱼ),

with every join nested to the left.  In a lattice of breadth at most 4 it
holds (`breadth≤4→fourDistributive`{.AgdaFunction}): the join of
`x₁, …, x₅` is the join of a sublist of at most four of them, which misses some
position `i` (`missing`{.AgdaFunction}), so it lies below `⋁_{j ≠ i} xⱼ`, and
the left side lies below the `i`-th joinand of the right side.  With
Corollary 1.31, every finite lattice satisfying (W) satisfies the law
(`finite-W→fourDistributive`{.AgdaFunction}).  It fails in the lattice of
subspaces of a five-dimensional vector space ([Freese, Ježek, and Nation
(1995)][], p. 25), so it is a nontrivial lattice equation; this module does
not formalize that.

```agda
-- A sublist shorter than its list misses a position.
missing : {A : Type ℓ} {T S : List A} → T ⊆ S → length T Nat.< length S
        → Σ[ p ∈ Fin (length S) ] T ⊆ removeAt S p
missing (y ∷ʳ q)    _         = zero , q
missing (refl ∷ q)  (s≤s lt)  = let (p , q′) = missing q lt in suc p , refl ∷ q′

module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-trans ; ≤-reflexive ; ∧-greatest ; ∧-lowerˡ ; ∧-lowerʳ
                                   ; ∨-least ; ∨-upperˡ ; ∨-upperʳ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ) renaming ( sym to ≈sym )

  private
    L : Type α
    L = 𝕌[ proj₁ 𝑳 ]

  -- The 4-distributive law, every join nested to the left.
  IsFourDistributive : Type (α ⊔ ρ)
  IsFourDistributive = (x x₁ x₂ x₃ x₄ x₅ : L)
    → x ∧ (x₁ ∨ x₂ ∨ x₃ ∨ x₄ ∨ x₅)
      ≤ (x ∧ (x₂ ∨ x₃ ∨ x₄ ∨ x₅)) ∨ (x ∧ (x₁ ∨ x₃ ∨ x₄ ∨ x₅)) ∨ (x ∧ (x₁ ∨ x₂ ∨ x₄ ∨ x₅))
        ∨ (x ∧ (x₁ ∨ x₂ ∨ x₃ ∨ x₅)) ∨ (x ∧ (x₁ ∨ x₂ ∨ x₃ ∨ x₄))

  -- A member of four (five) lies below their left-nested join.
  left4-upper : {f y₁ y₂ y₃ y₄ : L} → f ∈ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ [] → f ≤ y₁ ∨ y₂ ∨ y₃ ∨ y₄
  left4-upper (here refl)                          = ≤-trans (≤-trans ∨-upperˡ ∨-upperˡ) ∨-upperˡ
  left4-upper (there (here refl))                  = ≤-trans (≤-trans ∨-upperʳ ∨-upperˡ) ∨-upperˡ
  left4-upper (there (there (here refl)))          = ≤-trans ∨-upperʳ ∨-upperˡ
  left4-upper (there (there (there (here refl))))  = ∨-upperʳ

  left5-upper : {f y₁ y₂ y₃ y₄ y₅ : L} → f ∈ y₁ ∷ y₂ ∷ y₃ ∷ y₄ ∷ y₅ ∷ [] → f ≤ y₁ ∨ y₂ ∨ y₃ ∨ y₄ ∨ y₅
  left5-upper (here refl)                                  = ≤-trans (left4-upper (here refl)) ∨-upperˡ
  left5-upper (there (here refl))                          = ≤-trans (left4-upper (there (here refl))) ∨-upperˡ
  left5-upper (there (there (here refl)))                  =
    ≤-trans (left4-upper (there (there (here refl)))) ∨-upperˡ
  left5-upper (there (there (there (here refl))))          =
    ≤-trans (left4-upper (there (there (there (here refl))))) ∨-upperˡ
  left5-upper (there (there (there (there (here refl)))))  = ∨-upperʳ

  module _ (x x₁ x₂ x₃ x₄ x₅ : L) where
    -- The five arguments and, for each position, the join of the other four.
    S : List L
    S = x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []

    others₅ : Fin 5 → L
    others₅ 0F = x₂ ∨ x₃ ∨ x₄ ∨ x₅
    others₅ 1F = x₁ ∨ x₃ ∨ x₄ ∨ x₅
    others₅ 2F = x₁ ∨ x₂ ∨ x₄ ∨ x₅
    others₅ 3F = x₁ ∨ x₂ ∨ x₃ ∨ x₅
    others₅ 4F = x₁ ∨ x₂ ∨ x₃ ∨ x₄

    -- What remains at a missed position lies below the join of the others.
    removed≤others : (p : Fin 5) → ∀ {f} → f ∈ removeAt S p → f ≤ others₅ p
    removed≤others 0F = left4-upper
    removed≤others 1F = left4-upper
    removed≤others 2F = left4-upper
    removed≤others 3F = left4-upper
    removed≤others 4F = left4-upper

    -- Each joinand x ∧ others₅ p lies below the right side.
    joinand≤ : (p : Fin 5)
      → x ∧ others₅ p ≤ (x ∧ others₅ 0F) ∨ (x ∧ others₅ 1F) ∨ (x ∧ others₅ 2F)
                        ∨ (x ∧ others₅ 3F) ∨ (x ∧ others₅ 4F)
    joinand≤ 0F = left5-upper (here refl)
    joinand≤ 1F = left5-upper (there (here refl))
    joinand≤ 2F = left5-upper (there (there (here refl)))
    joinand≤ 3F = left5-upper (there (there (there (here refl))))
    joinand≤ 4F = left5-upper (there (there (there (there (here refl)))))

```

```agda
  -- Breadth at most 4 gives the 4-distributive law.
  breadth≤4→fourDistributive : Breadth≤ 𝑳 4 → IsFourDistributive
  breadth≤4→fourDistributive B x x₁ x₂ x₃ x₄ x₅ =
    ≤-trans (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ (≤-trans join≤ (≤-trans (≤-reflexive (≈sym eq)) T≤))))
            (joinand≤ x x₁ x₂ x₃ x₄ x₅ p)
    where
    reduced = B x₁ (x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
    t   = proj₁ reduced
    ts  = proj₁ (proj₂ reduced)
    sub = proj₁ (proj₂ (proj₂ reduced))
    len = proj₁ (proj₂ (proj₂ (proj₂ reduced)))
    eq  = proj₂ (proj₂ (proj₂ (proj₂ reduced)))
    miss = missing sub (s≤s len)
    p    = proj₁ miss

    up : {f : L} → f ∈ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [] → f ≤ ⋁⁺ 𝑳 x₁ (x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
    up = ⋁⁺-upper 𝑳 {b = x₁} {bs = x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []}

    join≤ : x₁ ∨ x₂ ∨ x₃ ∨ x₄ ∨ x₅ ≤ ⋁⁺ 𝑳 x₁ (x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])
    join≤ = ∨-least (∨-least (∨-least (∨-least (up (here refl)) (up (there (here refl))))
                                      (up (there (there (here refl)))))
                             (up (there (there (there (here refl))))))
                    (up (there (there (there (there (here refl))))))

    T≤ : ⋁⁺ 𝑳 t ts ≤ others₅ x x₁ x₂ x₃ x₄ x₅ p
    T≤ = ⋁⁺-least 𝑳 {b = t} {bs = ts} λ f∈ → removed≤others x x₁ x₂ x₃ x₄ x₅ p (Any-resp-⊆ (proj₂ miss) f∈)

-- Every finite lattice satisfying (W) satisfies the 4-distributive law.
finite-W→fourDistributive : (𝑳 : Lattice α ρ) → FiniteAlgebra (proj₁ 𝑳) → SatisfiesW 𝑳
                          → IsFourDistributive 𝑳
finite-W→fourDistributive 𝑳 𝑭 W = breadth≤4→fourDistributive 𝑳 (breadth≤4 𝑳 𝑭 W)
```
