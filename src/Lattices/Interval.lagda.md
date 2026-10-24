---
layout: default
file: "src/Lattices/Interval.lagda.md"
title: "Lattices.Interval module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Intervals of a lattice as lattices

This is the [Lattices.Interval][] module of the [agda-lattices][] library.

The *interval* `[lo, hi]` of a lattice `L` is the set of elements `x` with
`lo ≤ x ≤ hi`.  It is closed under meets and joins, so it is a sublattice of
`L`, with `lo` and `hi` as its bounds when `lo ≤ hi`, and it is the
one-element lattice exactly when `lo = hi`.  The direct decomposition of a
bounded lattice by a central element `c` ([Lattices.Central.Decomposition][])
has the two intervals `[0, c]` and `[c, 1]` as its factors, which is what this
module is for; but an interval is a construction of lattice theory in its own
right, and nothing here is about central elements.

The module defines the following, for a lattice `𝑳`{.AgdaBound} on a setoid:

+  `Interval 𝑳 lo hi`{.AgdaFunction}, the carrier: an element of
   `𝑳`{.AgdaBound} with proofs that it lies between `lo` and `hi`, two members
   being equal when their elements are;
+  the lattice `𝑳 [ lo , hi ]`{.AgdaFunction}, whose meet and join are those
   of `𝑳`{.AgdaBound}, carried by the closure of the interval under both;
+  the inclusion into `𝑳`{.AgdaBound} as an injective homomorphism
   (`intervalHom`{.AgdaFunction}, `intervalSub`{.AgdaFunction}), so that every
   condition the library moves to sublattices holds on an interval of a
   lattice that satisfies it;
+  the bounds `⊥ᴵ`{.AgdaFunction} and `⊤ᴵ`{.AgdaFunction} of a nonempty
   interval, and the two directions of "the interval is trivial exactly when
   `lo ≈ hi`" (`interval-nontrivial`{.AgdaFunction},
   `interval-trivial`{.AgdaFunction}).

agda-algebras has intervals of a lattice in the sense of the standard
library's order-theoretic lattices (`Order.Interval`); the lattices of this
library are algebras over the lattice signature on a setoid, which is why the
construction is repeated here for them.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Interval where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Patterns                using ( 0F ; 1F )
open import Data.Product                     using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                         using ( Func )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Nullary.Negation.Core   using ( ¬_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret      using ( interp-cong )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op ; setoidEqsToLattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Monolith         using ( Nontrivial )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```
-->

#### The carrier and the lattice

A member of the interval is an element with its two proofs, and two members are
equal when their elements are, so the proofs never matter to equality.  The meet
of two members lies above `lo`, since both do, and below `hi`, since one does;
the join dually.  The eight lattice equations hold because they hold in
`𝑳`{.AgdaBound} on the elements, and `setoidEqsToLattice`{.AgdaFunction} of
[Classical.Structures.Lattice.Basic][] accepts the proofs of `𝑳`{.AgdaBound}
unchanged, the equality of the interval being that of `𝑳`{.AgdaBound} on the
first components.  The meet order of the interval is the order of
`𝑳`{.AgdaBound} on the elements, definitionally
(`interval-≤`{.AgdaFunction}).

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law
                                   ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law ; absorbˡ-law ; absorbʳ-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ≤-respʳ-≈
                                   ; ∧-lowerˡ ; ∧-greatest ; ∨-upperˡ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )

  -- The elements between lo and hi, with their proofs.
  Interval : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → Type (α ⊔ ρ)
  Interval lo hi = Σ[ x ∈ 𝕌[ proj₁ 𝑳 ] ] (lo ≤ x × x ≤ hi)

  module _ (lo hi : 𝕌[ proj₁ 𝑳 ]) where

    -- Two members are equal when their elements are.
    intervalSetoid : Setoid (α ⊔ ρ) ρ
    intervalSetoid = record
      { Carrier        = Interval lo hi
      ; _≈_            = λ p q → proj₁ p ≈ proj₁ q
      ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }
      }

    infixl 7 _∧ᴵ_ _∨ᴵ_

    -- The meet and join of 𝑳, which stay in the interval.
    _∧ᴵ_ : Interval lo hi → Interval lo hi → Interval lo hi
    p ∧ᴵ q = proj₁ p ∧ proj₁ q
           , ∧-greatest (proj₁ (proj₂ p)) (proj₁ (proj₂ q))
           , ≤-trans ∧-lowerˡ (proj₂ (proj₂ p))

    _∨ᴵ_ : Interval lo hi → Interval lo hi → Interval lo hi
    p ∨ᴵ q = proj₁ p ∨ proj₁ q
           , ≤-trans (proj₁ (proj₂ p)) ∨-upperˡ
           , ∨-least (proj₂ (proj₂ p)) (proj₂ (proj₂ q))

    -- The interval as a lattice: the laws of 𝑳, read on the elements.
    intervalLattice : Lattice (α ⊔ ρ) ρ
    intervalLattice = setoidEqsToLattice intervalSetoid _∧ᴵ_ _∨ᴵ_
      (λ {p} {q} {u} {v} → ∧-cong {proj₁ p} {proj₁ q} {proj₁ u} {proj₁ v})
      (λ {p} {q} {u} {v} → ∨-cong {proj₁ p} {proj₁ q} {proj₁ u} {proj₁ v})
      ∧-assoc-law ∧-comm-law ∧-idem-law ∨-assoc-law ∨-comm-law ∨-idem-law absorbˡ-law absorbʳ-law

    -- The order of the interval is the order of 𝑳 on the elements.
    interval-≤ : ∀ {p q} → Lattice-Order._≤_ intervalLattice p q → proj₁ p ≤ proj₁ q
    interval-≤ p≤q = p≤q
```

#### The inclusion

The first projection respects equality by definition and commutes with both
operations, so it is a homomorphism into `𝑳`{.AgdaBound}
(`intervalHom`{.AgdaFunction}), and it is injective, again by the definition
of the interval's equality, so the interval is a sublattice of `𝑳`{.AgdaBound}
in the sense of [Setoid.Subalgebras.Basic][] (`intervalSub`{.AgdaFunction}).

```agda
    intervalHom : hom (proj₁ intervalLattice) (proj₁ 𝑳)
    intervalHom = mkhom (proj₁ intervalLattice) (proj₁ 𝑳) incl compatible
      where
      incl : Func intervalSetoid 𝔻[ proj₁ 𝑳 ]
      incl = record { to = proj₁ ; cong = λ e → e }

      compatible : compatible-map (proj₁ intervalLattice) (proj₁ 𝑳) incl
      compatible {∧-Op} {a} = interp-cong (proj₁ 𝑳) ∧-Op λ { 0F → refl ; 1F → refl }
      compatible {∨-Op} {a} = interp-cong (proj₁ 𝑳) ∨-Op λ { 0F → refl ; 1F → refl }

    intervalSub : proj₁ intervalLattice IsSubalgebraOf proj₁ 𝑳
    intervalSub = intervalHom , λ e → e
```

#### Bounds, and the trivial interval

When `lo ≤ hi`, the interval contains `lo` and `hi`, and they are its bottom
and its top: for a member `p`, the inequalities `lo ≤ p` and `p ≤ hi` are the
proofs `p` carries.  The interval has two different members exactly when
`lo ≉ hi`: if `lo ≉ hi`, then `⊥ᴵ`{.AgdaFunction} and `⊤ᴵ`{.AgdaFunction}
differ; and if `lo ≈ hi`, every member `p` equals `lo`, by antisymmetry from
`lo ≤ p ≤ hi ≈ lo`, so no two members differ.

```agda
    module _ (lo≤hi : lo ≤ hi) where
      ⊥ᴵ ⊤ᴵ : Interval lo hi
      ⊥ᴵ = lo , ≤-refl , lo≤hi
      ⊤ᴵ = hi , lo≤hi , ≤-refl

      ⊥ᴵ-bottom : Lattice-Order.IsBottom intervalLattice ⊥ᴵ
      ⊥ᴵ-bottom p = proj₁ (proj₂ p)

      ⊤ᴵ-top : Lattice-Order.IsTop intervalLattice ⊤ᴵ
      ⊤ᴵ-top p = proj₂ (proj₂ p)

      -- The interval has two different members when its ends differ.
      interval-nontrivial : ¬ lo ≈ hi → Nontrivial (proj₁ intervalLattice)
      interval-nontrivial lo≉hi = ⊥ᴵ , ⊤ᴵ , lo≉hi

    -- Every member of an interval with equal ends equals the lower end.
    interval-collapse : lo ≈ hi → ∀ (p : Interval lo hi) → proj₁ p ≈ lo
    interval-collapse lo≈hi p = ≤-antisym (≤-respʳ-≈ (sym lo≈hi) (proj₂ (proj₂ p))) (proj₁ (proj₂ p))

    -- An interval with equal ends has no two different members.
    interval-trivial : lo ≈ hi → ¬ Nontrivial (proj₁ intervalLattice)
    interval-trivial lo≈hi (p , q , p≉q) =
      p≉q (trans (interval-collapse lo≈hi p) (sym (interval-collapse lo≈hi q)))
```

The lattice is also written `𝑳 [ lo , hi ]`{.AgdaFunction}.

```agda
infix 10 _[_,_]

_[_,_] : (𝑳 : Lattice α ρ) → 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → Lattice (α ⊔ ρ) ρ
𝑳 [ lo , hi ] = intervalLattice 𝑳 lo hi
```

--------------------------------------

[Lattices.Interval]: Lattices.Interval.html
[Lattices.Central.Decomposition]: Lattices.Central.Decomposition.html
[Classical.Structures.Lattice.Basic]: Classical.Structures.Lattice.Basic.html
[Setoid.Subalgebras.Basic]: Setoid.Subalgebras.Basic.html
