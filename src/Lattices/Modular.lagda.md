---
layout: default
file: "src/Lattices/Modular.lagda.md"
title: "Lattices.Modular module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Modular and distributive lattices

This is the [Lattices.Modular][] module of the [agda-lattices][] library.

A lattice is *modular* if `x ≤ z` implies `x ∨ (y ∧ z) = (x ∨ y) ∧ z`, and
*distributive* if `x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)` for all `x`, `y`, `z`.
Every distributive lattice is modular, and the inequality
`x ∨ (y ∧ z) ≤ (x ∨ y) ∧ z` holds for `x ≤ z` in every lattice, so the modular
law asks only for the other half.  The two classical characterizations by
forbidden sublattices are proved in [Lattices.Modular.Dedekind][] (a lattice is
modular if and only if it has no sublattice isomorphic to the pentagon `N₅`)
and [Lattices.Modular.Birkhoff][] (a modular lattice is distributive if and only
if it has no sublattice isomorphic to the diamond `M₃`), and together they are
the M₃-N₅ theorem ([Davey and Priestley (2002)][], Theorem 4.10).

This library has distributive lattices as a structure too,
`DistributiveLattice`{.AgdaFunction} of [Lattices.Distributive][], a lattice
packaged with its distributive laws, and that module passes between the
structure and the predicate below.  This module states both conditions as *predicates* on
a given lattice, in the shape of [Lattices.Semidistributive][], so that a
proof can be applied to the elements it is about, a decision procedure can
sweep them, and the conditions can be moved to sublattices and along
isomorphisms.  It defines the following:

+  `IsModular`{.AgdaFunction}, the modular law as an implication, and
   `ModularIdentity`{.AgdaFunction}, the equivalent identity
   `x ∨ (y ∧ (x ∨ z)) = (x ∨ y) ∧ (x ∨ z)`, which is what a sweep decides;
+  `IsDistributive`{.AgdaFunction}, with the dual distributive law derived
   (`IsDistributive-dual`{.AgdaFunction}) rather than assumed, and
   `IsDistributive→IsModular`{.AgdaFunction};
+  `ModularFailure`{.AgdaFunction} and `DistributiveFailure`{.AgdaFunction}, a
   failure of each law as a witness, which is what the two criteria start from;
+  the invariance of both conditions under sublattices and isomorphisms;
+  the decisions `isModular?`{.AgdaFunction} and
   `isDistributive?`{.AgdaFunction} on a finite lattice, and the functions
   `modularFailure`{.AgdaFunction} and `distributiveFailure`{.AgdaFunction}
   that turn a negative verdict into a witness.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Modular where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Properties              using ( all? ; ¬∀⟶∃¬ )
open import Data.Product                     using ( _×_ ; _,_ ; proj₁ ; proj₂ ; ∃-syntax )
open import Function                         using ( Func )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Nullary.Decidable.Core  using ( Dec ; map′ )
open import Relation.Nullary.Negation.Core   using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra ; all³? ; enum-all³ )
open import Setoid.Homomorphisms.Basic          using ( hom )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; ≅-sym )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )
open import Setoid.Subalgebras.Properties       using ( ≅→≤ )

-- Imports from this library --------------------------------------------------------
open import Lattices.Semidistributive  using ( hom-preserves-∧ ; hom-preserves-∨ ; hom-preserves-≤ )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ β ρᵃ ρᵇ : Level
```
-->

#### The predicates

Fix a lattice `𝑳`{.AgdaBound}, with the curried operations of
`Lattice-Op`{.AgdaModule} and the meet order `x ≤ z`, meaning `x ∧ z ≈ x`, of
`Lattice-Order`{.AgdaModule}.  `IsModular`{.AgdaFunction} is the modular law in
Dedekind's form, an implication between an inequality and an equation; it is
the form the criteria use, and the one a consumer applies to a pair `x ≤ z` it
has in hand.  `ModularIdentity`{.AgdaFunction} is the same law as an identity,
obtained by putting `x ∨ z` for `z`, which lies above `x` whatever `z` is; it
has no hypothesis, so a finite sweep decides it instance by instance.
`IsDistributive`{.AgdaFunction} is the law that meets distribute over joins;
the dual law is a consequence, below.

A *failure* of a law is a triple at which it fails, together with the
hypothesis the law needs there: `ModularFailure`{.AgdaFunction} is a triple
`x ≤ z`, `y` with `x ∨ (y ∧ z) ≉ (x ∨ y) ∧ z`, and
`DistributiveFailure`{.AgdaFunction} a triple with
`x ∧ (y ∨ z) ≉ (x ∧ y) ∨ (x ∧ z)`.  A failure refutes the law, but the converse
needs a search: from `¬ IsModular 𝑳`{.AgdaFunction} alone no triple can be
read off constructively.  In a finite lattice the search exists, and the
decision block at the end of this module performs it.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳       using ( _≤_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ )

  -- The modular law: x ≤ z implies x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z.
  IsModular : Type (α ⊔ ρ)
  IsModular = ∀ x y z → x ≤ z → x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z

  -- The modular law as an identity.
  ModularIdentity : Type (α ⊔ ρ)
  ModularIdentity = ∀ x y z → x ∨ (y ∧ (x ∨ z)) ≈ (x ∨ y) ∧ (x ∨ z)

  -- The distributive law: meets distribute over joins.
  IsDistributive : Type (α ⊔ ρ)
  IsDistributive = ∀ x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)

  -- A triple x ≤ z, y at which the modular law fails.
  ModularFailure : Type (α ⊔ ρ)
  ModularFailure = ∃[ x ] ∃[ y ] ∃[ z ] (x ≤ z × ¬ (x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z))

  -- A triple at which the distributive law fails.
  DistributiveFailure : Type (α ⊔ ρ)
  DistributiveFailure = ∃[ x ] ∃[ y ] ∃[ z ] ¬ (x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z))
```

#### The two forms of the modular law, and distributivity

The modular law gives the identity at `x ≤ x ∨ z`, and the identity gives the
law: if `x ≤ z` then `x ∨ z ≈ z`, and the identity at `x`, `y`, `z` becomes the
law after rewriting `x ∨ z` to `z` on both sides.

A failure refutes its law (`ModularFailure→¬IsModular`{.AgdaFunction},
`DistributiveFailure→¬IsDistributive`{.AgdaFunction}).

The dual distributive law, `x ∨ (y ∧ z) ≈ (x ∨ y) ∧ (x ∨ z)`, follows from the
distributive law by the usual computation: distribute `x ∨ y` over `x ∨ z`,
absorb `(x ∨ y) ∧ x` to `x`, distribute `z` over `x ∨ y`, and absorb `z ∧ x`
into `x`.  So the two distributive laws are equivalent, by this lemma and its
dual, and `IsDistributive`{.AgdaFunction} states one of them.

A distributive lattice is modular: for `x ≤ z`,
`(x ∨ y) ∧ z ≈ (z ∧ x) ∨ (z ∧ y) ≈ x ∨ (y ∧ z)`, since `z ∧ x ≈ x`.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                                   ; ∨-assoc-law ; absorbˡ-law ; absorbʳ-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-via-∨ ; ∨-upperˡ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  IsModular→ModularIdentity : IsModular 𝑳 → ModularIdentity 𝑳
  IsModular→ModularIdentity m x y z = m x y (x ∨ z) ∨-upperˡ

  ModularIdentity→IsModular : ModularIdentity 𝑳 → IsModular 𝑳
  ModularIdentity→IsModular mi x y z x≤z = begin
    x ∨ (y ∧ z)        ≈˘⟨ ∨-cong refl (∧-cong refl x∨z≈z) ⟩
    x ∨ (y ∧ (x ∨ z))  ≈⟨ mi x y z ⟩
    (x ∨ y) ∧ (x ∨ z)  ≈⟨ ∧-cong refl x∨z≈z ⟩
    (x ∨ y) ∧ z        ∎
    where
    x∨z≈z : x ∨ z ≈ z
    x∨z≈z = ≤-via-∨ x≤z

  -- A failure of the modular law refutes it.
  ModularFailure→¬IsModular : ModularFailure 𝑳 → ¬ IsModular 𝑳
  ModularFailure→¬IsModular (x , y , z , x≤z , fails) m = fails (m x y z x≤z)

  -- A failure of the distributive law refutes it.
  DistributiveFailure→¬IsDistributive : DistributiveFailure 𝑳 → ¬ IsDistributive 𝑳
  DistributiveFailure→¬IsDistributive (x , y , z , fails) d = fails (d x y z)

  -- The dual distributive law, derived.
  IsDistributive-dual : IsDistributive 𝑳 → ∀ x y z → x ∨ (y ∧ z) ≈ (x ∨ y) ∧ (x ∨ z)
  IsDistributive-dual d x y z = sym (begin
    (x ∨ y) ∧ (x ∨ z)              ≈⟨ d (x ∨ y) x z ⟩
    ((x ∨ y) ∧ x) ∨ ((x ∨ y) ∧ z)  ≈⟨ ∨-cong (trans ∧-comm-law absorbˡ-law) ∧-comm-law ⟩
    x ∨ (z ∧ (x ∨ y))              ≈⟨ ∨-cong refl (d z x y) ⟩
    x ∨ ((z ∧ x) ∨ (z ∧ y))        ≈˘⟨ ∨-assoc-law ⟩
    x ∨ (z ∧ x) ∨ (z ∧ y)          ≈⟨ ∨-cong x∨z∧x≈x ∧-comm-law ⟩
    x ∨ (y ∧ z)                    ∎)
    where
    x∨z∧x≈x : x ∨ (z ∧ x) ≈ x
    x∨z∧x≈x = trans ∨-comm-law (trans (∨-cong ∧-comm-law refl) absorbʳ-law)

  IsDistributive→IsModular : IsDistributive 𝑳 → IsModular 𝑳
  IsDistributive→IsModular d x y z x≤z = sym (begin
    (x ∨ y) ∧ z        ≈⟨ ∧-comm-law ⟩
    z ∧ (x ∨ y)        ≈⟨ d z x y ⟩
    (z ∧ x) ∨ (z ∧ y)  ≈⟨ ∨-cong (trans ∧-comm-law x≤z) ∧-comm-law ⟩
    x ∨ (y ∧ z)        ∎)
```

#### Sublattices

Both conditions pass to sublattices, by the pattern of the invariance lemmas of
[Lattices.Semidistributive][]: move the hypothesis into `𝑳`{.AgdaBound} along
the injective homomorphism `h`, apply the law there, and move the conclusion
back by injectivity, rewriting `h` past the operations with
`hom-preserves-∧`{.AgdaFunction} and `hom-preserves-∨`{.AgdaFunction}.  For the
modular law the hypothesis `x ≤ z` goes to `h x ≤ h z` by monotonicity
(`hom-preserves-≤`{.AgdaFunction}).

```agda
module _ (𝑲 : Lattice α ρᵃ) (𝑳 : Lattice β ρᵇ) (sub : proj₁ 𝑲 IsSubalgebraOf proj₁ 𝑳) where
  open Lattice-Op 𝑲          using () renaming ( _∧_ to _∧ᴷ_ ; _∨_ to _∨ᴷ_ )
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( refl )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  private
    h : hom (proj₁ 𝑲) (proj₁ 𝑳)
    h = proj₁ sub

    f : 𝕌[ proj₁ 𝑲 ] → 𝕌[ proj₁ 𝑳 ]
    f = proj₁ h ⟨$⟩_

  IsModular-S-invar : IsModular 𝑳 → IsModular 𝑲
  IsModular-S-invar m x y z x≤z = proj₂ sub (begin
    f (x ∨ᴷ (y ∧ᴷ z))   ≈⟨ hom-preserves-∨ 𝑲 𝑳 h x (y ∧ᴷ z) ⟩
    f x ∨ f (y ∧ᴷ z)    ≈⟨ ∨-cong refl (hom-preserves-∧ 𝑲 𝑳 h y z) ⟩
    f x ∨ (f y ∧ f z)   ≈⟨ m (f x) (f y) (f z) (hom-preserves-≤ 𝑲 𝑳 h x≤z) ⟩
    (f x ∨ f y) ∧ f z   ≈˘⟨ ∧-cong (hom-preserves-∨ 𝑲 𝑳 h x y) refl ⟩
    f (x ∨ᴷ y) ∧ f z    ≈˘⟨ hom-preserves-∧ 𝑲 𝑳 h (x ∨ᴷ y) z ⟩
    f ((x ∨ᴷ y) ∧ᴷ z)   ∎)

  IsDistributive-S-invar : IsDistributive 𝑳 → IsDistributive 𝑲
  IsDistributive-S-invar d x y z = proj₂ sub (begin
    f (x ∧ᴷ (y ∨ᴷ z))          ≈⟨ hom-preserves-∧ 𝑲 𝑳 h x (y ∨ᴷ z) ⟩
    f x ∧ f (y ∨ᴷ z)           ≈⟨ ∧-cong refl (hom-preserves-∨ 𝑲 𝑳 h y z) ⟩
    f x ∧ (f y ∨ f z)          ≈⟨ d (f x) (f y) (f z) ⟩
    (f x ∧ f y) ∨ (f x ∧ f z)  ≈˘⟨ ∨-cong (hom-preserves-∧ 𝑲 𝑳 h x y) (hom-preserves-∧ 𝑲 𝑳 h x z) ⟩
    f (x ∧ᴷ y) ∨ f (x ∧ᴷ z)    ≈˘⟨ hom-preserves-∨ 𝑲 𝑳 h (x ∧ᴷ y) (x ∧ᴷ z) ⟩
    f ((x ∧ᴷ y) ∨ᴷ (x ∧ᴷ z))   ∎)
```

#### Isomorphic lattices

As in [Lattices.Semidistributive][], invariance under isomorphism is the
sublattice case applied to the inverse, from the left-hand side of the
isomorphism to the right.

```agda
module _ (𝑲 : Lattice α ρᵃ) (𝑳 : Lattice β ρᵇ) (φ : proj₁ 𝑲 ≅ proj₁ 𝑳) where
  private
    sub : proj₁ 𝑳 IsSubalgebraOf proj₁ 𝑲
    sub = ≅→≤ (≅-sym φ)

  IsModular-I-invar : IsModular 𝑲 → IsModular 𝑳
  IsModular-I-invar = IsModular-S-invar 𝑳 𝑲 sub

  IsDistributive-I-invar : IsDistributive 𝑲 → IsDistributive 𝑳
  IsDistributive-I-invar = IsDistributive-S-invar 𝑳 𝑲 sub
```

#### Deciding the conditions in a finite lattice

In a finite lattice with decidable equality both conditions are decidable by a
sweep over triples, `all³?`{.AgdaFunction} of [Setoid.Algebras.Finite][], as
the semidistributive laws are in [Lattices.Semidistributive][]: the modular law
through its identity form, whose instances `MI-at x y z`{.AgdaFunction} have
no hypothesis, and the distributive law directly.  Each instance respects `≈`
in each argument (`MI-resp`{.AgdaFunction}, `D-resp`{.AgdaFunction}).

The sweep evaluates the lattice's own operations.  When they are expensive to
evaluate but agree, up to `≈`, with cheaper functions `_∧′_` and `_∨′_` (a
lattice built order-first from a slow construction is the case in point), the
decisions `isModular-by?`{.AgdaFunction} and `isDistributive-by?`{.AgdaFunction}
compare the two sides of each instance computed with the cheaper functions, and
carry the answer back to the lattice's operations by the agreement and the
congruence of the operations.  The verdict is about `𝑳`{.AgdaBound} itself;
only the computation changes.  `isModular?`{.AgdaFunction} and
`isDistributive?`{.AgdaFunction} are the special case in which the cheaper
functions are the operations themselves.  A lattice with `n` enumerated
elements costs `n³` instances for each.

A negative verdict is a refutation `¬ IsModular 𝑳`, a function
`IsModular 𝑳 → ⊥`, from which no triple can be read; but in a finite lattice
the failure can be found.
`modularFailure`{.AgdaFunction} and `distributiveFailure`{.AgdaFunction} run
the search: a refutation of the law refutes the sweep over the enumeration, and
`¬∀⟶∃¬`{.AgdaFunction} of the standard library, applied once per variable with
the decisions of the inner sweeps, finds an enumerated triple at which the
instance fails.  For the modular law, a failure of the identity at `x`, `y`,
`z` is a failure of the law at `x ≤ x ∨ z`, `y`.

```agda
module _ (𝑳 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑳)) where
  open FiniteAlgebra 𝑭      using ( _≟_ ; card ; enum )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong )
  open Lattice-Order 𝑳      using ( ∨-upperˡ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; refl ; sym ; trans )

  private
    U : Type α
    U = 𝕌[ proj₁ 𝑳 ]

    MI-at D-at : U → U → U → Type ρ
    MI-at x y z = x ∨ (y ∧ (x ∨ z)) ≈ (x ∨ y) ∧ (x ∨ z)
    D-at  x y z = x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)

    MI-resp : ∀ {x x' y y' z z'} → x ≈ x' → y ≈ y' → z ≈ z' → MI-at x y z → MI-at x' y' z'
    MI-resp x≈ y≈ z≈ e =
      trans (sym (∨-cong x≈ (∧-cong y≈ (∨-cong x≈ z≈))))
            (trans e (∧-cong (∨-cong x≈ y≈) (∨-cong x≈ z≈)))

    D-resp : ∀ {x x' y y' z z'} → x ≈ x' → y ≈ y' → z ≈ z' → D-at x y z → D-at x' y' z'
    D-resp x≈ y≈ z≈ e =
      trans (sym (∧-cong x≈ (∨-cong y≈ z≈)))
            (trans e (∨-cong (∧-cong x≈ y≈) (∧-cong x≈ z≈)))

  module _ (_∧′_ _∨′_ : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ])
           (∧≈ : ∀ x y → x ∧ y ≈ x ∧′ y) (∨≈ : ∀ x y → x ∨ y ≈ x ∨′ y) where
    private
      -- Each side of an instance, computed with the cheaper functions.
      mi-lhs : ∀ x y z → x ∨ (y ∧ (x ∨ z)) ≈ x ∨′ (y ∧′ (x ∨′ z))
      mi-lhs x y z = trans (∨-cong refl (trans (∧-cong refl (∨≈ x z)) (∧≈ y (x ∨′ z))))
                           (∨≈ x (y ∧′ (x ∨′ z)))

      mi-rhs : ∀ x y z → (x ∨ y) ∧ (x ∨ z) ≈ (x ∨′ y) ∧′ (x ∨′ z)
      mi-rhs x y z = trans (∧-cong (∨≈ x y) (∨≈ x z)) (∧≈ (x ∨′ y) (x ∨′ z))

      d-lhs : ∀ x y z → x ∧ (y ∨ z) ≈ x ∧′ (y ∨′ z)
      d-lhs x y z = trans (∧-cong refl (∨≈ y z)) (∧≈ x (y ∨′ z))

      d-rhs : ∀ x y z → (x ∧ y) ∨ (x ∧ z) ≈ (x ∧′ y) ∨′ (x ∧′ z)
      d-rhs x y z = trans (∨-cong (∧≈ x y) (∧≈ x z)) (∨≈ (x ∧′ y) (x ∧′ z))

      -- An equation between the two sides holds for one computation iff for the other.
      transport : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → a' ≈ b' → a ≈ b
      transport a≈ b≈ e = trans a≈ (trans e (sym b≈))

      untransport : ∀ {a a' b b'} → a ≈ a' → b ≈ b' → a ≈ b → a' ≈ b'
      untransport a≈ b≈ e = trans (sym a≈) (trans e b≈)

    modularIdentity-by? : Dec (ModularIdentity 𝑳)
    modularIdentity-by? = all³? 𝑭 MI-at MI-resp λ x y z →
      map′ (transport (mi-lhs x y z) (mi-rhs x y z)) (untransport (mi-lhs x y z) (mi-rhs x y z))
           ((x ∨′ (y ∧′ (x ∨′ z))) ≟ ((x ∨′ y) ∧′ (x ∨′ z)))

    isModular-by? : Dec (IsModular 𝑳)
    isModular-by? =
      map′ (ModularIdentity→IsModular 𝑳) (IsModular→ModularIdentity 𝑳) modularIdentity-by?

    isDistributive-by? : Dec (IsDistributive 𝑳)
    isDistributive-by? = all³? 𝑭 D-at D-resp λ x y z →
      map′ (transport (d-lhs x y z) (d-rhs x y z)) (untransport (d-lhs x y z) (d-rhs x y z))
           ((x ∧′ (y ∨′ z)) ≟ ((x ∧′ y) ∨′ (x ∧′ z)))

  isModular? : Dec (IsModular 𝑳)
  isModular? = isModular-by? _∧_ _∨_ (λ _ _ → refl) (λ _ _ → refl)

  isDistributive? : Dec (IsDistributive 𝑳)
  isDistributive? = isDistributive-by? _∧_ _∨_ (λ _ _ → refl) (λ _ _ → refl)

  private
    -- A triple of enumerated elements at which a decidable instance fails.
    counterexample : (P : U → U → U → Type ρ) → (∀ x y z → Dec (P x y z))
      → ¬ (∀ i j k → P (enum i) (enum j) (enum k)) → ∃[ x ] ∃[ y ] ∃[ z ] ¬ P x y z
    counterexample P P? ¬all =
      let (i , ¬i) = ¬∀⟶∃¬ card _ (λ i → all? λ j → all? λ k → P? (enum i) (enum j) (enum k)) ¬all
          (j , ¬j) = ¬∀⟶∃¬ card _ (λ j → all? λ k → P? (enum i) (enum j) (enum k)) ¬i
          (k , ¬k) = ¬∀⟶∃¬ card _ (λ k → P? (enum i) (enum j) (enum k)) ¬j
      in enum i , enum j , enum k , ¬k

  -- A refutation of the modular law yields a triple at which it fails.
  modularFailure : ¬ IsModular 𝑳 → ModularFailure 𝑳
  modularFailure ¬m =
    let (x , y , z , ¬e) = counterexample MI-at (λ x y z → (x ∨ (y ∧ (x ∨ z))) ≟ ((x ∨ y) ∧ (x ∨ z)))
                             λ h → ¬m (ModularIdentity→IsModular 𝑳 (enum-all³ 𝑭 MI-at MI-resp h))
    in x , y , x ∨ z , ∨-upperˡ , ¬e

  -- A refutation of the distributive law yields a triple at which it fails.
  distributiveFailure : ¬ IsDistributive 𝑳 → DistributiveFailure 𝑳
  distributiveFailure ¬d =
    counterexample D-at (λ x y z → (x ∧ (y ∨ z)) ≟ ((x ∧ y) ∨ (x ∧ z)))
                   λ h → ¬d (enum-all³ 𝑭 D-at D-resp h)
```
