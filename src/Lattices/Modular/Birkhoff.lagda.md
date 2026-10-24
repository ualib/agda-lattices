---
layout: default
file: "src/Lattices/Modular/Birkhoff.lagda.md"
title: "Lattices.Modular.Birkhoff module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Birkhoff's criterion: a modular lattice is distributive iff it has no diamond

This is the [Lattices.Modular.Birkhoff][] module of the [agda-lattices][] library.

Birkhoff's theorem ([Birkhoff (1933)][]; [Davey and Priestley (2002)][],
Theorem 4.10) says that a modular lattice is distributive if and only if
it has no sublattice isomorphic to the diamond `M₃` of
[Lattices.Examples.M3][].  With Dedekind's theorem of
[Lattices.Modular.Dedekind][] it gives the M₃-N₅ theorem: a lattice is
distributive if and only if it has neither a pentagon nor a diamond.  As for
Dedekind's theorem, one direction is invariance
(`IsDistributive-S-invar`{.AgdaFunction} of [Lattices.Modular][]) and the
failure of distributivity in `M₃`, and the other is a construction.

Read constructively, the theorem has the following parts:

+  **The construction**.  In a modular lattice, from a witnessed failure of
   distributivity, `DistributiveFailure 𝑳`{.AgdaFunction}, an embedding of
   `M₃` (`birkhoff`{.AgdaFunction}).  It assumes modularity and nothing else.
+  **The easy direction**.  A distributive lattice has no diamond
   (`IsDistributive→¬Embeds-M₃`{.AgdaFunction}), for any lattice.
+  **The converse**.  A modular lattice with no diamond satisfies every
   instance of the distributive law up to double negation, and is
   distributive outright when its equality is decidable
   (`¬Embeds-M₃→IsDistributive`{.AgdaFunction}).
+  **The M₃-N₅ theorem**, for a lattice with decidable equality
   (`M₃-N₅-theorem`{.AgdaFunction}), and its finite form, which decides a
   finite lattice and produces the forbidden sublattice when it is not
   distributive (`distributive-or-N₅-or-M₃`{.AgdaFunction}).

The construction runs through the *median polynomials* of a triple,

    u = (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x)    and    v = (x ∨ y) ∧ (y ∨ z) ∧ (z ∨ x),

for which `u ≤ v` in every lattice.  A lattice is distributive if and only if
`u = v` for every triple.  The half that says a distributive lattice satisfies
this *median identity* is classical and is not needed here.  This module proves
the other half, in the pointwise form the construction needs: in a modular
lattice, `u ≈ v` at `x`, `y`, `z` implies the distributive law at the same
triple, since `x ∧ (y ∨ z) ≈ x ∧ v` and `x ∧ u ≈ (x ∧ y) ∨ (x ∧ z)`
(`median→distributive`{.AgdaFunction}).  So a failure of distributivity at a
triple is a triple with `u ≉ v`.  Then `x' = (x ∧ v) ∨ u`, `y' = (y ∧ v) ∨ u`
and `z' = (z ∧ v) ∨ u`, between `u` and `v`, are three elements any two of
which meet to `u` and join to `v` (`median-pair`{.AgdaFunction}), and the five
elements `u, x', y', z', v` form a diamond.  As for the pentagon, the diamond is
a configuration, a `Diamond`{.AgdaRecord}: five elements `⊥, a, b, c, ⊤` with
the three meets of distinct atoms `⊥`, the three joins `⊤`, and `⊥ ≉ ⊤`;
`Diamond→Embeds`{.AgdaFunction} shows that every one is an embedding of `M₃`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Modular.Birkhoff where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ) renaming ( refl to ≡-refl )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; from-yes ; from-no )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )

-- Imports from this library ----------------------------------------------------
open import Lattices.Examples.M3        using ( M₃ ; M₃-laws ; M₃-finite )
                                        renaming ( _∧_ to _∧³_ ; _∨_ to _∨³_ )
open import Lattices.Examples.N5        using ( N₅ )
open import Lattices.Modular            using ( IsModular ; IsDistributive ; DistributiveFailure
                                              ; IsDistributive→IsModular ; IsDistributive-S-invar
                                              ; isModular? ; isDistributive? ; distributiveFailure )
open import Lattices.Modular.Dedekind   using ( IsModular→¬Embeds-N₅ ; ¬Embeds-N₅→IsModular
                                              ; modular-or-N₅ )
open import Lattices.Nation             using ( Embeds )
open import Lattices.Table              using ( tableHom )

private variable α ρ : Level
```
-->

#### The diamond is modular and not distributive

`M₃` is modular and not distributive, by the decisions of
[Lattices.Modular][]; its failure of distributivity is the one of the
introduction to [Lattices.Examples.Mn][]: `a ∧ (b ∨ c) = a ∧ ⊤ = a` and
`(a ∧ b) ∨ (a ∧ c) = ⊥ ∨ ⊥ = ⊥` (`M₃-distributive-failure`{.AgdaFunction}, by
evaluation).

```agda
M₃-modular : IsModular M₃
M₃-modular = from-yes (isModular? M₃ M₃-finite)

M₃-not-distributive : ¬ IsDistributive M₃
M₃-not-distributive = from-no (isDistributive? M₃ M₃-finite)

-- a ∧ (b ∨ c) = a differs from (a ∧ b) ∨ (a ∧ c) = ⊥.
M₃-distributive-failure : DistributiveFailure M₃
M₃-distributive-failure = 1F , 2F , 3F , λ ()
```

#### The easy direction

```agda
module _ (𝑳 : Lattice α ρ) where

  IsDistributive→¬Embeds-M₃ : IsDistributive 𝑳 → ¬ Embeds M₃ 𝑳
  IsDistributive→¬Embeds-M₃ d emb = M₃-not-distributive (IsDistributive-S-invar M₃ 𝑳 emb d)
```

#### Diamonds

A `Diamond`{.AgdaRecord} in `𝑳`{.AgdaBound} is the configuration of the
introduction.  The bottom lies below the three atoms and the top above them,
since `⊥ ≈ a ∧ b ≈ b ∧ c` and `⊤ ≈ a ∨ b ≈ b ∨ c`; these six inequalities and
`⊥ ≤ ⊤` are all the comparabilities in `M₃`.

```agda
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                                   ; ∧-idem-law ; ∨-idem-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-refl ; ≤-reflexive ; ≤-trans ; ≤-antisym
                                   ; ≤-respˡ-≈ ; ≤-respʳ-≈
                                   ; ≤-via-∨ ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest
                                   ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  -- Five elements of 𝑳 in the configuration of M₃: three atoms, pairwise complements.
  record Diamond : Type (α ⊔ ρ) where
    field
      ⊥ a b c ⊤  : 𝕌[ proj₁ 𝑳 ]
      a∧b≈⊥      : a ∧ b ≈ ⊥
      b∧c≈⊥      : b ∧ c ≈ ⊥
      a∧c≈⊥      : a ∧ c ≈ ⊥
      a∨b≈⊤      : a ∨ b ≈ ⊤
      b∨c≈⊤      : b ∨ c ≈ ⊤
      a∨c≈⊤      : a ∨ c ≈ ⊤
      ⊥≉⊤        : ¬ (⊥ ≈ ⊤)

  private
    meet-≤ : ∀ {x y} → x ≤ y → x ≈ x ∧ y
    meet-≤ = sym

    meet-≥ : ∀ {x y} → y ≤ x → y ≈ x ∧ y
    meet-≥ y≤x = trans (sym y≤x) ∧-comm-law

    join-≤ : ∀ {x y} → x ≤ y → y ≈ x ∨ y
    join-≤ x≤y = sym (≤-via-∨ x≤y)

    join-≥ : ∀ {x y} → y ≤ x → x ≈ x ∨ y
    join-≥ y≤x = trans (sym (≤-via-∨ y≤x)) ∨-comm-law

  module _ (D : Diamond) where
    open Diamond D

    private
      ⊥≤a : ⊥ ≤ a
      ⊥≤a = ≤-respˡ-≈ a∧b≈⊥ ∧-lowerˡ

      ⊥≤b : ⊥ ≤ b
      ⊥≤b = ≤-respˡ-≈ a∧b≈⊥ ∧-lowerʳ

      ⊥≤c : ⊥ ≤ c
      ⊥≤c = ≤-respˡ-≈ b∧c≈⊥ ∧-lowerʳ

      a≤⊤ : a ≤ ⊤
      a≤⊤ = ≤-respʳ-≈ a∨b≈⊤ ∨-upperˡ

      b≤⊤ : b ≤ ⊤
      b≤⊤ = ≤-respʳ-≈ a∨b≈⊤ ∨-upperʳ

      c≤⊤ : c ≤ ⊤
      c≤⊤ = ≤-respʳ-≈ b∨c≈⊤ ∨-upperʳ

      ⊥≤⊤ : ⊥ ≤ ⊤
      ⊥≤⊤ = ≤-trans ⊥≤a a≤⊤
```

The map `j`{.AgdaFunction} sends the elements of `M₃`, numbered as in
[Lattices.Examples.M3][] (`⊥, a, b, c, ⊤` as `0` to `4`), to the five elements
of the configuration, and commutes with both operations on all 25 pairs: on a
comparable pair by the order, on a pair of distinct atoms by the six equations,
up to commutativity.

```agda
      -- The images of ⊥, a, b, c, ⊤.
      j : Fin 5 → 𝕌[ proj₁ 𝑳 ]
      j 0F = ⊥
      j 1F = a
      j 2F = b
      j 3F = c
      j 4F = ⊤

      j-∧ : ∀ x y → j (x ∧³ y) ≈ j x ∧ j y
      j-∧ 0F 0F = sym ∧-idem-law
      j-∧ 0F 1F = meet-≤ ⊥≤a
      j-∧ 0F 2F = meet-≤ ⊥≤b
      j-∧ 0F 3F = meet-≤ ⊥≤c
      j-∧ 0F 4F = meet-≤ ⊥≤⊤
      j-∧ 1F 0F = meet-≥ ⊥≤a
      j-∧ 1F 1F = sym ∧-idem-law
      j-∧ 1F 2F = sym a∧b≈⊥
      j-∧ 1F 3F = sym a∧c≈⊥
      j-∧ 1F 4F = meet-≤ a≤⊤
      j-∧ 2F 0F = meet-≥ ⊥≤b
      j-∧ 2F 1F = sym (trans ∧-comm-law a∧b≈⊥)
      j-∧ 2F 2F = sym ∧-idem-law
      j-∧ 2F 3F = sym b∧c≈⊥
      j-∧ 2F 4F = meet-≤ b≤⊤
      j-∧ 3F 0F = meet-≥ ⊥≤c
      j-∧ 3F 1F = sym (trans ∧-comm-law a∧c≈⊥)
      j-∧ 3F 2F = sym (trans ∧-comm-law b∧c≈⊥)
      j-∧ 3F 3F = sym ∧-idem-law
      j-∧ 3F 4F = meet-≤ c≤⊤
      j-∧ 4F 0F = meet-≥ ⊥≤⊤
      j-∧ 4F 1F = meet-≥ a≤⊤
      j-∧ 4F 2F = meet-≥ b≤⊤
      j-∧ 4F 3F = meet-≥ c≤⊤
      j-∧ 4F 4F = sym ∧-idem-law

      j-∨ : ∀ x y → j (x ∨³ y) ≈ j x ∨ j y
      j-∨ 0F 0F = sym ∨-idem-law
      j-∨ 0F 1F = join-≤ ⊥≤a
      j-∨ 0F 2F = join-≤ ⊥≤b
      j-∨ 0F 3F = join-≤ ⊥≤c
      j-∨ 0F 4F = join-≤ ⊥≤⊤
      j-∨ 1F 0F = join-≥ ⊥≤a
      j-∨ 1F 1F = sym ∨-idem-law
      j-∨ 1F 2F = sym a∨b≈⊤
      j-∨ 1F 3F = sym a∨c≈⊤
      j-∨ 1F 4F = join-≤ a≤⊤
      j-∨ 2F 0F = join-≥ ⊥≤b
      j-∨ 2F 1F = sym (trans ∨-comm-law a∨b≈⊤)
      j-∨ 2F 2F = sym ∨-idem-law
      j-∨ 2F 3F = sym b∨c≈⊤
      j-∨ 2F 4F = join-≤ b≤⊤
      j-∨ 3F 0F = join-≥ ⊥≤c
      j-∨ 3F 1F = sym (trans ∨-comm-law a∨c≈⊤)
      j-∨ 3F 2F = sym (trans ∨-comm-law b∨c≈⊤)
      j-∨ 3F 3F = sym ∨-idem-law
      j-∨ 3F 4F = join-≤ c≤⊤
      j-∨ 4F 0F = join-≥ ⊥≤⊤
      j-∨ 4F 1F = join-≥ a≤⊤
      j-∨ 4F 2F = join-≥ b≤⊤
      j-∨ 4F 3F = join-≥ c≤⊤
      j-∨ 4F 4F = sym ∨-idem-law
```

The map is injective because any two of the five elements coinciding would
force `⊥ ≈ ⊤`.  Two equal atoms `p ≈ q` give `⊥ ≈ p ∧ q ≈ p ≈ p ∨ q ≈ ⊤`
(`atoms-collapse`{.AgdaFunction}).  An atom `p` equal to `⊥` makes each of the
other two atoms `q`, `r` equal to `⊤`, since `⊤ ≈ p ∨ q ≈ ⊥ ∨ q ≈ q`, and then
`⊥ ≈ q ∧ r ≈ ⊤` (`bottom-atom`{.AgdaFunction}); an atom equal to `⊤` is the
dual case (`top-atom`{.AgdaFunction}).

```agda
      atoms-collapse : ∀ {p q} → p ∧ q ≈ ⊥ → p ∨ q ≈ ⊤ → p ≈ q → ⊥ ≈ ⊤
      atoms-collapse {p} {q} p∧q≈⊥ p∨q≈⊤ p≈q = begin
        ⊥      ≈˘⟨ p∧q≈⊥ ⟩
        p ∧ q  ≈˘⟨ ∧-cong refl p≈q ⟩
        p ∧ p  ≈⟨ ∧-idem-law ⟩
        p      ≈˘⟨ ∨-idem-law ⟩
        p ∨ p  ≈⟨ ∨-cong refl p≈q ⟩
        p ∨ q  ≈⟨ p∨q≈⊤ ⟩
        ⊤      ∎

      bottom-atom : ∀ {p q r} → p ∨ q ≈ ⊤ → p ∨ r ≈ ⊤ → q ∧ r ≈ ⊥ → ⊥ ≤ q → ⊥ ≤ r
        → ⊥ ≈ p → ⊥ ≈ ⊤
      bottom-atom {p} {q} {r} p∨q≈⊤ p∨r≈⊤ q∧r≈⊥ ⊥≤q ⊥≤r ⊥≈p = begin
        ⊥      ≈˘⟨ q∧r≈⊥ ⟩
        q ∧ r  ≈⟨ ∧-cong (to-⊤ p∨q≈⊤ ⊥≤q) (to-⊤ p∨r≈⊤ ⊥≤r) ⟩
        ⊤ ∧ ⊤  ≈⟨ ∧-idem-law ⟩
        ⊤      ∎
        where
        to-⊤ : ∀ {s} → p ∨ s ≈ ⊤ → ⊥ ≤ s → s ≈ ⊤
        to-⊤ {s} p∨s≈⊤ ⊥≤s = begin
          s      ≈˘⟨ ≤-via-∨ ⊥≤s ⟩
          ⊥ ∨ s  ≈⟨ ∨-cong ⊥≈p refl ⟩
          p ∨ s  ≈⟨ p∨s≈⊤ ⟩
          ⊤      ∎

      top-atom : ∀ {p q r} → p ∧ q ≈ ⊥ → p ∧ r ≈ ⊥ → q ∨ r ≈ ⊤ → q ≤ ⊤ → r ≤ ⊤
        → p ≈ ⊤ → ⊥ ≈ ⊤
      top-atom {p} {q} {r} p∧q≈⊥ p∧r≈⊥ q∨r≈⊤ q≤⊤ r≤⊤ p≈⊤ = begin
        ⊥      ≈˘⟨ ∨-idem-law ⟩
        ⊥ ∨ ⊥  ≈˘⟨ ∨-cong (to-⊥ p∧q≈⊥ q≤⊤) (to-⊥ p∧r≈⊥ r≤⊤) ⟩
        q ∨ r  ≈⟨ q∨r≈⊤ ⟩
        ⊤      ∎
        where
        to-⊥ : ∀ {s} → p ∧ s ≈ ⊥ → s ≤ ⊤ → s ≈ ⊥
        to-⊥ {s} p∧s≈⊥ s≤⊤ = begin
          s      ≈˘⟨ trans ∧-comm-law s≤⊤ ⟩
          ⊤ ∧ s  ≈˘⟨ ∧-cong p≈⊤ refl ⟩
          p ∧ s  ≈⟨ p∧s≈⊥ ⟩
          ⊥      ∎

      -- The commuted forms the cases need.
      b∧a≈⊥ : b ∧ a ≈ ⊥
      b∧a≈⊥ = trans ∧-comm-law a∧b≈⊥

      c∧a≈⊥ : c ∧ a ≈ ⊥
      c∧a≈⊥ = trans ∧-comm-law a∧c≈⊥

      c∧b≈⊥ : c ∧ b ≈ ⊥
      c∧b≈⊥ = trans ∧-comm-law b∧c≈⊥

      b∨a≈⊤ : b ∨ a ≈ ⊤
      b∨a≈⊤ = trans ∨-comm-law a∨b≈⊤

      c∨a≈⊤ : c ∨ a ≈ ⊤
      c∨a≈⊤ = trans ∨-comm-law a∨c≈⊤

      c∨b≈⊤ : c ∨ b ≈ ⊤
      c∨b≈⊤ = trans ∨-comm-law b∨c≈⊤

      ⊥≈a→ : ⊥ ≈ a → ⊥ ≈ ⊤
      ⊥≈a→ = bottom-atom a∨b≈⊤ a∨c≈⊤ b∧c≈⊥ ⊥≤b ⊥≤c

      ⊥≈b→ : ⊥ ≈ b → ⊥ ≈ ⊤
      ⊥≈b→ = bottom-atom b∨a≈⊤ b∨c≈⊤ a∧c≈⊥ ⊥≤a ⊥≤c

      ⊥≈c→ : ⊥ ≈ c → ⊥ ≈ ⊤
      ⊥≈c→ = bottom-atom c∨a≈⊤ c∨b≈⊤ a∧b≈⊥ ⊥≤a ⊥≤b

      a≈⊤→ : a ≈ ⊤ → ⊥ ≈ ⊤
      a≈⊤→ = top-atom a∧b≈⊥ a∧c≈⊥ b∨c≈⊤ b≤⊤ c≤⊤

      b≈⊤→ : b ≈ ⊤ → ⊥ ≈ ⊤
      b≈⊤→ = top-atom b∧a≈⊥ b∧c≈⊥ a∨c≈⊤ a≤⊤ c≤⊤

      c≈⊤→ : c ≈ ⊤ → ⊥ ≈ ⊤
      c≈⊤→ = top-atom c∧a≈⊥ c∧b≈⊥ a∨b≈⊤ a≤⊤ b≤⊤

      j-injective : ∀ x y → j x ≈ j y → x ≡ y
      j-injective 0F 0F _ = ≡-refl
      j-injective 0F 1F e = ⊥-elim (⊥≉⊤ (⊥≈a→ e))
      j-injective 0F 2F e = ⊥-elim (⊥≉⊤ (⊥≈b→ e))
      j-injective 0F 3F e = ⊥-elim (⊥≉⊤ (⊥≈c→ e))
      j-injective 0F 4F e = ⊥-elim (⊥≉⊤ e)
      j-injective 1F 0F e = ⊥-elim (⊥≉⊤ (⊥≈a→ (sym e)))
      j-injective 1F 1F _ = ≡-refl
      j-injective 1F 2F e = ⊥-elim (⊥≉⊤ (atoms-collapse a∧b≈⊥ a∨b≈⊤ e))
      j-injective 1F 3F e = ⊥-elim (⊥≉⊤ (atoms-collapse a∧c≈⊥ a∨c≈⊤ e))
      j-injective 1F 4F e = ⊥-elim (⊥≉⊤ (a≈⊤→ e))
      j-injective 2F 0F e = ⊥-elim (⊥≉⊤ (⊥≈b→ (sym e)))
      j-injective 2F 1F e = ⊥-elim (⊥≉⊤ (atoms-collapse b∧a≈⊥ b∨a≈⊤ e))
      j-injective 2F 2F _ = ≡-refl
      j-injective 2F 3F e = ⊥-elim (⊥≉⊤ (atoms-collapse b∧c≈⊥ b∨c≈⊤ e))
      j-injective 2F 4F e = ⊥-elim (⊥≉⊤ (b≈⊤→ e))
      j-injective 3F 0F e = ⊥-elim (⊥≉⊤ (⊥≈c→ (sym e)))
      j-injective 3F 1F e = ⊥-elim (⊥≉⊤ (atoms-collapse c∧a≈⊥ c∨a≈⊤ e))
      j-injective 3F 2F e = ⊥-elim (⊥≉⊤ (atoms-collapse c∧b≈⊥ c∨b≈⊤ e))
      j-injective 3F 3F _ = ≡-refl
      j-injective 3F 4F e = ⊥-elim (⊥≉⊤ (c≈⊤→ e))
      j-injective 4F 0F e = ⊥-elim (⊥≉⊤ (sym e))
      j-injective 4F 1F e = ⊥-elim (⊥≉⊤ (a≈⊤→ (sym e)))
      j-injective 4F 2F e = ⊥-elim (⊥≉⊤ (b≈⊤→ (sym e)))
      j-injective 4F 3F e = ⊥-elim (⊥≉⊤ (c≈⊤→ (sym e)))
      j-injective 4F 4F _ = ≡-refl

    -- A diamond in 𝑳 is an embedding of M₃.
    Diamond→Embeds : Embeds M₃ 𝑳
    Diamond→Embeds = tableHom M₃-laws 𝑳 j j-∧ j-∨ , λ {x} {y} → j-injective x y
```

#### The median polynomials

`u`{.AgdaFunction} and `v`{.AgdaFunction} are the median polynomials of the
introduction.  The construction never looks inside them: it uses only that
`u` is the join of `x ∧ y`, `y ∧ z` and `z ∧ x` (an upper bound of the three,
below every upper bound; `IsJoin₃`{.AgdaFunction}) and that `v` is the meet of
`x ∨ y`, `y ∨ z` and `z ∨ x` (`IsMeet₃`{.AgdaFunction}).  Both properties are
invariant under a cyclic shift of the three arguments
(`IsJoin₃-rotate`{.AgdaFunction}, `IsMeet₃-rotate`{.AgdaFunction}), which
shifts `x ∧ y, y ∧ z, z ∧ x` cyclically.  So a lemma proved for the pair
`x', y'` at the triple `x, y, z` applies at `y, z, x` to the pair `y', z'`, and
at `z, x, y` to `z', x'`, with the same `u` and `v` and no rearrangement of
joins or meets.

```agda
  -- u is the join of s, t and w.
  IsJoin₃ : (u s t w : 𝕌[ proj₁ 𝑳 ]) → Type (α ⊔ ρ)
  IsJoin₃ u s t w = (s ≤ u × t ≤ u × w ≤ u) × (∀ {e} → s ≤ e → t ≤ e → w ≤ e → u ≤ e)

  -- v is the meet of s, t and w.
  IsMeet₃ : (v s t w : 𝕌[ proj₁ 𝑳 ]) → Type (α ⊔ ρ)
  IsMeet₃ v s t w = (v ≤ s × v ≤ t × v ≤ w) × (∀ {e} → e ≤ s → e ≤ t → e ≤ w → e ≤ v)

  IsJoin₃-rotate : ∀ {u s t w} → IsJoin₃ u s t w → IsJoin₃ u t w s
  IsJoin₃-rotate ((s≤ , t≤ , w≤) , least) = (t≤ , w≤ , s≤) , λ t≤e w≤e s≤e → least s≤e t≤e w≤e

  IsMeet₃-rotate : ∀ {v s t w} → IsMeet₃ v s t w → IsMeet₃ v t w s
  IsMeet₃-rotate ((≤s , ≤t , ≤w) , greatest) = (≤t , ≤w , ≤s) , λ e≤t e≤w e≤s → greatest e≤s e≤t e≤w

  -- The median polynomials of a triple.
  u v : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ]
  u x y z = (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x)
  v x y z = (x ∨ y) ∧ (y ∨ z) ∧ (z ∨ x)

  u-isJoin₃ : ∀ x y z → IsJoin₃ (u x y z) (x ∧ y) (y ∧ z) (z ∧ x)
  u-isJoin₃ x y z = (≤-trans ∨-upperˡ ∨-upperˡ , ≤-trans ∨-upperʳ ∨-upperˡ , ∨-upperʳ)
                  , λ s≤e t≤e w≤e → ∨-least (∨-least s≤e t≤e) w≤e

  v-isMeet₃ : ∀ x y z → IsMeet₃ (v x y z) (x ∨ y) (y ∨ z) (z ∨ x)
  v-isMeet₃ x y z = (≤-trans ∧-lowerˡ ∧-lowerˡ , ≤-trans ∧-lowerˡ ∧-lowerʳ , ∧-lowerʳ)
                  , λ e≤s e≤t e≤w → ∧-greatest (∧-greatest e≤s e≤t) e≤w
```

The rest of the construction assumes that `𝑳`{.AgdaBound} is modular, and
works with any `U` and `V` that are the join of `x ∧ y`, `y ∧ z`, `z ∧ x` and
the meet of `x ∨ y`, `y ∨ z`, `z ∨ x`.  First, `U ≤ V` in every lattice, since
each of the three meets lies below each of the three joins.  Write
`p = (x ∧ V) ∨ U` and `q = (y ∧ V) ∨ U`; the claim (`median-pair`{.AgdaFunction})
is that `p ∧ q ≈ U` and `p ∨ q ≈ V`.  The computation is that of
[Davey and Priestley (2002)][], proof of Theorem 4.10, arranged as inequalities,
with each use of the modular law named.

+  **The meet**.  `U` lies below `p` and `q`.  Conversely, the modular law at
   `U ≤ q` gives `p ∧ q ≈ U ∨ ((x ∧ V) ∧ q)`, so it suffices that
   `(x ∧ V) ∧ q ≤ U`.  Let `w = (z ∧ x) ∨ (y ∧ (z ∨ x))`.  Then `q ≤ w`,
   since `y ∧ V ≤ y ∧ (z ∨ x)` and each of the three meets that make up `U`
   lies below `w`.  The modular law at `z ∧ x ≤ x` gives
   `x ∧ w ≈ (z ∧ x) ∨ ((y ∧ (z ∨ x)) ∧ x)`, which lies below `U`, since
   `(y ∧ (z ∨ x)) ∧ x ≤ x ∧ y`.  So `(x ∧ V) ∧ q ≤ x ∧ q ≤ x ∧ w ≤ U`.
+  **The join**.  `p` and `q` lie below `V`.  Conversely, the modular law at
   `U ≤ V` gives `q ≈ (U ∨ y) ∧ V`; call the right-hand side `q*`.  Let
   `w* = (y ∨ (z ∧ x)) ∧ (z ∨ x)`, the dual of `w`.  Then `w* ≤ q*`, since
   `w* ≤ y ∨ (z ∧ x) ≤ U ∨ y` and `w*` lies below each of the three joins
   that make up `V`.  The modular law at `x ≤ z ∨ x` gives
   `x ∨ w* ≈ (x ∨ (y ∨ (z ∧ x))) ∧ (z ∨ x)`, which lies above `V`.  So
   `V ≤ x ∨ w* ≤ x ∨ q*`, hence `V ≤ (x ∨ q*) ∧ V`, and the modular law at
   `q* ≤ V` gives `(q* ∨ x) ∧ V ≈ q* ∨ (x ∧ V)`, which lies below `q ∨ p`.

```agda
  module _ (m : IsModular 𝑳) where
    private
      -- The modular law at p ≤ r.
      mod : ∀ {p q r} → p ≤ r → p ∨ (q ∧ r) ≈ (p ∨ q) ∧ r
      mod {p} {q} {r} = m p q r

    module _ {x y z U V : 𝕌[ proj₁ 𝑳 ]}
             (uJ : IsJoin₃ U (x ∧ y) (y ∧ z) (z ∧ x)) (vM : IsMeet₃ V (x ∨ y) (y ∨ z) (z ∨ x)) where
      private
        xy≤U : x ∧ y ≤ U
        xy≤U = proj₁ (proj₁ uJ)

        zx≤U : z ∧ x ≤ U
        zx≤U = proj₂ (proj₂ (proj₁ uJ))

        U-least : ∀ {e} → x ∧ y ≤ e → y ∧ z ≤ e → z ∧ x ≤ e → U ≤ e
        U-least = proj₂ uJ

        V≤xy : V ≤ x ∨ y
        V≤xy = proj₁ (proj₁ vM)

        V≤yz : V ≤ y ∨ z
        V≤yz = proj₁ (proj₂ (proj₁ vM))

        V≤zx : V ≤ z ∨ x
        V≤zx = proj₂ (proj₂ (proj₁ vM))

        V-greatest : ∀ {e} → e ≤ x ∨ y → e ≤ y ∨ z → e ≤ z ∨ x → e ≤ V
        V-greatest = proj₂ vM

      U≤V : U ≤ V
      U≤V = U-least (V-greatest (≤-trans ∧-lowerˡ ∨-upperˡ) (≤-trans ∧-lowerʳ ∨-upperˡ)
                                (≤-trans ∧-lowerˡ ∨-upperʳ))
                    (V-greatest (≤-trans ∧-lowerˡ ∨-upperʳ) (≤-trans ∧-lowerˡ ∨-upperˡ)
                                (≤-trans ∧-lowerʳ ∨-upperˡ))
                    (V-greatest (≤-trans ∧-lowerʳ ∨-upperˡ) (≤-trans ∧-lowerˡ ∨-upperʳ)
                                (≤-trans ∧-lowerˡ ∨-upperˡ))

      private
        p q w w* q* : 𝕌[ proj₁ 𝑳 ]
        p  = (x ∧ V) ∨ U
        q  = (y ∧ V) ∨ U
        w  = (z ∧ x) ∨ (y ∧ (z ∨ x))
        w* = (y ∨ (z ∧ x)) ∧ (z ∨ x)
        q* = (U ∨ y) ∧ V

        q≤w : q ≤ w
        q≤w = ∨-least (≤-trans (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ V≤zx)) ∨-upperʳ)
                      (U-least (≤-trans (∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ ∨-upperʳ)) ∨-upperʳ)
                               (≤-trans (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ ∨-upperˡ)) ∨-upperʳ)
                               ∨-upperˡ)

        x∧w≤U : x ∧ w ≤ U
        x∧w≤U = ≤-respˡ-≈ (sym (trans ∧-comm-law (sym (mod ∧-lowerʳ))))
                          (∨-least zx≤U
                                   (≤-trans (∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ ∧-lowerˡ)) xy≤U))

        p∧q≤U : p ∧ q ≤ U
        p∧q≤U = ≤-respˡ-≈ (sym p∧q≈) (∨-least ≤-refl
                  (≤-trans (∧-greatest (≤-trans ∧-lowerˡ ∧-lowerˡ) ∧-lowerʳ)
                           (≤-trans (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ q≤w)) x∧w≤U)))
          where
          p∧q≈ : p ∧ q ≈ U ∨ ((x ∧ V) ∧ q)
          p∧q≈ = trans (∧-cong ∨-comm-law refl) (sym (mod ∨-upperʳ))

        q*≈q : q* ≈ q
        q*≈q = trans (sym (mod U≤V)) ∨-comm-law

        w*≤q* : w* ≤ q*
        w*≤q* = ∧-greatest (≤-trans ∧-lowerˡ (∨-least ∨-upperʳ (≤-trans zx≤U ∨-upperˡ)))
                           (V-greatest (≤-trans ∧-lowerˡ (∨-least ∨-upperʳ (≤-trans ∧-lowerʳ ∨-upperˡ)))
                                       (≤-trans ∧-lowerˡ (∨-least ∨-upperˡ (≤-trans ∧-lowerˡ ∨-upperʳ)))
                                       ∧-lowerʳ)

        V≤x∨w* : V ≤ x ∨ w*
        V≤x∨w* = ≤-respʳ-≈ (sym (mod ∨-upperʳ))
                   (∧-greatest (≤-trans V≤xy (∨-least ∨-upperˡ (≤-trans ∨-upperˡ ∨-upperʳ))) V≤zx)

        V≤p∨q : V ≤ p ∨ q
        V≤p∨q = ≤-trans (≤-respʳ-≈ (trans (∧-cong ∨-comm-law refl) (sym (mod ∧-lowerʳ))) V≤∧V)
                        (∨-least (≤-trans (≤-reflexive q*≈q) ∨-upperʳ) (≤-trans ∨-upperˡ ∨-upperˡ))
          where
          V≤∧V : V ≤ (x ∨ q*) ∧ V
          V≤∧V = ∧-greatest (≤-trans V≤x∨w* (∨-least ∨-upperˡ (≤-trans w*≤q* ∨-upperʳ))) ≤-refl

      -- The two elements over x and y meet to U and join to V.
      median-pair : ((x ∧ V) ∨ U) ∧ ((y ∧ V) ∨ U) ≈ U × ((x ∧ V) ∨ U) ∨ ((y ∧ V) ∨ U) ≈ V
      median-pair = ≤-antisym p∧q≤U (∧-greatest ∨-upperʳ ∨-upperʳ)
                  , ≤-antisym (∨-least p≤V (∨-least ∧-lowerʳ U≤V)) V≤p∨q
        where
        p≤V : p ≤ V
        p≤V = ∨-least ∧-lowerʳ U≤V
```

#### From a failure of distributivity to a diamond

In a modular lattice, the median identity at a triple gives the distributive
law there, by the argument of the introduction
(`median→distributive`{.AgdaFunction}).  So a failure of distributivity at
`x`, `y`, `z` is a failure of `u ≈ v` there, and the diamond is
`u, x', y', z', v` (`failure→Diamond`{.AgdaFunction}): the pair lemma at
`x, y, z` gives the meet and join of `x'` and `y'`, at `y, z, x` those of `y'`
and `z'`, and at `z, x, y` those of `z'` and `x'`.

```agda
    median→distributive : ∀ x y z → u x y z ≈ v x y z → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
    median→distributive x y z u≈v = begin
      x ∧ (y ∨ z)        ≈⟨ ≤-antisym (∧-greatest ∧-lowerˡ (V-greatest (≤-trans ∧-lowerˡ ∨-upperˡ) ∧-lowerʳ
                                                                      (≤-trans ∧-lowerˡ ∨-upperʳ)))
                                     (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ V≤yz)) ⟩
      x ∧ v x y z        ≈˘⟨ ∧-cong refl u≈v ⟩
      x ∧ u x y z        ≈⟨ ≤-antisym x∧U≤s (∧-greatest s≤x (∨-least xy≤U (≤-trans x∧z≤z∧x zx≤U))) ⟩
      (x ∧ y) ∨ (x ∧ z)  ∎
      where
      uJ : IsJoin₃ (u x y z) (x ∧ y) (y ∧ z) (z ∧ x)
      uJ = u-isJoin₃ x y z

      xy≤U : x ∧ y ≤ u x y z
      xy≤U = proj₁ (proj₁ uJ)

      zx≤U : z ∧ x ≤ u x y z
      zx≤U = proj₂ (proj₂ (proj₁ uJ))

      V≤yz : v x y z ≤ y ∨ z
      V≤yz = proj₁ (proj₂ (proj₁ (v-isMeet₃ x y z)))

      V-greatest : ∀ {e} → e ≤ x ∨ y → e ≤ y ∨ z → e ≤ z ∨ x → e ≤ v x y z
      V-greatest = proj₂ (v-isMeet₃ x y z)

      s : 𝕌[ proj₁ 𝑳 ]
      s = (x ∧ y) ∨ (x ∧ z)

      x∧z≤z∧x : x ∧ z ≤ z ∧ x
      x∧z≤z∧x = ∧-greatest ∧-lowerʳ ∧-lowerˡ

      s≤x : s ≤ x
      s≤x = ∨-least ∧-lowerˡ ∧-lowerˡ

      x∧U≤s : x ∧ u x y z ≤ s
      x∧U≤s = ≤-trans (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ U≤s∨yz))
                      (≤-respˡ-≈ (sym (trans ∧-comm-law (sym (mod s≤x))))
                                 (∨-least ≤-refl (≤-trans (∧-greatest ∧-lowerʳ (≤-trans ∧-lowerˡ ∧-lowerˡ))
                                                          ∨-upperˡ)))
        where
        U≤s∨yz : u x y z ≤ s ∨ (y ∧ z)
        U≤s∨yz = proj₂ uJ (≤-trans ∨-upperˡ ∨-upperˡ) ∨-upperʳ
                          (≤-trans (∧-greatest ∧-lowerʳ ∧-lowerˡ) (≤-trans ∨-upperʳ ∨-upperˡ))

    module _ (x y z : 𝕌[ proj₁ 𝑳 ]) (fails : ¬ (u x y z ≈ v x y z)) where
      private
        U V : 𝕌[ proj₁ 𝑳 ]
        U = u x y z
        V = v x y z

        uJ : IsJoin₃ U (x ∧ y) (y ∧ z) (z ∧ x)
        uJ = u-isJoin₃ x y z

        vM : IsMeet₃ V (x ∨ y) (y ∨ z) (z ∨ x)
        vM = v-isMeet₃ x y z

        -- s and t meet to U and join to V.
        Pair : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ 𝑳 ] → Type ρ
        Pair s t = s ∧ t ≈ U × s ∨ t ≈ V

        xy : Pair ((x ∧ V) ∨ U) ((y ∧ V) ∨ U)
        xy = median-pair uJ vM

        yz : Pair ((y ∧ V) ∨ U) ((z ∧ V) ∨ U)
        yz = median-pair (IsJoin₃-rotate uJ) (IsMeet₃-rotate vM)

        zx : Pair ((z ∧ V) ∨ U) ((x ∧ V) ∨ U)
        zx = median-pair (IsJoin₃-rotate (IsJoin₃-rotate uJ)) (IsMeet₃-rotate (IsMeet₃-rotate vM))

      failure→Diamond : Diamond
      failure→Diamond = record
        { ⊥      = U
        ; a      = (x ∧ V) ∨ U
        ; b      = (y ∧ V) ∨ U
        ; c      = (z ∧ V) ∨ U
        ; ⊤      = V
        ; a∧b≈⊥  = proj₁ xy
        ; b∧c≈⊥  = proj₁ yz
        ; a∧c≈⊥  = trans ∧-comm-law (proj₁ zx)
        ; a∨b≈⊤  = proj₂ xy
        ; b∨c≈⊤  = proj₂ yz
        ; a∨c≈⊤  = trans ∨-comm-law (proj₂ zx)
        ; ⊥≉⊤    = fails
        }
```

#### Birkhoff's theorem

The construction composes the two steps, and the converses follow from it as
Dedekind's do.  For the M₃-N₅ theorem, a distributive lattice is modular and
so has no pentagon, and has no diamond; conversely, without a pentagon a
lattice with decidable equality is modular, and then without a diamond it is
distributive.  A finite lattice is decided in two steps: modular or a
pentagon, then distributive or a diamond.

```agda
  -- Birkhoff's construction: in a modular lattice, a failure of distributivity yields a diamond.
  birkhoff : IsModular 𝑳 → DistributiveFailure 𝑳 → Embeds M₃ 𝑳
  birkhoff m (x , y , z , fails) =
    Diamond→Embeds (failure→Diamond m x y z λ u≈v → fails (median→distributive m x y z u≈v))

  -- Without a diamond, no instance of the distributive law fails in a modular lattice.
  ¬Embeds-M₃→¬¬distributive : IsModular 𝑳 → ¬ Embeds M₃ 𝑳
    → ∀ x y z → ¬ ¬ (x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z))
  ¬Embeds-M₃→¬¬distributive m none x y z fails = none (birkhoff m (x , y , z , fails))

  -- With decidable equality, a modular lattice without a diamond is distributive.
  ¬Embeds-M₃→IsDistributive : (∀ x y → Dec (x ≈ y)) → IsModular 𝑳 → ¬ Embeds M₃ 𝑳
    → IsDistributive 𝑳
  ¬Embeds-M₃→IsDistributive _≟_ m none x y z = decided ((x ∧ (y ∨ z)) ≟ ((x ∧ y) ∨ (x ∧ z)))
    where
    decided : Dec (x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)) → x ∧ (y ∨ z) ≈ (x ∧ y) ∨ (x ∧ z)
    decided (yes e)     = e
    decided (no fails)  = ⊥-elim (¬Embeds-M₃→¬¬distributive m none x y z fails)

  -- The M₃-N₅ theorem, for a lattice with decidable equality.
  M₃-N₅-theorem : (∀ x y → Dec (x ≈ y)) → IsDistributive 𝑳 ⇔ (¬ Embeds N₅ 𝑳 × ¬ Embeds M₃ 𝑳)
  M₃-N₅-theorem _≟_ = mk⇔
    (λ d → IsModular→¬Embeds-N₅ 𝑳 (IsDistributive→IsModular 𝑳 d) , IsDistributive→¬Embeds-M₃ d)
    (λ (noN₅ , noM₃) → ¬Embeds-M₃→IsDistributive _≟_ (¬Embeds-N₅→IsModular 𝑳 _≟_ noN₅) noM₃)

  -- A finite lattice is distributive, or has a pentagon, or has a diamond, and which is decided.
  distributive-or-N₅-or-M₃ : FiniteAlgebra (proj₁ 𝑳) → IsDistributive 𝑳 ⊎ (Embeds N₅ 𝑳 ⊎ Embeds M₃ 𝑳)
  distributive-or-N₅-or-M₃ 𝑭 = modular-or-not (modular-or-N₅ 𝑳 𝑭)
    where
    distributive-or-not : IsModular 𝑳 → Dec (IsDistributive 𝑳)
      → IsDistributive 𝑳 ⊎ (Embeds N₅ 𝑳 ⊎ Embeds M₃ 𝑳)
    distributive-or-not _ (yes d)   = inj₁ d
    distributive-or-not m (no ¬d)   = inj₂ (inj₂ (birkhoff m (distributiveFailure 𝑳 𝑭 ¬d)))

    modular-or-not : IsModular 𝑳 ⊎ Embeds N₅ 𝑳 → IsDistributive 𝑳 ⊎ (Embeds N₅ 𝑳 ⊎ Embeds M₃ 𝑳)
    modular-or-not (inj₁ m)    = distributive-or-not m (isDistributive? 𝑳 𝑭)
    modular-or-not (inj₂ emb)  = inj₂ (inj₁ emb)
```
