---
layout: default
file: "src/Lattices/Modular/Dedekind.lagda.md"
title: "Lattices.Modular.Dedekind module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Dedekind's criterion: a lattice is modular iff it has no pentagon

This is the [Lattices.Modular.Dedekind][] module of the [agda-lattices][] library.

Dedekind's theorem ([Dedekind (1900)][]; [Davey and Priestley (2002)][],
Theorem 4.10) says that a lattice is modular if and only if it has no
sublattice isomorphic to the pentagon `N₅` of [Lattices.Examples.N5][].  One
direction is the invariance of the modular law under sublattices,
`IsModular-S-invar`{.AgdaFunction} of [Lattices.Modular][], together with the
failure of the law in `N₅`.  The other direction is a construction, and it is
the content of the theorem: a failure of the modular law at `x ≤ z`, `y` names
five elements that form a pentagon.

Read constructively, the theorem has the following parts:

+  **The construction**.  From a witnessed failure,
   `ModularFailure 𝑳`{.AgdaFunction}, an embedding of `N₅` into
   `𝑳`{.AgdaBound} (`dedekind`{.AgdaFunction}).  It assumes nothing about
   `𝑳`{.AgdaBound}: no finiteness, no decidable equality.
+  **The easy direction**.  A modular lattice has no pentagon
   (`IsModular→¬Embeds-N₅`{.AgdaFunction}), for any lattice.
+  **The converse**.  A lattice with no pentagon satisfies every instance of
   the modular law up to double negation
   (`¬Embeds-N₅→¬¬modular`{.AgdaFunction}), for any lattice; and it is modular
   outright when its equality is decidable
   (`¬Embeds-N₅→IsModular`{.AgdaFunction}), since then each instance either
   holds or is a failure.  A finite lattice is decided one way or the other,
   with the pentagon in hand when it is not modular
   (`modular-or-N₅`{.AgdaFunction}).

The construction goes through a configuration that does not mention the
failure: a `Pentagon`{.AgdaRecord} is five elements `⊥, a, b, c, ⊤` of
`𝑳`{.AgdaBound} with `a ≤ c`, `b ∧ a ≈ b ∧ c ≈ ⊥`, `b ∨ a ≈ b ∨ c ≈ ⊤` and
`a ≉ c`, named after the elements of `N₅` they are the images of.
`Pentagon→Embeds`{.AgdaFunction} shows that every such configuration is an
embedding, and `failure→Pentagon`{.AgdaFunction} builds one from a failure.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Modular.Dedekind where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.Product                           using ( _,_ ; proj₁ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; _⊔_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ) renaming ( refl to ≡-refl )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; from-no )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )

-- Imports from this library ----------------------------------------------------
open import Lattices.Examples.N5  using ( N₅ ; N₅-laws ; N₅-finite )
                                  renaming ( _∧_ to _∧⁵_ ; _∨_ to _∨⁵_ )
open import Lattices.Modular      using ( IsModular ; ModularFailure
                                        ; IsModular-S-invar ; isModular? ; modularFailure )
open import Lattices.Nation       using ( Embeds )
open import Lattices.Table        using ( tableHom )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ : Level
```
-->

#### The pentagon fails the modular law

`N₅` is not modular, by the decision of [Lattices.Modular][], and the failure
is the one its picture shows: `a ≤ c`, yet `a ∨ (b ∧ c) = a ∨ ⊥ = a` and
`(a ∨ b) ∧ c = ⊤ ∧ c = c` (`N₅-modular-failure`{.AgdaFunction}, by
evaluation).

```agda
N₅-not-modular : ¬ IsModular N₅
N₅-not-modular = from-no (isModular? N₅ N₅-finite)

-- a ≤ c, and a ∨ (b ∧ c) = a differs from (a ∨ b) ∧ c = c.
N₅-modular-failure : ModularFailure N₅
N₅-modular-failure = 1F , 2F , 3F , ≡-refl , λ ()
```

#### The easy direction

```agda
module _ (𝑳 : Lattice α ρ) where

  IsModular→¬Embeds-N₅ : IsModular 𝑳 → ¬ Embeds N₅ 𝑳
  IsModular→¬Embeds-N₅ m emb = N₅-not-modular (IsModular-S-invar N₅ 𝑳 emb m)
```

#### Pentagons

A `Pentagon`{.AgdaRecord} in `𝑳`{.AgdaBound} is the configuration of the
introduction.  Its six relations are those of `N₅` that the embedding needs
beyond the lattice laws, and the rest follow.  The bottom lies below every
element: `⊥ ≈ b ∧ a` lies below `a` and `b`, and `⊥ ≈ b ∧ c` below `c`.
Dually every element lies below the top.  These eight inequalities, with
`a ≤ c`, are all the comparabilities in `N₅`.

```agda
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law
                                   ; ∧-idem-law ; ∨-idem-law ; ∧-assoc-law ; absorbˡ-law )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-trans ; ≤-antisym ; ≤-respˡ-≈ ; ≤-respʳ-≈ ; ≤-via-∨
                                   ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest ; ∨-upperˡ ; ∨-upperʳ
                                   ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )

  -- Five elements of 𝑳 in the configuration of N₅: a ≤ c, and b a complement of both.
  record Pentagon : Type (α ⊔ ρ) where
    field
      ⊥ a b c ⊤  : 𝕌[ proj₁ 𝑳 ]
      a≤c        : a ≤ c
      b∧a≈⊥      : b ∧ a ≈ ⊥
      b∧c≈⊥      : b ∧ c ≈ ⊥
      b∨a≈⊤      : b ∨ a ≈ ⊤
      b∨c≈⊤      : b ∨ c ≈ ⊤
      a≉c        : ¬ (a ≈ c)

  module _ (P : Pentagon) where
    open Pentagon P

    private
      ⊥≤a : ⊥ ≤ a
      ⊥≤a = ≤-respˡ-≈ b∧a≈⊥ ∧-lowerʳ

      ⊥≤b : ⊥ ≤ b
      ⊥≤b = ≤-respˡ-≈ b∧a≈⊥ ∧-lowerˡ

      ⊥≤c : ⊥ ≤ c
      ⊥≤c = ≤-respˡ-≈ b∧c≈⊥ ∧-lowerʳ

      a≤⊤ : a ≤ ⊤
      a≤⊤ = ≤-respʳ-≈ b∨a≈⊤ ∨-upperʳ

      b≤⊤ : b ≤ ⊤
      b≤⊤ = ≤-respʳ-≈ b∨a≈⊤ ∨-upperˡ

      c≤⊤ : c ≤ ⊤
      c≤⊤ = ≤-respʳ-≈ b∨c≈⊤ ∨-upperʳ

      ⊥≤⊤ : ⊥ ≤ ⊤
      ⊥≤⊤ = ≤-trans ⊥≤a a≤⊤
```

The map `j`{.AgdaFunction} sends the elements of `N₅`, numbered as in
[Lattices.Examples.N5][] (`⊥, a, b, c, ⊤` as `0` to `4`), to the five elements
of the configuration.  It commutes with both operations on all 25 pairs.  On a
comparable pair, the meet is the smaller element and the join the larger, in
`N₅` and in `𝑳`{.AgdaBound} alike (`meet-≤`{.AgdaFunction},
`meet-≥`{.AgdaFunction}, `join-≤`{.AgdaFunction}, `join-≥`{.AgdaFunction}); the
incomparable pairs are `a, b` and `b, c`, whose meets and joins are the four
equations of the configuration, up to commutativity.

```agda
      meet-≤ : ∀ {x y} → x ≤ y → x ≈ x ∧ y
      meet-≤ = sym

      meet-≥ : ∀ {x y} → y ≤ x → y ≈ x ∧ y
      meet-≥ y≤x = trans (sym y≤x) ∧-comm-law

      join-≤ : ∀ {x y} → x ≤ y → y ≈ x ∨ y
      join-≤ x≤y = sym (≤-via-∨ x≤y)

      join-≥ : ∀ {x y} → y ≤ x → x ≈ x ∨ y
      join-≥ y≤x = trans (sym (≤-via-∨ y≤x)) ∨-comm-law

      -- The images of ⊥, a, b, c, ⊤.
      j : Fin 5 → 𝕌[ proj₁ 𝑳 ]
      j 0F = ⊥
      j 1F = a
      j 2F = b
      j 3F = c
      j 4F = ⊤

      j-∧ : ∀ x y → j (x ∧⁵ y) ≈ j x ∧ j y
      j-∧ 0F 0F = sym ∧-idem-law
      j-∧ 0F 1F = meet-≤ ⊥≤a
      j-∧ 0F 2F = meet-≤ ⊥≤b
      j-∧ 0F 3F = meet-≤ ⊥≤c
      j-∧ 0F 4F = meet-≤ ⊥≤⊤
      j-∧ 1F 0F = meet-≥ ⊥≤a
      j-∧ 1F 1F = sym ∧-idem-law
      j-∧ 1F 2F = sym (trans ∧-comm-law b∧a≈⊥)
      j-∧ 1F 3F = meet-≤ a≤c
      j-∧ 1F 4F = meet-≤ a≤⊤
      j-∧ 2F 0F = meet-≥ ⊥≤b
      j-∧ 2F 1F = sym b∧a≈⊥
      j-∧ 2F 2F = sym ∧-idem-law
      j-∧ 2F 3F = sym b∧c≈⊥
      j-∧ 2F 4F = meet-≤ b≤⊤
      j-∧ 3F 0F = meet-≥ ⊥≤c
      j-∧ 3F 1F = meet-≥ a≤c
      j-∧ 3F 2F = sym (trans ∧-comm-law b∧c≈⊥)
      j-∧ 3F 3F = sym ∧-idem-law
      j-∧ 3F 4F = meet-≤ c≤⊤
      j-∧ 4F 0F = meet-≥ ⊥≤⊤
      j-∧ 4F 1F = meet-≥ a≤⊤
      j-∧ 4F 2F = meet-≥ b≤⊤
      j-∧ 4F 3F = meet-≥ c≤⊤
      j-∧ 4F 4F = sym ∧-idem-law

      j-∨ : ∀ x y → j (x ∨⁵ y) ≈ j x ∨ j y
      j-∨ 0F 0F = sym ∨-idem-law
      j-∨ 0F 1F = join-≤ ⊥≤a
      j-∨ 0F 2F = join-≤ ⊥≤b
      j-∨ 0F 3F = join-≤ ⊥≤c
      j-∨ 0F 4F = join-≤ ⊥≤⊤
      j-∨ 1F 0F = join-≥ ⊥≤a
      j-∨ 1F 1F = sym ∨-idem-law
      j-∨ 1F 2F = sym (trans ∨-comm-law b∨a≈⊤)
      j-∨ 1F 3F = join-≤ a≤c
      j-∨ 1F 4F = join-≤ a≤⊤
      j-∨ 2F 0F = join-≥ ⊥≤b
      j-∨ 2F 1F = sym b∨a≈⊤
      j-∨ 2F 2F = sym ∨-idem-law
      j-∨ 2F 3F = sym b∨c≈⊤
      j-∨ 2F 4F = join-≤ b≤⊤
      j-∨ 3F 0F = join-≥ ⊥≤c
      j-∨ 3F 1F = join-≥ a≤c
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
force `a ≈ c`.  Four coincidences do so through the order alone, since `a ≤ c`
and every element lies between `⊥` and `⊤`: `⊥ ≈ c`, `⊥ ≈ ⊤` and `a ≈ ⊤` put
`c` below `a`, and `⊥ ≈ b` gives `⊤ ≈ b ∨ a ≈ ⊥ ∨ a ≈ a`.  If `⊥ ≈ a`, then
`⊤ ≈ b ∨ a ≈ b ∨ ⊥ ≈ b`, so `c ≈ c ∧ ⊤ ≈ c ∧ b ≈ ⊥ ≈ a`.  The other four reduce
to these: `a ≈ b` gives `⊥ ≈ b ∧ a ≈ a`; `b ≈ c` gives `⊥ ≈ b ∧ c ≈ c`;
`b ≈ ⊤` gives `⊥ ≈ b ∧ c ≈ ⊤ ∧ c ≈ c`; and `c ≈ ⊤` gives `b ≤ c`, so
`⊥ ≈ b ∧ c ≈ b`.

```agda
      open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

      -- c ≤ a, with a ≤ c, gives a ≈ c.
      collapse : c ≤ a → a ≈ c
      collapse c≤a = ≤-antisym a≤c c≤a

      ⊥≈c→a≈c : ⊥ ≈ c → a ≈ c
      ⊥≈c→a≈c ⊥≈c = collapse (≤-respˡ-≈ ⊥≈c ⊥≤a)

      ⊥≈⊤→a≈c : ⊥ ≈ ⊤ → a ≈ c
      ⊥≈⊤→a≈c ⊥≈⊤ = collapse (≤-trans c≤⊤ (≤-respˡ-≈ ⊥≈⊤ ⊥≤a))

      a≈⊤→a≈c : a ≈ ⊤ → a ≈ c
      a≈⊤→a≈c a≈⊤ = collapse (≤-respʳ-≈ (sym a≈⊤) c≤⊤)

      ⊥≈b→a≈c : ⊥ ≈ b → a ≈ c
      ⊥≈b→a≈c ⊥≈b = collapse (≤-respʳ-≈ ⊤≈a c≤⊤)
        where
        ⊤≈a : ⊤ ≈ a
        ⊤≈a = begin
          ⊤      ≈˘⟨ b∨a≈⊤ ⟩
          b ∨ a  ≈˘⟨ ∨-cong ⊥≈b refl ⟩
          ⊥ ∨ a  ≈⟨ ≤-via-∨ ⊥≤a ⟩
          a      ∎

      ⊥≈a→a≈c : ⊥ ≈ a → a ≈ c
      ⊥≈a→a≈c ⊥≈a = sym (begin
        c      ≈˘⟨ c≤⊤ ⟩
        c ∧ ⊤  ≈⟨ ∧-cong refl ⊤≈b ⟩
        c ∧ b  ≈⟨ ∧-comm-law ⟩
        b ∧ c  ≈⟨ b∧c≈⊥ ⟩
        ⊥      ≈⟨ ⊥≈a ⟩
        a      ∎)
        where
        ⊤≈b : ⊤ ≈ b
        ⊤≈b = begin
          ⊤      ≈˘⟨ b∨a≈⊤ ⟩
          b ∨ a  ≈˘⟨ ∨-cong refl ⊥≈a ⟩
          b ∨ ⊥  ≈⟨ ∨-comm-law ⟩
          ⊥ ∨ b  ≈⟨ ≤-via-∨ ⊥≤b ⟩
          b      ∎

      a≈b→a≈c : a ≈ b → a ≈ c
      a≈b→a≈c a≈b = ⊥≈a→a≈c (trans (sym b∧a≈⊥) (trans (∧-cong (sym a≈b) refl) ∧-idem-law))

      b≈c→a≈c : b ≈ c → a ≈ c
      b≈c→a≈c b≈c = ⊥≈c→a≈c (trans (sym b∧c≈⊥) (trans (∧-cong b≈c refl) ∧-idem-law))

      b≈⊤→a≈c : b ≈ ⊤ → a ≈ c
      b≈⊤→a≈c b≈⊤ = ⊥≈c→a≈c (trans (sym b∧c≈⊥) (trans (∧-cong b≈⊤ refl)
                                                       (trans ∧-comm-law c≤⊤)))

      c≈⊤→a≈c : c ≈ ⊤ → a ≈ c
      c≈⊤→a≈c c≈⊤ = ⊥≈b→a≈c (trans (sym b∧c≈⊥) b≤c)
        where
        b≤c : b ≤ c
        b≤c = ≤-respʳ-≈ (sym c≈⊤) b≤⊤

      j-injective : ∀ x y → j x ≈ j y → x ≡ y
      j-injective 0F 0F _ = ≡-refl
      j-injective 0F 1F e = ⊥-elim (a≉c (⊥≈a→a≈c e))
      j-injective 0F 2F e = ⊥-elim (a≉c (⊥≈b→a≈c e))
      j-injective 0F 3F e = ⊥-elim (a≉c (⊥≈c→a≈c e))
      j-injective 0F 4F e = ⊥-elim (a≉c (⊥≈⊤→a≈c e))
      j-injective 1F 0F e = ⊥-elim (a≉c (⊥≈a→a≈c (sym e)))
      j-injective 1F 1F _ = ≡-refl
      j-injective 1F 2F e = ⊥-elim (a≉c (a≈b→a≈c e))
      j-injective 1F 3F e = ⊥-elim (a≉c e)
      j-injective 1F 4F e = ⊥-elim (a≉c (a≈⊤→a≈c e))
      j-injective 2F 0F e = ⊥-elim (a≉c (⊥≈b→a≈c (sym e)))
      j-injective 2F 1F e = ⊥-elim (a≉c (a≈b→a≈c (sym e)))
      j-injective 2F 2F _ = ≡-refl
      j-injective 2F 3F e = ⊥-elim (a≉c (b≈c→a≈c e))
      j-injective 2F 4F e = ⊥-elim (a≉c (b≈⊤→a≈c e))
      j-injective 3F 0F e = ⊥-elim (a≉c (⊥≈c→a≈c (sym e)))
      j-injective 3F 1F e = ⊥-elim (a≉c (sym e))
      j-injective 3F 2F e = ⊥-elim (a≉c (b≈c→a≈c (sym e)))
      j-injective 3F 3F _ = ≡-refl
      j-injective 3F 4F e = ⊥-elim (a≉c (c≈⊤→a≈c e))
      j-injective 4F 0F e = ⊥-elim (a≉c (⊥≈⊤→a≈c (sym e)))
      j-injective 4F 1F e = ⊥-elim (a≉c (a≈⊤→a≈c (sym e)))
      j-injective 4F 2F e = ⊥-elim (a≉c (b≈⊤→a≈c (sym e)))
      j-injective 4F 3F e = ⊥-elim (a≉c (c≈⊤→a≈c (sym e)))
      j-injective 4F 4F _ = ≡-refl

    -- A pentagon in 𝑳 is an embedding of N₅.
    Pentagon→Embeds : Embeds N₅ 𝑳
    Pentagon→Embeds = tableHom N₅-laws 𝑳 j j-∧ j-∨ , λ {x} {y} → j-injective x y
```

#### From a failure of the modular law to a pentagon

Let `x ≤ z`, `y` be a failure of the modular law, and write
`a = x ∨ (y ∧ z)` and `c = (x ∨ y) ∧ z`.  The pentagon is
`⊥ = y ∧ z`, `a`, `b = y`, `c`, `⊤ = x ∨ y`
([Davey and Priestley (2002)][], proof of Theorem 4.10), and its relations
hold as follows:

+  `a ≤ c` is the modular inequality: `x` and `y ∧ z` both lie below `x ∨ y`
   and below `z`.  It is the only place where `x ≤ z` is used.
+  `y ∧ c ≈ y ∧ z`, since `y ∧ (x ∨ y) ≈ y` by absorption; and `y ∧ a` lies
   between `y ∧ z` (which is below `y` and below `a`) and `y ∧ c` (since
   `a ≤ c`), so it equals `y ∧ z` too.
+  `y ∨ a ≈ x ∨ y`, since `y ∨ x ∨ (y ∧ z)` absorbs `y ∧ z`; and `y ∨ c` lies
   between `y ∨ a` and `x ∨ y` (both `y` and `c` are below `x ∨ y`), so it
   equals `x ∨ y` too.
+  `a ≉ c` is the failure.

```agda
  module _ (x y z : 𝕌[ proj₁ 𝑳 ]) (x≤z : x ≤ z) (fails : ¬ (x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z)) where
    private
      a c : 𝕌[ proj₁ 𝑳 ]
      a = x ∨ (y ∧ z)
      c = (x ∨ y) ∧ z

      y∧z≤x∨y : y ∧ z ≤ x ∨ y
      y∧z≤x∨y = ≤-trans ∧-lowerˡ ∨-upperʳ

      a≤c : a ≤ c
      a≤c = ∨-least (∧-greatest ∨-upperˡ x≤z) (∧-greatest y∧z≤x∨y ∧-lowerʳ)

      y∧c≈y∧z : y ∧ c ≈ y ∧ z
      y∧c≈y∧z = trans (sym ∧-assoc-law) (∧-cong (trans (∧-cong refl ∨-comm-law) absorbˡ-law) refl)

      y∧a≈y∧z : y ∧ a ≈ y ∧ z
      y∧a≈y∧z = ≤-antisym (≤-respʳ-≈ y∧c≈y∧z (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ a≤c)))
                          (∧-greatest ∧-lowerˡ ∨-upperʳ)

      y∨a≈x∨y : y ∨ a ≈ x ∨ y
      y∨a≈x∨y = ≤-antisym (∨-least ∨-upperʳ (∨-least ∨-upperˡ y∧z≤x∨y))
                          (∨-least (≤-trans ∨-upperˡ ∨-upperʳ) ∨-upperˡ)

      y∨c≈x∨y : y ∨ c ≈ x ∨ y
      y∨c≈x∨y = ≤-antisym (∨-least ∨-upperʳ ∧-lowerˡ)
                          (≤-respˡ-≈ y∨a≈x∨y (∨-least ∨-upperˡ (≤-trans a≤c ∨-upperʳ)))

    failure→Pentagon : Pentagon
    failure→Pentagon = record
      { ⊥      = y ∧ z
      ; a      = a
      ; b      = y
      ; c      = c
      ; ⊤      = x ∨ y
      ; a≤c    = a≤c
      ; b∧a≈⊥  = y∧a≈y∧z
      ; b∧c≈⊥  = y∧c≈y∧z
      ; b∨a≈⊤  = y∨a≈x∨y
      ; b∨c≈⊤  = y∨c≈x∨y
      ; a≉c    = fails
      }
```

#### Dedekind's theorem

The construction composes the two steps.  The converse directions follow from
it: if `𝑳`{.AgdaBound} has no pentagon, an instance `x ≤ z`, `y` of the modular
law cannot fail, so its negation is refuted; with decidable equality the
instance is decided, and the negative case is refuted the same way.  A finite
lattice is decided by `isModular?`{.AgdaFunction}, and a negative verdict is
turned into a failure by `modularFailure`{.AgdaFunction} of
[Lattices.Modular][], and then into a pentagon.

```agda
  -- Dedekind's construction: a failure of the modular law yields a pentagon.
  dedekind : ModularFailure 𝑳 → Embeds N₅ 𝑳
  dedekind (x , y , z , x≤z , fails) = Pentagon→Embeds (failure→Pentagon x y z x≤z fails)

  -- Without a pentagon, no instance of the modular law fails.
  ¬Embeds-N₅→¬¬modular : ¬ Embeds N₅ 𝑳 → ∀ x y z → x ≤ z → ¬ ¬ (x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z)
  ¬Embeds-N₅→¬¬modular none x y z x≤z fails = none (dedekind (x , y , z , x≤z , fails))

  -- With decidable equality, a lattice without a pentagon is modular.
  ¬Embeds-N₅→IsModular : (∀ x y → Dec (x ≈ y)) → ¬ Embeds N₅ 𝑳 → IsModular 𝑳
  ¬Embeds-N₅→IsModular _≟_ none x y z x≤z = decided ((x ∨ (y ∧ z)) ≟ ((x ∨ y) ∧ z))
    where
    decided : Dec (x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z) → x ∨ (y ∧ z) ≈ (x ∨ y) ∧ z
    decided (yes e)      = e
    decided (no fails)   = ⊥-elim (¬Embeds-N₅→¬¬modular none x y z x≤z fails)

  -- A finite lattice is modular or has a pentagon, and which is decided.
  modular-or-N₅ : FiniteAlgebra (proj₁ 𝑳) → IsModular 𝑳 ⊎ Embeds N₅ 𝑳
  modular-or-N₅ 𝑭 = decided (isModular? 𝑳 𝑭)
    where
    decided : Dec (IsModular 𝑳) → IsModular 𝑳 ⊎ Embeds N₅ 𝑳
    decided (yes m)   = inj₁ m
    decided (no ¬m)   = inj₂ (dedekind (modularFailure 𝑳 𝑭 ¬m))
```
