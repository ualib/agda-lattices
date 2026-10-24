---
layout: default
file: "src/Lattices/Nation/Alternating.lagda.md"
title: "Lattices.Nation.Alternating module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Lemmas 5.52 and 5.53: cycles alternating B₁ and A₂

This is the [Lattices.Nation.Alternating][] module of the [agda-lattices][]
library.

Lemma 5.52 of [Freese, Ježek, and Nation (1995)][] (pp. 123 to 125) takes a
subsequence `r₀ A₂ r₁ B₁ r₂ A₂ r₃ B₁ r₄ A₂ r₅` of a minimal C-cycle in an
S-lattice and concludes `r₀ ≤ r₂ ∨ r₄` and `r₄ ≰ r₀ ∨ r₂`.  Lemma 5.49 gives
`r₀ ≤ r₁ ∨ r₂` and `r₂ ≤ r₃ ∨ r₄`; `r₄₋₋ ≰ κ(r₂)`, since otherwise `r₂ B r₄₋`
and the cycle shortens through `r₄₋ = r₅` or `r₄₋ A r₅`
(`Sub-shortcut`{.AgdaFunction}); then `r₂ ≤ r₂₋ ∨ r₄₋₋`, and (SD∨) refutes
`r₄₋₋ ≤ r₀ ∨ r₂`, which is the second conclusion.  For the first, supposing
`r₀ ≰ r₂ ∨ r₄`, the elements `a = r₂`, `a₀ = (r₀ ∨ r₂) ∧ (r₂ ∨ r₄)`,
`a₁ = a₀₋`, `b = r₃₋ ∨ r₄₋₋` and `b₀ = r₃₋ ∨ r₄₋` form the configuration of
Lemma 5.38, `a₀` being join irreducible as a proper meet; three of the
conditions share one argument (`absorb`{.AgdaFunction}): `r₄ ≤ z ∨ w` with
`r₃ ≤ z ≤ r₃ ∨ r₄`, `w ≤ r₄₋` and `r₄ ≰ z` makes `r₃ ∨ r₄ = r₃ ∨ w ∨ (r₄ ∧ z)`
by (SD∨), which lies below `κ(r₄)`.

The module checks in 1.6 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Alternating where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; z≤n ; s≤s )
                                                   renaming ( _≤_ to _≤ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n≤1+n ; +-suc ; +-comm ; +-identityʳ ; +-mono-≤ ; +-monoʳ-≤ )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-reflexive to ≤ℕ-reflexive ; ≤-trans to ≤ℕ-trans )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType      as BTypeModule
import Lattices.Nation.Extension  as ExtensionModule
open import Lattices.Nation.Configurations  using ( module Configurations )
open import Lattices.Nation.Cycle           using ( module Cycles ; _∷_ ; [] )
open import Agda.Primitive                  using () renaming ( Set to Type )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### Lemma 5.52

```agda
module Alternating {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                   (laws : LatticeTableLaws _∧_ _∨_)
                   (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                   (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W )
  open Configurations laws w using ( Config₃₈ ; no-config₃₈ ; meet-irr )
  open ExtensionModule.Extension laws sd w using ( lemma-5-49 )

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 hiding ( k )

    -- r₀ A₂ r₁ B₁ r₂ A₂ r₃ B₁ r₄ A₂ r₅, a subsequence of the cycle.
    module Lemma552 {x : ℕ → Fin (suc n)} (sub : Sub 5 x)
                    (A₀₁ : x 0 A₂ x 1) (B₁₂ : x 1 B₁ x 2) (A₂₃ : x 2 A₂ x 3) (B₃₄ : x 3 B₁ x 4) (A₄₅ : x 4 A₂ x 5) where

      r₀ r₁ r₂ r₃ r₄ r₅ : Fin (suc n)
      r₀ = x 0
      r₁ = x 1
      r₂ = x 2
      r₃ = x 3
      r₄ = x 4
      r₅ = x 5

      2≤5 : 2 ≤ℕ 5
      2≤5 = s≤s (s≤s z≤n)

      3≤5 : 3 ≤ℕ 5
      3≤5 = s≤s (s≤s (s≤s z≤n))

      4≤5 : 4 ≤ℕ 5
      4≤5 = s≤s (s≤s (s≤s (s≤s z≤n)))

      5≤5 : 5 ≤ℕ 5
      5≤5 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

      i₂ : HasOneLowerCover r₂
      i₂ = Sub-irr sub 2≤5

      i₃ : HasOneLowerCover r₃
      i₃ = Sub-irr sub 3≤5

      i₄ : HasOneLowerCover r₄
      i₄ = Sub-irr sub 4≤5

      i₅ : HasOneLowerCover r₅
      i₅ = Sub-irr sub 5≤5

      i₄₋ : HasOneLowerCover (r₄ ₋)
      i₄₋ = Sub-₋irr 𝒞 sub 4≤5

      -- Lemma 5.49 twice.
      r₀≤r₁∨r₂ : r₀ ≤ r₁ ∨ r₂
      r₀≤r₁∨r₂ = lemma-5-49 A₀₁ B₁₂

      r₂≤r₃∨r₄ : r₂ ≤ r₃ ∨ r₄
      r₂≤r₃∨r₄ = lemma-5-49 A₂₃ B₃₄

      -- Consequences of the A's and B's.
      r₁<r₀ : r₁ < r₀
      r₁<r₀ = A→< (proj₁ A₀₁)

      r₃<r₂ : r₃ < r₂
      r₃<r₂ = A→< (proj₁ A₂₃)

      r₅<r₄ : r₅ < r₄
      r₅<r₄ = A→< (proj₁ A₄₅)

      r₃≤r₂₋ : r₃ ≤ r₂ ₋
      r₃≤r₂₋ = <→≤₋ r₃<r₂

      r₃₋≤r₂₋ : r₃ ₋ ≤ r₂ ₋
      r₃₋≤r₂₋ = ≤-trans (₋≤ r₃) r₃≤r₂₋

      r₁≤κr₂ : r₁ ≤ κ r₂
      r₁≤κr₂ = B→≤κ (proj₁ B₁₂)

      r₃≤κr₄ : r₃ ≤ κ r₄
      r₃≤κr₄ = B→≤κ (proj₁ B₃₄)

      r₃≰r₄ : ¬ r₃ ≤ r₄
      r₃≰r₄ = B→≰ (proj₁ B₃₄)

      r₄₋≤κr₃ : r₄ ₋ ≤ κ r₃
      r₄₋≤κr₃ = B→₋≤κ (proj₁ B₃₄)

      r₃≤r₃₋∨r₄ : r₃ ≤ (r₃ ₋) ∨ r₄
      r₃≤r₃₋∨r₄ = proj₁ (proj₂ (proj₂ (proj₂ (proj₁ B₃₄))))

      r₄≤r₅∨κr₅ : r₄ ≤ r₅ ∨ κ r₅
      r₄≤r₅∨κr₅ = proj₂ (proj₂ (proj₂ (proj₁ A₄₅)))

      -- r₄ ≰ κ(r₂), so r₄₋ ≰ κ(r₂) by the free star principle; and r₂ ≠ r₄₋.
      r₄≰κr₂ : ¬ r₄ ≤ κ r₂
      r₄≰κr₂ h = a≰κ i₂ (≤-trans r₂≤r₃∨r₄ (∨-least (≤-trans r₃≤r₂₋ (₋≤κ r₂)) h))

      r₄₋≰κr₂ : ¬ r₄ ₋ ≤ κ r₂
      r₄₋≰κr₂ h = r₄≰κr₂ (Sub-freeStar′ sub 2≤5 4≤5 (λ ()) (λ ()) (λ { (() , _) }) h)

      r₂≢r₄₋ : r₂ ≢ r₄ ₋
      r₂≢r₄₋ e = r₃≰r₄ (≤-trans (proj₁ r₃<r₂) (≤-trans (≤-reflexive′ e) (₋≤ r₄)))

      -- r₄₋₋ ≰ κ(r₂): otherwise r₂ B r₄₋ by Lemma 2.58, and r₄₋ = r₅ or r₄₋ A r₅ shortens the cycle.
      r₄₋₋≰κr₂ : ¬ (r₄ ₋) ₋ ≤ κ r₂
      r₄₋₋≰κr₂ h = decide (r₄ ₋ ≟ r₅)
        where
        r₂Br₄₋ : r₂ B r₄ ₋
        r₂Br₄₋ = B-from-κ i₂ i₄₋ r₂≢r₄₋ h r₄₋≰κr₂

        decide : Dec (r₄ ₋ ≡ r₅) → ⊥
        decide (yes e) = Sub-freeStar sub 2≤5 5≤5 (λ ()) (λ { (() , _) }) (subst (r₂ B_) e r₂Br₄₋)
        decide (no ne) = Sub-shortcut sub 2≤5 5≤5 5≤5 (inj₂ r₂Br₄₋ ∷ (inj₁ r₄₋Ar₅ ∷ []))
          where
          r₅<r₄₋ : r₅ < r₄ ₋
          r₅<r₄₋ = <→≤₋ r₅<r₄ , λ e → ne (sym e)

          r₄₋Ar₅ : r₄ ₋ A r₅
          r₄₋Ar₅ = i₄₋ , i₅ , r₅<r₄₋ , ≤-trans (₋≤ r₄) r₄≤r₅∨κr₅

      -- Hence r₂ ≤ r₂₋ ∨ r₄₋₋ (Lemma 2.57), and r₄₋₋ ≰ r₃₋.
      r₂≤r₂₋∨r₄₋₋ : r₂ ≤ (r₂ ₋) ∨ ((r₄ ₋) ₋)
      r₂≤r₂₋∨r₄₋₋ = ≰κ→ i₂ r₄₋₋≰κr₂

      r₄₋₋≰r₃₋ : ¬ (r₄ ₋) ₋ ≤ r₃ ₋
      r₄₋₋≰r₃₋ h = a≰κ i₂ (≤-trans r₂≤r₂₋∨r₄₋₋ (∨-least (₋≤κ r₂) (≤-trans h (≤-trans r₃₋≤r₂₋ (₋≤κ r₂)))))

      -- The second conclusion, strongly: r₄₋₋ ≰ r₀ ∨ r₂ = r₁ ∨ r₂, by (SD∨) on r₁ ∨ r₂₋ ∨ r₂ = r₁ ∨ r₂₋ ∨ r₄₋₋.
      r₀∨r₂≡r₁∨r₂ : r₀ ∨ r₂ ≡ r₁ ∨ r₂
      r₀∨r₂≡r₁∨r₂ = ≤-antisym (∨-least r₀≤r₁∨r₂ ∨-upperʳ) (∨-least (≤∨ˡ (proj₁ r₁<r₀)) ∨-upperʳ)

      r₂≰r₄₋₋ : ¬ r₂ ≤ (r₄ ₋) ₋
      r₂≰r₄₋₋ h = r₃≰r₄ (≤-trans (proj₁ r₃<r₂) (≤-trans h (≤-trans (₋≤ (r₄ ₋)) (₋≤ r₄))))

      r₄₋₋≰r₀∨r₂ : ¬ (r₄ ₋) ₋ ≤ r₀ ∨ r₂
      r₄₋₋≰r₀∨r₂ h =
        a≰κ i₂ (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨ (r₁ ∨ (r₂ ₋)) r₂ ((r₄ ₋) ₋) e))
                                          (∨-least (∨-least r₁≤κr₂ (₋≤κ r₂)) (≤-trans r₂∧r₄₋₋≤r₂₋ (₋≤κ r₂)))))
        where
        e : (r₁ ∨ (r₂ ₋)) ∨ r₂ ≡ (r₁ ∨ (r₂ ₋)) ∨ ((r₄ ₋) ₋)
        e = ≤-antisym (∨-least ∨-upperˡ (≤-trans r₂≤r₂₋∨r₄₋₋ (∨-least (≤∨ˡ ∨-upperʳ) ∨-upperʳ)))
                      (∨-least ∨-upperˡ (≤-trans h (≤-trans (≤-reflexive′ r₀∨r₂≡r₁∨r₂) (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ))))

        r₂∧r₄₋₋≤r₂₋ : r₂ ∧ ((r₄ ₋) ₋) ≤ r₂ ₋
        r₂∧r₄₋₋≤r₂₋ = <→≤₋′ ∧-lowerˡ λ e′ → r₂≰r₄₋₋ (subst (_≤ (r₄ ₋) ₋) e′ ∧-lowerʳ)

      part2 : ¬ r₄ ≤ r₀ ∨ r₂
      part2 h = r₄₋₋≰r₀∨r₂ (≤-trans (₋≤ (r₄ ₋)) (≤-trans (₋≤ r₄) h))

      -- The first conclusion, supposing r₀ ≰ r₂ ∨ r₄: the configuration of Lemma 5.38.
      module Part1 (r₀≰ : ¬ r₀ ≤ r₂ ∨ r₄) where
        a a₀ a₁ b b₀ : Fin (suc n)
        a = r₂
        a₀ = (r₀ ∨ r₂) ∧ (r₂ ∨ r₄)
        a₁ = a₀ ₋
        b = (r₃ ₋) ∨ ((r₄ ₋) ₋)
        b₀ = (r₃ ₋) ∨ (r₄ ₋)

        a≤a₀ : a ≤ a₀
        a≤a₀ = ∧-greatest ∨-upperʳ ∨-upperˡ

        r₂≰r₄₋ : ¬ r₂ ≤ r₄ ₋
        r₂≰r₄₋ h = r₃≰r₄ (≤-trans (proj₁ r₃<r₂) (≤-trans h (₋≤ r₄)))

        r₄≰r₂₋ : ¬ r₄ ≤ r₂ ₋
        r₄≰r₂₋ h = r₄₋≰κr₂ (≤-trans (₋≤ r₄) (≤-trans h (₋≤κ r₂)))

        -- r₄ ≤ z ∨ w with r₃ ≤ z ≤ r₃ ∨ r₄, w ≤ r₄₋ and r₄ ≰ z: (SD∨) gives r₃ ∨ r₄ = r₃ ∨ w ∨ (r₄ ∧ z) ≤ κ(r₄).
        absorb : ∀ z w′ → r₃ ≤ z → z ≤ r₃ ∨ r₄ → w′ ≤ r₄ ₋ → ¬ r₄ ≤ z → ¬ r₄ ≤ z ∨ w′
        absorb z w′ r₃≤z z≤ w′≤ r₄≰z h =
          a≰κ i₄ (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨ (r₃ ∨ w′) r₄ z e))
                                            (∨-least (∨-least r₃≤κr₄ (≤-trans w′≤ (₋≤κ r₄))) (≤-trans r₄∧z≤r₄₋ (₋≤κ r₄)))))
          where
          e : (r₃ ∨ w′) ∨ r₄ ≡ (r₃ ∨ w′) ∨ z
          e = ≤-antisym (∨-least ∨-upperˡ (≤-trans h (∨-least ∨-upperʳ (≤∨ˡ ∨-upperʳ))))
                        (∨-least ∨-upperˡ (≤-trans z≤ (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ)))

          r₄∧z≤r₄₋ : r₄ ∧ z ≤ r₄ ₋
          r₄∧z≤r₄₋ = <→≤₋′ ∧-lowerˡ λ e′ → r₄≰z (subst (_≤ z) e′ ∧-lowerʳ)

        -- a ≠ a₀: otherwise (W) on r₂ = (r₀ ∨ r₂) ∧ (r₂ ∨ r₄) ≤ r₂₋ ∨ r₄₋₋ fails in every disjunct.
        a≢a₀ : a ≢ a₀
        a≢a₀ e = cases (W (r₀ ∨ r₂) (r₂ ∨ r₄) (r₂ ₋) ((r₄ ₋) ₋) (≤-trans (≤-reflexive′ (sym e)) r₂≤r₂₋∨r₄₋₋))
          where
          cases : (r₀ ∨ r₂ ≤ (r₂ ₋) ∨ ((r₄ ₋) ₋) ⊎ r₂ ∨ r₄ ≤ (r₂ ₋) ∨ ((r₄ ₋) ₋)) ⊎ (a₀ ≤ r₂ ₋ ⊎ a₀ ≤ (r₄ ₋) ₋) → ⊥
          cases (inj₁ (inj₁ h)) = r₀≰ (≤-trans ∨-upperˡ (≤-trans h (∨-least (≤∨ˡ (₋≤ r₂)) (≤∨ʳ (≤-trans (₋≤ (r₄ ₋)) (₋≤ r₄))))))
          cases (inj₁ (inj₂ h)) = absorb (r₂ ₋) ((r₄ ₋) ₋) r₃≤r₂₋ (≤-trans (₋≤ r₂) r₂≤r₃∨r₄) (₋≤ (r₄ ₋)) r₄≰r₂₋ (≤-trans ∨-upperʳ h)
          cases (inj₂ (inj₁ h)) = proj₂ i₂ (≤-antisym (₋≤ r₂) (≤-trans a≤a₀ h))
          cases (inj₂ (inj₂ h)) = r₂≰r₄₋₋ (≤-trans a≤a₀ h)

        a<a₀ : a < a₀
        a<a₀ = a≤a₀ , a≢a₀

        -- a₀ is a proper meet, hence join irreducible, and a₁ = a₀₋ is its lower cover above a.
        ia₀ : HasOneLowerCover a₀
        ia₀ = meet-irr ⊥≢a₀ (∧-lowerˡ , λ e → r₀≰ (≤-trans ∨-upperˡ (≤-trans (≤-reflexive′ (sym e)) ∧-lowerʳ)))
                            (∧-lowerʳ , λ e → part2 (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sym e)) ∧-lowerˡ))) refl
          where
          ⊥≢a₀ : ⊥ᴸ ≢ a₀
          ⊥≢a₀ e = proj₂ i₂ (≤-antisym (₋≤ r₂) (≤-trans a≤a₀ (≤-trans (≤-reflexive′ (sym e)) (⊥ᴸ-least _))))

        a≤a₁ : a ≤ a₁
        a≤a₁ = <→≤₋ a<a₀

        r₃₋≤a₁ : r₃ ₋ ≤ a₁
        r₃₋≤a₁ = ≤-trans r₃₋≤r₂₋ (≤-trans (₋≤ r₂) a≤a₁)

        r₃≤a₀ : r₃ ≤ a₀
        r₃≤a₀ = ≤-trans (proj₁ r₃<r₂) a≤a₀

        a₀≤r₃∨r₄ : a₀ ≤ r₃ ∨ r₄
        a₀≤r₃∨r₄ = ≤-trans ∧-lowerʳ (∨-least r₂≤r₃∨r₄ ∨-upperʳ)

        r₄≰a₀ : ¬ r₄ ≤ a₀
        r₄≰a₀ h = part2 (≤-trans h ∧-lowerˡ)

        r₄≰a₀∨r₄₋ : ¬ r₄ ≤ a₀ ∨ (r₄ ₋)
        r₄≰a₀∨r₄₋ = absorb a₀ (r₄ ₋) r₃≤a₀ a₀≤r₃∨r₄ ≤-refl r₄≰a₀

        -- 5.38 (6): a₀ ≤ a₁ ∨ b₀ = a₁ ∨ r₄₋ fails by (W).
        a₀≰ : ¬ a₀ ≤ a₁ ∨ b₀
        a₀≰ h = cases (W (r₀ ∨ r₂) (r₂ ∨ r₄) a₁ (r₄ ₋) (≤-trans h (∨-least ∨-upperˡ (∨-least (≤∨ˡ r₃₋≤a₁) ∨-upperʳ))))
          where
          cases : (r₀ ∨ r₂ ≤ a₁ ∨ (r₄ ₋) ⊎ r₂ ∨ r₄ ≤ a₁ ∨ (r₄ ₋)) ⊎ (a₀ ≤ a₁ ⊎ a₀ ≤ r₄ ₋) → ⊥
          cases (inj₁ (inj₁ h′)) = r₀≰ (≤-trans ∨-upperˡ (≤-trans h′ (∨-least (≤-trans (₋≤ a₀) ∧-lowerʳ) (≤∨ʳ (₋≤ r₄)))))
          cases (inj₁ (inj₂ h′)) = r₄≰a₀∨r₄₋ (≤-trans ∨-upperʳ (≤-trans h′ (∨-monoˡ (₋≤ a₀))))
          cases (inj₂ (inj₁ h′)) = proj₂ ia₀ (≤-antisym (₋≤ a₀) h′)
          cases (inj₂ (inj₂ h′)) = r₂≰r₄₋ (≤-trans a≤a₀ h′)

        -- 5.38 (7): b₀ ≤ a₁ ∨ b gives r₄₋ ≤ a₁ ∨ r₄₋₋, and (W) on r₄₋ = r₄ ∧ (a₀ ∨ r₄₋) ≤ a₁ ∨ r₄₋₋ fails.
        b₀≰ : ¬ b₀ ≤ a₁ ∨ b
        b₀≰ h = cases (W r₄ (a₀ ∨ (r₄ ₋)) a₁ ((r₄ ₋) ₋) (≤-trans meet≤r₄₋ r₄₋≤))
          where
          r₄₋≤ : r₄ ₋ ≤ a₁ ∨ ((r₄ ₋) ₋)
          r₄₋≤ = ≤-trans ∨-upperʳ (≤-trans h (∨-least ∨-upperˡ (∨-least (≤∨ˡ r₃₋≤a₁) ∨-upperʳ)))

          r₄₋≤meet : r₄ ₋ ≤ r₄ ∧ (a₀ ∨ (r₄ ₋))
          r₄₋≤meet = ∧-greatest (₋≤ r₄) ∨-upperʳ

          meet≤r₄₋ : r₄ ∧ (a₀ ∨ (r₄ ₋)) ≤ r₄ ₋
          meet≤r₄₋ = <→≤₋′ ∧-lowerˡ λ e → r₄≰a₀∨r₄₋ (subst (_≤ a₀ ∨ (r₄ ₋)) e ∧-lowerʳ)

          cases : (r₄ ≤ a₁ ∨ ((r₄ ₋) ₋) ⊎ a₀ ∨ (r₄ ₋) ≤ a₁ ∨ ((r₄ ₋) ₋))
                ⊎ (r₄ ∧ (a₀ ∨ (r₄ ₋)) ≤ a₁ ⊎ r₄ ∧ (a₀ ∨ (r₄ ₋)) ≤ (r₄ ₋) ₋) → ⊥
          cases (inj₁ (inj₁ h′)) = r₄≰a₀∨r₄₋ (≤-trans h′ (∨-mono (₋≤ a₀) (₋≤ (r₄ ₋))))
          cases (inj₁ (inj₂ h′)) = a₀≰ (≤-trans ∨-upperˡ (≤-trans h′ (∨-monoʳ (≤∨ʳ (₋≤ (r₄ ₋))))))
          cases (inj₂ (inj₁ h′)) = r₄₋₋≰r₀∨r₂ (≤-trans (₋≤ (r₄ ₋)) (≤-trans r₄₋≤meet (≤-trans h′ (≤-trans (₋≤ a₀) ∧-lowerˡ))))
          cases (inj₂ (inj₂ h′)) = proj₂ i₄₋ (≤-antisym (₋≤ (r₄ ₋)) (≤-trans r₄₋≤meet h′))

        -- b = r₃₋ ∨ r₄₋₋ is join reducible: r₃₋ ≰ r₄₋₋, as r₃ ≰ r₄, and r₄₋₋ ≰ r₃₋.
        r₃₋≰r₄₋₋ : ¬ r₃ ₋ ≤ (r₄ ₋) ₋
        r₃₋≰r₄₋₋ h = r₃≰r₄ (≤-trans r₃≤r₃₋∨r₄ (∨-least (≤-trans h (≤-trans (₋≤ (r₄ ₋)) (₋≤ r₄))) ≤-refl))

        config : Config₃₈ a a₀ a₁ b b₀
        config = record
          { b-red  = λ { (b₋≤b , b₋≢b) → b₋≢b (≤-antisym b₋≤b (∨-least (<→≤₋ r₃₋<b) (<→≤₋ r₄₋₋<b))) }
          ; a-cond = inj₂ (i₂ , ≤-trans r₂≤r₂₋∨r₄₋₋ (∨-monoʳ ∨-upperʳ))
          ; a≤a₁   = a≤a₁
          ; a₁⋖a₀  = ₋⋖ ia₀
          ; b≤b₀   = ∨-mono ≤-refl (₋≤ (r₄ ₋))
          ; a≰b₀   = λ h → a≰κ i₃ (≤-trans (proj₁ r₃<r₂) (≤-trans h (∨-least (₋≤κ r₃) r₄₋≤κr₃)))
          ; b≰a₀   = λ h → r₄₋₋≰r₀∨r₂ (≤-trans ∨-upperʳ (≤-trans h ∧-lowerˡ))
          ; a₀≰    = a₀≰
          ; b₀≰    = b₀≰ }
          where
          r₃₋<b : r₃ ₋ < b
          r₃₋<b = ∨-upperˡ , λ e → r₄₋₋≰r₃₋ (≤ᵈ→ (sym e))

          r₄₋₋<b : (r₄ ₋) ₋ < b
          r₄₋₋<b = ∨-upperʳ , λ e → r₃₋≰r₄₋₋ (≤ᵈ→ (sym (trans e ∨-comm-law)))

      part1 : r₀ ≤ r₂ ∨ r₄
      part1 = decidable-stable (_ ≤? _) λ r₀≰ → no-config₃₈ (Part1.config r₀≰)

    -- Lemma 5.52: for a subsequence r₀ A₂ r₁ B₁ r₂ A₂ r₃ B₁ r₄ A₂ r₅, r₀ ≤ r₂ ∨ r₄ and r₄ ≰ r₀ ∨ r₂.
    lemma-5-52 : ∀ {x : ℕ → Fin (suc n)} (sub : Sub 5 x)
               → x 0 A₂ x 1 → x 1 B₁ x 2 → x 2 A₂ x 3 → x 3 B₁ x 4 → x 4 A₂ x 5
               → (x 0 ≤ x 2 ∨ x 4) × ¬ (x 4 ≤ x 0 ∨ x 2)
    lemma-5-52 sub A₀₁ B₁₂ A₂₃ B₃₄ A₄₅ = Lemma552.part1 sub A₀₁ B₁₂ A₂₃ B₃₄ A₄₅ , Lemma552.part2 sub A₀₁ B₁₂ A₂₃ B₃₄ A₄₅
```

#### Lemma 5.53

A minimal C-cycle `q₁ B₁ p₁ A₂ q₂ B₁ p₂ … qₙ B₁ pₙ A₂ q₁` is read from its
base `q₁`: `qⱼ₊₁` is the member at position `2j` and `pⱼ₊₁` at `2j + 1`, so its
length is `2n`.  The book's cases: `n = 1` contradicts `q₁ B₁ p₁` with
`p₁ A₂ q₁`; `n = 2` is Lemma 5.49 twice and (SD∨); and for `n ≥ 3`, Lemma
5.52 (1) on the windows `pⱼ, qⱼ₊₁, pⱼ₊₁, qⱼ₊₂, pⱼ₊₂, qⱼ₊₃` gives
`p₁ ≤ pₙ₋₁ ∨ pₙ` by induction, while Lemma 5.52 (2) on the window
`pₙ₋₁, qₙ, pₙ, q₁, p₁, q₂` denies it.  Each window is the rotation of the
cycle that starts it, read through `at-rotate-≤′`{.AgdaFunction} and
`at-rotate-wrap`{.AgdaFunction}.

```agda
  two : ℕ → ℕ
  two j = j + j

  two-suc : ∀ j → two (suc j) ≡ suc (suc (two j))
  two-suc j = cong suc (+-suc j j)

  two-mono : ∀ {a b} → a ≤ℕ b → two a ≤ℕ two b
  two-mono h = +-mono-≤ h h

  module Lemma553 (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 using ( at ; at-wrap ; at-irr )
    open Rotation 𝒞 using ( at-rotate-≤ ; at-rotate-≤′ ; at-rotate-wrap )

    kc : ℕ
    kc = MinimalCycle.k 𝒞

    -- The hypotheses: the cycle alternates B₁ and A₂ from its base, with 2n members.
    Bs-type As-type : Type
    Bs-type = ∀ j → two j ≤ℕ kc → at (two j) B₁ at (suc (two j))
    As-type = ∀ j → suc (two j) ≤ℕ kc → at (suc (two j)) A₂ at (suc (suc (two j)))

    -- n = 1: q₁ B₁ p₁ and p₁ A₂ q₁.
    case₁ : kc ≡ 1 → Bs-type → As-type → ⊥
    case₁ e Bs As = B→≰ (proj₁ (Bs 0 z≤n)) (proj₁ (A→< (proj₁ (subst (at 1 A₂_) at2≡at0 (As 0 (≤ℕ-reflexive (sym e)))))))
      where
      at2≡at0 : at 2 ≡ at 0
      at2≡at0 = trans (cong (λ z → at (suc z)) (sym e)) at-wrap

    -- n = 2: p₁ ≤ q₂ ∨ p₂ and p₂ ≤ q₁ ∨ p₁ (Lemma 5.49), so (q₁ ∨ q₂) ∨ p₁ = (q₁ ∨ q₂) ∨ p₂ and (SD∨) puts p₁
    -- below q₁ ∨ p₁₋ ≤ κ(p₁).
    case₂ : kc ≡ 3 → Bs-type → As-type → ⊥
    case₂ e Bs As = a≰κ (at-irr 1 (subst (1 ≤ℕ_) (sym e) (s≤s z≤n)))
      (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨ (at 0 ∨ at 2) (at 1) (at 3) e′))
                                 (∨-least (∨-least q₁≤κp₁ (≤-trans q₂≤p₁₋ (₋≤κ (at 1)))) (≤-trans p₁∧p₂≤p₁₋ (₋≤κ (at 1))))))
      where
      at4≡at0 : at 4 ≡ at 0
      at4≡at0 = trans (cong (λ z → at (suc z)) (sym e)) at-wrap

      B₀₁ : at 0 B₁ at 1
      B₀₁ = Bs 0 z≤n

      A₁₂ : at 1 A₂ at 2
      A₁₂ = As 0 (subst (1 ≤ℕ_) (sym e) (s≤s z≤n))

      B₂₃ : at 2 B₁ at 3
      B₂₃ = Bs 1 (subst (2 ≤ℕ_) (sym e) (s≤s (s≤s z≤n)))

      A₃₀ : at 3 A₂ at 0
      A₃₀ = subst (at 3 A₂_) at4≡at0 (As 1 (≤ℕ-reflexive (sym e)))

      p₁≤q₂∨p₂ : at 1 ≤ at 2 ∨ at 3
      p₁≤q₂∨p₂ = lemma-5-49 A₁₂ B₂₃

      p₂≤q₁∨p₁ : at 3 ≤ at 0 ∨ at 1
      p₂≤q₁∨p₁ = lemma-5-49 A₃₀ B₀₁

      q₂≤p₁₋ : at 2 ≤ at 1 ₋
      q₂≤p₁₋ = <→≤₋ (A→< (proj₁ A₁₂))

      q₁≤κp₁ : at 0 ≤ κ (at 1)
      q₁≤κp₁ = B→≤κ (proj₁ B₀₁)

      e′ : (at 0 ∨ at 2) ∨ at 1 ≡ (at 0 ∨ at 2) ∨ at 3
      e′ = ≤-antisym (∨-least ∨-upperˡ (≤-trans p₁≤q₂∨p₂ (∨-least (≤∨ˡ ∨-upperʳ) ∨-upperʳ)))
                     (∨-least ∨-upperˡ (≤-trans p₂≤q₁∨p₁ (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ)))

      p₁∧p₂≤p₁₋ : at 1 ∧ at 3 ≤ at 1 ₋
      p₁∧p₂≤p₁₋ = <→≤₋′ ∧-lowerˡ λ e″ → B→≰ (proj₁ B₂₃) (≤-trans (≤-trans q₂≤p₁₋ (₋≤ (at 1))) (subst (_≤ at 3) e″ ∧-lowerʳ))

    -- n ≥ 3, with n = n″ + 3: the chain p₁ ≤ pⱼ₊₁ ∨ pⱼ₊₂ by Lemma 5.52 (1), against Lemma 5.52 (2).
    module Case₃ (n″ : ℕ) (e : kc ≡ suc (two (suc (suc n″)))) (Bs : Bs-type) (As : As-type) where
      n′ : ℕ
      n′ = suc (suc n″)

      P : ℕ → Fin (suc n)
      P j = at (suc (two j))

      5≤kc : 5 ≤ℕ kc
      5≤kc = subst (5 ≤ℕ_) (sym e) (s≤s (two-mono (s≤s (s≤s z≤n))))

      two-ss : ∀ j → two (suc (suc j)) ≡ suc (suc (suc (suc (two j))))
      two-ss j = trans (two-suc (suc j)) (cong (λ z → suc (suc z)) (two-suc j))

      -- The window pⱼ₊₁, qⱼ₊₂, pⱼ₊₁, qⱼ₊₂, pⱼ₊₂, qⱼ₊₃, the rotation by 2j + 1, for j + 2 ≤ n′.
      module Window (j : ℕ) (j+2≤n′ : suc (suc j) ≤ℕ n′) where
        r : ℕ
        r = suc (two j)

        𝒞′ : MinimalCycle
        𝒞′ = rotate 𝒞 r

        module 𝒫′ = MinimalCycleProperties 𝒞′

        bound : suc (two (suc (suc j))) ≤ℕ kc
        bound = subst (suc (two (suc (suc j))) ≤ℕ_) (sym e) (s≤s (two-mono j+2≤n′))

        -- The positions read by the window, as indices of the hypotheses.
        e₀ : r + 0 ≡ suc (two j)
        e₀ = +-identityʳ r

        e₁ : r + 1 ≡ suc (suc (two j))
        e₁ = +-comm r 1

        e₁′ : r + 1 ≡ two (suc j)
        e₁′ = trans e₁ (sym (two-suc j))

        e₂ : r + 2 ≡ suc (two (suc j))
        e₂ = trans (+-comm r 2) (cong suc (sym (two-suc j)))

        e₃ : r + 3 ≡ suc (suc (two (suc j)))
        e₃ = trans (+-comm r 3) (cong (λ z → suc (suc z)) (sym (two-suc j)))

        e₃′ : r + 3 ≡ two (suc (suc j))
        e₃′ = trans (+-comm r 3) (sym (two-ss j))

        e₄ : r + 4 ≡ suc (two (suc (suc j)))
        e₄ = trans (+-comm r 4) (cong suc (sym (two-ss j)))

        e₅ : r + 5 ≡ suc (suc (two (suc (suc j))))
        e₅ = trans (+-comm r 5) (cong (λ z → suc (suc z)) (sym (two-ss j)))

        r+5≤sK : r + 5 ≤ℕ suc kc
        r+5≤sK = subst (_≤ℕ suc kc) (sym e₅) (s≤s bound)

        rd : ∀ t → t ≤ℕ 5 → ∀ m → r + t ≡ m → 𝒫′.at t ≡ at m
        rd t t≤5 m eq = trans (at-rotate-≤′ r (≤ℕ-trans t≤5 5≤kc) (≤ℕ-trans (+-monoʳ-≤ r t≤5) r+5≤sK)) (cong at eq)

        sub′ : 𝒫′.Sub 5 𝒫′.at
        sub′ = 𝒫′.Sub-prefix 𝒫′.whole 5≤kc

        -- Bounds for the hypotheses used.
        b₁ : suc (two j) ≤ℕ kc
        b₁ = ≤ℕ-trans (s≤s (two-mono (≤ℕ-trans (n≤1+n j) (n≤1+n (suc j))))) bound

        b₂ : two (suc j) ≤ℕ kc
        b₂ = ≤ℕ-trans (two-mono (n≤1+n (suc j))) (<⇒≤ bound)

        b₃ : suc (two (suc j)) ≤ℕ kc
        b₃ = ≤ℕ-trans (s≤s (two-mono (n≤1+n (suc j)))) bound

        b₄ : two (suc (suc j)) ≤ℕ kc
        b₄ = <⇒≤ bound

        5≤5 : 5 ≤ℕ 5
        5≤5 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

        A₀₁′ : 𝒫′.at 0 A₂ 𝒫′.at 1
        A₀₁′ = subst₂ _A₂_ (sym (rd 0 z≤n _ e₀)) (sym (rd 1 (s≤s z≤n) _ e₁)) (As j b₁)

        B₁₂′ : 𝒫′.at 1 B₁ 𝒫′.at 2
        B₁₂′ = subst₂ _B₁_ (sym (rd 1 (s≤s z≤n) _ e₁′)) (sym (rd 2 (s≤s (s≤s z≤n)) _ e₂)) (Bs (suc j) b₂)

        A₂₃′ : 𝒫′.at 2 A₂ 𝒫′.at 3
        A₂₃′ = subst₂ _A₂_ (sym (rd 2 (s≤s (s≤s z≤n)) _ e₂)) (sym (rd 3 (s≤s (s≤s (s≤s z≤n))) _ e₃)) (As (suc j) b₃)

        B₃₄′ : 𝒫′.at 3 B₁ 𝒫′.at 4
        B₃₄′ = subst₂ _B₁_ (sym (rd 3 (s≤s (s≤s (s≤s z≤n))) _ e₃′)) (sym (rd 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) _ e₄)) (Bs (suc (suc j)) b₄)

        A₄₅′ : 𝒫′.at 4 A₂ 𝒫′.at 5
        A₄₅′ = subst₂ _A₂_ (sym (rd 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) _ e₄)) (sym (rd 5 5≤5 _ e₅)) (As (suc (suc j)) bound)

        -- Lemma 5.52 (1): pⱼ₊₁ ≤ pⱼ₊₂ ∨ pⱼ₊₃.
        step : P j ≤ P (suc j) ∨ P (suc (suc j))
        step = subst (λ a → a ≤ P (suc j) ∨ P (suc (suc j))) (rd 0 z≤n _ e₀)
                 (subst (λ b → 𝒫′.at 0 ≤ b ∨ P (suc (suc j))) (rd 2 (s≤s (s≤s z≤n)) _ e₂)
                   (subst (λ c → 𝒫′.at 0 ≤ 𝒫′.at 2 ∨ c) (rd 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) _ e₄)
                     (proj₁ (InCycle.lemma-5-52 𝒞′ sub′ A₀₁′ B₁₂′ A₂₃′ B₃₄′ A₄₅′))))

      -- p₁ ≤ pⱼ₊₁ ∨ pⱼ₊₂ for j + 1 ≤ n′, by induction.
      chain : ∀ j → suc j ≤ℕ n′ → at 1 ≤ P j ∨ P (suc j)
      chain zero     _      = ∨-upperˡ
      chain (suc j)  sj+1≤n′ = ≤-trans (chain j (≤ℕ-trans (n≤1+n (suc j)) sj+1≤n′)) (∨-least (Window.step j sj+1≤n′) ∨-upperˡ)

      -- The window pₙ₋₁, qₙ, pₙ, q₁, p₁, q₂: the rotation by 2n - 3, read across the base.
      module Last where
        r : ℕ
        r = suc (two (suc n″))

        𝒞′ : MinimalCycle
        𝒞′ = rotate 𝒞 r

        module 𝒫′ = MinimalCycleProperties 𝒞′

        kc≡ : kc ≡ suc (suc r)
        kc≡ = trans e (cong suc (two-suc (suc n″)))

        sub′ : 𝒫′.Sub 5 𝒫′.at
        sub′ = 𝒫′.Sub-prefix 𝒫′.whole 5≤kc

        t≤kc : ∀ {t} → t ≤ℕ 5 → t ≤ℕ kc
        t≤kc t≤5 = ≤ℕ-trans t≤5 5≤kc

        -- The three members before the base: positions r, r + 1 and r + 2 = kc.
        rd₀ : 𝒫′.at 0 ≡ at r
        rd₀ = trans (at-rotate-≤ r (subst (r + 0 ≤ℕ_) (sym kc≡) (≤ℕ-reflexive′ (+-identityʳ r)))) (cong at (+-identityʳ r))
          where
          ≤ℕ-reflexive′ : r + 0 ≡ r → r + 0 ≤ℕ suc (suc r)
          ≤ℕ-reflexive′ eq = ≤ℕ-trans (≤ℕ-reflexive eq) (≤ℕ-trans (n≤1+n r) (n≤1+n (suc r)))

        rd₁ : 𝒫′.at 1 ≡ at (suc r)
        rd₁ = trans (at-rotate-≤ r (subst (r + 1 ≤ℕ_) (sym kc≡) (≤ℕ-trans (≤ℕ-reflexive (+-comm r 1)) (n≤1+n (suc r))))) (cong at (+-comm r 1))

        rd₂ : 𝒫′.at 2 ≡ at kc
        rd₂ = trans (at-rotate-≤ r (subst (r + 2 ≤ℕ_) (sym kc≡) (≤ℕ-reflexive (+-comm r 2)))) (cong at (trans (+-comm r 2) (sym kc≡)))

        -- The three after it: positions 0, 1 and 2 again.
        rdw : ∀ t → t ≤ℕ 5 → ∀ d → r + t ≡ d + suc kc → d ≤ℕ kc → 𝒫′.at t ≡ at d
        rdw t t≤5 d eq d≤kc = at-rotate-wrap r d (t≤kc t≤5) eq d≤kc

        sK≡ : suc kc ≡ suc (suc (suc r))
        sK≡ = cong suc kc≡

        rd₃ : 𝒫′.at 3 ≡ at 0
        rd₃ = rdw 3 (s≤s (s≤s (s≤s z≤n))) 0 (trans (+-comm r 3) (sym sK≡)) z≤n

        rd₄ : 𝒫′.at 4 ≡ at 1
        rd₄ = rdw 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) 1 (trans (+-comm r 4) (cong suc (sym sK≡))) (t≤kc (s≤s z≤n))

        rd₅ : 𝒫′.at 5 ≡ at 2
        rd₅ = rdw 5 (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) 2 (trans (+-comm r 5) (cong (λ z → suc (suc z)) (sym sK≡))) (t≤kc (s≤s (s≤s z≤n)))

        -- The hypotheses: pₙ₋₁ A₂ qₙ, qₙ B₁ pₙ, pₙ A₂ q₁, q₁ B₁ p₁ and p₁ A₂ q₂.
        r≤kc : r ≤ℕ kc
        r≤kc = subst (r ≤ℕ_) (sym kc≡) (≤ℕ-trans (n≤1+n r) (n≤1+n (suc r)))

        A₀₁′ : 𝒫′.at 0 A₂ 𝒫′.at 1
        A₀₁′ = subst₂ _A₂_ (sym rd₀) (sym rd₁) (As (suc n″) r≤kc)

        B₁₂′ : 𝒫′.at 1 B₁ 𝒫′.at 2
        B₁₂′ = subst₂ _B₁_ (sym (trans rd₁ (cong at (sym (two-suc (suc n″)))))) (sym (trans rd₂ (cong at e))) (Bs (suc (suc n″)) (subst (_≤ℕ kc) (sym (two-suc (suc n″))) (subst (suc r ≤ℕ_) (sym kc≡) (n≤1+n (suc r)))))

        A₂₃′ : 𝒫′.at 2 A₂ 𝒫′.at 3
        A₂₃′ = subst₂ _A₂_ (sym (trans rd₂ (cong at e))) (sym (trans rd₃ (trans (sym at-wrap) (cong (λ z → at (suc z)) e)))) (As (suc (suc n″)) (≤ℕ-reflexive (sym e)))

        B₃₄′ : 𝒫′.at 3 B₁ 𝒫′.at 4
        B₃₄′ = subst₂ _B₁_ (sym rd₃) (sym rd₄) (Bs 0 z≤n)

        A₄₅′ : 𝒫′.at 4 A₂ 𝒫′.at 5
        A₄₅′ = subst₂ _A₂_ (sym rd₄) (sym rd₅) (As 0 (t≤kc (s≤s z≤n)))

        -- Lemma 5.52 (2): p₁ ≰ pₙ₋₁ ∨ pₙ.
        part2 : ¬ at 1 ≤ P (suc n″) ∨ P (suc (suc n″))
        part2 h = proj₂ (InCycle.lemma-5-52 𝒞′ sub′ A₀₁′ B₁₂′ A₂₃′ B₃₄′ A₄₅′)
                        (subst (λ a → a ≤ 𝒫′.at 0 ∨ 𝒫′.at 2) (sym rd₄)
                          (subst (λ b → at 1 ≤ b ∨ 𝒫′.at 2) (sym rd₀)
                            (subst (λ c → at 1 ≤ P (suc n″) ∨ c) (sym (trans rd₂ (cong at e))) h)))

      contradiction : ⊥
      contradiction = Last.part2 (chain (suc n″) ≤ℕ-refl)

    -- Lemma 5.53: no minimal C-cycle is of the form q₁ B₁ p₁ A₂ q₂ B₁ p₂ … qₙ B₁ pₙ A₂ q₁.
    lemma-5-53 : ∀ n′ → kc ≡ suc (two n′) → Bs-type → As-type → ⊥
    lemma-5-53 zero           e Bs As = case₁ e Bs As
    lemma-5-53 (suc zero)     e Bs As = case₂ e Bs As
    lemma-5-53 (suc (suc n″)) e Bs As = Case₃.contradiction n″ e Bs As
```
