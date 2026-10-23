---
layout: default
file: "src/Lattices/Nation/Lemma548.lagda.md"
title: "Lattices.Nation.Lemma548 module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Lemma 5.48: under the hypotheses of Lemma 5.47, p is the lower cover of q_k

This is the [Lattices.Nation.Lemma548][] module of the [agda-lattices][]
library.

Lemma 5.48 of [Freese, Ježek, and Nation (1995)][] (pp. 119 and 120) has the
hypotheses of Lemma 5.47 ([Lattices.Nation.Lemma547][]): a subsequence
`q₀, …, q_k, p` of a minimal C-cycle in an S-lattice with `q₀, …, q_k` a B-type
sequence, `q_k A₂ p`, `q₀ ≤ κ(p)` and `p₋ ≮ q₀₋`; and it concludes
`p = q_{k*}`.  Supposing `p < q_{k*}`, Lemma 5.43 applies to the sequence
itself with `t = q_{k*}`: its hypotheses are immediate from Lemma 5.47 and
(B3), except (6), `q_{k*} ≰ u` for `u = p ∨ ⋁ᵢ₍ₖ₋₁ qᵢ₋ ∨ q_{k-1}`, which (W)
proves.  The surviving disjunct, `κ(q_k) ≤ u`, makes `u = κ(q_k)`; then
`κ(p) ∧ ⋁ᵢ≤ₖ qᵢ ≤ κ(q_k)`, by (SD∨) applied to
`⋁ᵢ₍ₖ qᵢ ∨ q_{k*} ∨ q_k = ⋁ᵢ₍ₖ qᵢ ∨ q_{k*} ∨ (κ(p) ∧ ⋁ᵢ≤ₖ qᵢ)` otherwise, and a
second application of (W) to this inequality fails in every disjunct, by (B1)
and `p₋ ≰ q₀₋`.  Lemma 5.43 then gives `⋁ᵢ₍ₖ qᵢ₋ ≰ κ(p)`, against Lemma 5.47.
Nation's paper states the lemma as its Lemma 3.6, with the same proof.

The module checks in 1.8 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Lemma548 where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; s≤s )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; <-trans to <ℕ-trans )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; sym )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType         as BTypeModule
import Lattices.Nation.Lemma547      as Lemma547Module
import Lattices.Nation.Subsequences  as SubsequencesModule
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### The setting

```agda
module Lemma548 {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least ; W-⋁< )
  module L547 = Lemma547Module.Lemma547 laws sd w
  module Subs = SubsequencesModule.Subsequences laws sd w

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 hiding ( k )
    open BT.InCycle 𝒞
    open L547.InCycle 𝒞 using ( lemma-5-47 )
    module SubsC = Subs.InCycle 𝒞

    -- q₀, …, q_k, p with k = j′ + 1, under the hypotheses of Lemma 5.47, and p ≠ q_{k*}.
    module Setting {j′ : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub (suc (suc j′)) x) (bt : BType (suc j′) x)
                   (hA₂ : x (suc j′) A₂ x (suc (suc j′))) (q₀≤κp : x 0 ≤ κ (x (suc (suc j′))))
                   (¬p₋<q₀₋ : ¬ (x (suc (suc j′)) ₋ < x 0 ₋)) (ne : x (suc (suc j′)) ≢ x (suc j′) ₋) where
      open BType bt

      k : ℕ
      k = suc j′

      p : Fin (suc n)
      p = x (suc k)

      q₋ : ℕ → Fin (suc n)
      q₋ i = x i ₋

      irr : ∀ {i} → i ≤ℕ suc k → HasOneLowerCover (x i)
      irr = Sub-irr sub

      iₚ : HasOneLowerCover p
      iₚ = irr ≤ℕ-refl

      iₖ : HasOneLowerCover (x k)
      iₖ = irr (n≤1+n k)

      -- Consequences of q_k A₂ p.
      hA : x k A p
      hA = proj₁ hA₂

      qₖ∧κp≡p₋ : x k ∧ κ p ≡ p ₋
      qₖ∧κp≡p₋ = proj₂ hA₂

      p≤qₖ₋ : p ≤ x k ₋
      p≤qₖ₋ = <→≤₋ (A→< hA)

      p<qₖ₋ : p < x k ₋
      p<qₖ₋ = p≤qₖ₋ , ne

      qₖ≤p∨κp : x k ≤ p ∨ κ p
      qₖ≤p∨κp = proj₂ (proj₂ (proj₂ hA))

      -- Lemma 5.47.
      p₋≰q₀₋ : ¬ p ₋ ≤ x 0 ₋
      p₋≰q₀₋ = proj₁ (lemma-5-47 sub bt hA₂ q₀≤κp ¬p₋<q₀₋)

      ⋁<ₖ≤κp : ⋁< x k ≤ κ p
      ⋁<ₖ≤κp = proj₂ (lemma-5-47 sub bt hA₂ q₀≤κp ¬p₋<q₀₋)

      xᵢ≤κp : ∀ {i} → i <ℕ k → x i ≤ κ p
      xᵢ≤κp i<k = ≤-trans (⋁<-upper x i<k) ⋁<ₖ≤κp

      -- Y = ⋁ᵢ₍ₖ₋₁ qᵢ₋ and u = p ∨ Y ∨ q_{k-1}, the right side of 5.43 (6), and its bound κ(q_k).
      Y u : Fin (suc n)
      Y = ⋁< q₋ j′
      u = p ∨ (Y ∨ x j′)

      u≤κqₖ : u ≤ κ (x k)
      u≤κqₖ = ∨-least (≤-trans p≤qₖ₋ (₋≤κ (x k)))
                      (∨-least (⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (B2 (<ℕ-trans i<j′ (n<1+n j′)) ≤ℕ-refl))
                               (B2 (n<1+n j′) ≤ℕ-refl))

      from-qₖ : ¬ x k ≤ u
      from-qₖ le = a≰κ iₖ (≤-trans le u≤κqₖ)

      -- q_{k*} ≰ p, since p < q_{k*}.
      from-qₖ₋≤p : ¬ x k ₋ ≤ p
      from-qₖ₋≤p le = ne (≤-antisym p≤qₖ₋ le)

      -- q_{k*} ≰ q_{i*} for i < k - 1, by (B4).
      from-qₖ₋≤qᵢ₋ : ∀ i → i <ℕ j′ → ¬ x k ₋ ≤ x i ₋
      from-qₖ₋≤qᵢ₋ i i<j′ le = B4 (s≤s i<j′) ≤ℕ-refl (≤-trans le (₋≤κ (x i)))

      -- q_{k*} ≰ q_{k-1}: equality contradicts (B1); and q_{k*} ≤ q_{k-1*} contradicts p₋ ≰ q₀₋ when
      -- k = 1, and (B3) with (B4) when k ≥ 2.
      from-qₖ₋≤qⱼ′ : ¬ x k ₋ ≤ x j′
      from-qₖ₋≤qⱼ′ le = split j′ bt p₋≰q₀₋ (≤-trans (₋≤ p) p≤qₖ₋) (<→≤₋′ le λ e → B1 ≤ℕ-refl (≤-trans (₋≤ (x j′)) (≤-trans (≤-reflexive′ (sym e)) (₋≤ (x k)))))
        where
        split : ∀ j′ {x : ℕ → Fin (suc n)} (bt : BType (suc j′) x) → ¬ x (suc (suc j′)) ₋ ≤ x 0 ₋
              → x (suc (suc j′)) ₋ ≤ x (suc j′) ₋ → ¬ x (suc j′) ₋ ≤ x j′ ₋
        split zero      bt p₋≰q₀₋ p₋≤qₖ₋ le = p₋≰q₀₋ (≤-trans p₋≤qₖ₋ le)
        split (suc j″)  bt _      _      le = BType.B4 bt ≤ℕ-refl ≤ℕ-refl (≤-trans le (BType.B3 bt (n≤1+n (suc j″))))
```

#### The case κ(q_k) ≤ u

```agda
      module Last (κqₖ≤u : κ (x k) ≤ u) where
        -- Q = ⋁ᵢ≤ₖ qᵢ, and the meet κ(p) ∧ Q, which lies below κ(q_k): otherwise q_k ≤ q_{k*} ∨ (κ(p) ∧ Q)
        -- by Lemma 2.57, (SD∨) applies to ⋁ᵢ₍ₖ qᵢ ∨ q_{k*} ∨ q_k = ⋁ᵢ₍ₖ qᵢ ∨ q_{k*} ∨ (κ(p) ∧ Q), and
        -- q_k ∧ κ(p) ∧ Q ≤ p₋ ≤ q_{k*} leaves q_k ≤ ⋁ᵢ₍ₖ qᵢ ∨ q_{k*} ≤ κ(q_k).
        Q meet X₀ : Fin (suc n)
        Q = ⋁< x (suc k)
        meet = κ p ∧ Q
        X₀ = ⋁< x k ∨ (x k ₋)

        X₀≤κqₖ : X₀ ≤ κ (x k)
        X₀≤κqₖ = ∨-least (⋁<-least x λ i i<k → B2 i<k ≤ℕ-refl) (₋≤κ (x k))

        meet≤κqₖ : meet ≤ κ (x k)
        meet≤κqₖ = decidable-stable (_ ≤? _) λ meet≰ →
          a≰κ iₖ (≤-trans (≤-trans ∨-upperʳ (≤-reflexive′ (sd∨ X₀ (x k) meet (e₁ meet≰)))) (∨-least X₀≤κqₖ (≤-trans qₖ∧meet≤X₀ X₀≤κqₖ)))
          where
          e₁ : ¬ meet ≤ κ (x k) → X₀ ∨ x k ≡ X₀ ∨ meet
          e₁ meet≰ = ≤-antisym (∨-least ∨-upperˡ (≤-trans (≰κ→ iₖ meet≰) (∨-monoˡ ∨-upperʳ)))
                               (∨-least ∨-upperˡ (≤-trans ∧-lowerʳ (∨-monoˡ ∨-upperˡ)))

          qₖ∧meet≤X₀ : x k ∧ meet ≤ X₀
          qₖ∧meet≤X₀ = ≤-trans (∧-monoʳ ∧-lowerˡ) (≤-trans (≤-reflexive′ qₖ∧κp≡p₋) (≤-trans (₋≤ p) (≤-trans p≤qₖ₋ ∨-upperʳ)))

        -- κ(p) ≰ κ(q_k), as q_k ≤ p ∨ κ(p) with p ≤ κ(q_k); and Q ≰ κ(q_k), as q_k ≤ Q.
        from-κp : ¬ κ p ≤ u
        from-κp le = a≰κ iₖ (≤-trans qₖ≤p∨κp (∨-least (≤-trans p≤qₖ₋ (₋≤κ (x k))) (≤-trans le u≤κqₖ)))

        from-Q : ¬ Q ≤ u
        from-Q le = a≰κ iₖ (≤-trans (⋁<-upper x (n<1+n k)) (≤-trans le u≤κqₖ))

        -- Members of the sequence before q_k lie below the meet, and so does p₋.
        xᵢ≤meet : ∀ {i} → i <ℕ k → x i ≤ meet
        xᵢ≤meet i<k = ∧-greatest (xᵢ≤κp i<k) (⋁<-upper x (<ℕ-trans i<k (n<1+n k)))

        p₋≤meet : p ₋ ≤ meet
        p₋≤meet = ∧-greatest (₋≤κ p) (≤-trans (₋≤ p) (≤-trans p≤qₖ₋ (≤-trans (₋≤ (x k)) (⋁<-upper x (n<1+n k)))))

        -- The meet is not below p: q_{k-1} ≤ p ≤ q_k would contradict (B1).
        from-meet≤p : ¬ meet ≤ p
        from-meet≤p le = B1 ≤ℕ-refl (≤-trans (₋≤ (x j′)) (≤-trans (xᵢ≤meet (n<1+n j′)) (≤-trans le (≤-trans p≤qₖ₋ (₋≤ (x k))))))

        -- Nor below q_{i*} for i < k - 1: p₋ ≤ q₀₋ contradicts Lemma 5.47, and q_{i-1} ≤ q_{i*} (B1).
        from-meet≤qᵢ₋ : ∀ i → i <ℕ j′ → ¬ meet ≤ x i ₋
        from-meet≤qᵢ₋ zero     _     le = p₋≰q₀₋ (≤-trans p₋≤meet le)
        from-meet≤qᵢ₋ (suc i′) si′<j′ le =
          B1 (<⇒≤ (<ℕ-trans si′<j′ (n<1+n j′))) (≤-trans (₋≤ (x i′)) (≤-trans (xᵢ≤meet (<ℕ-trans (n<1+n i′) (<ℕ-trans si′<j′ (n<1+n j′)))) (≤-trans le (₋≤ (x (suc i′))))))

        -- Nor below q_{k-1}: for k = 1, p₋ ≤ q₀ with p₋ ≠ q₀ puts p₋ below q₀₋; for k ≥ 2, q_{k-2} ≤ q_{k-1}
        -- contradicts (B1).
        from-meet≤qⱼ′ : ¬ meet ≤ x j′
        from-meet≤qⱼ′ le = split j′ bt p₋≰q₀₋ (≤-trans (₋≤ p) (≤-trans p≤qₖ₋ (₋≤ (x k)))) (≤-trans p₋≤meet le)
                                 (λ i<k → ≤-trans (xᵢ≤meet i<k) le)
          where
          split : ∀ j′ {x : ℕ → Fin (suc n)} (bt : BType (suc j′) x) → ¬ x (suc (suc j′)) ₋ ≤ x 0 ₋
                → x (suc (suc j′)) ₋ ≤ x (suc j′) → x (suc (suc j′)) ₋ ≤ x j′ → (∀ {i} → i <ℕ suc j′ → x i ≤ x j′) → ⊥
          split zero     {x} bt p₋≰q₀₋ p₋≤q₁ p₋≤q₀ _ =
            p₋≰q₀₋ (<→≤₋′ p₋≤q₀ λ e → BType.B1 bt ≤ℕ-refl (≤-trans (₋≤ (x 0)) (≤-trans (≤-reflexive′ (sym e)) p₋≤q₁)))
          split (suc j″) {x} bt _ _ _ f = BType.B1 bt (n≤1+n (suc j″)) (≤-trans (₋≤ (x j″)) (f (<ℕ-trans (n<1+n j″) (n<1+n (suc j″)))))

        contradiction : ⊥
        contradiction = outer (W (κ p) Q p (Y ∨ x j′) (≤-trans meet≤κqₖ κqₖ≤u))
          where
          inner : (κ p ≤ Y ∨ x j′ ⊎ Q ≤ Y ∨ x j′) ⊎ ((Σ ℕ λ i → i <ℕ j′ × meet ≤ x i ₋) ⊎ meet ≤ x j′) → ⊥
          inner (inj₁ (inj₁ le))               = from-κp (≤∨ʳ le)
          inner (inj₁ (inj₂ le))               = from-Q (≤∨ʳ le)
          inner (inj₂ (inj₁ (i , i<j′ , le)))  = from-meet≤qᵢ₋ i i<j′ le
          inner (inj₂ (inj₂ le))               = from-meet≤qⱼ′ le

          outer : (κ p ≤ u ⊎ Q ≤ u) ⊎ (meet ≤ p ⊎ meet ≤ Y ∨ x j′) → ⊥
          outer (inj₁ (inj₁ le)) = from-κp le
          outer (inj₁ (inj₂ le)) = from-Q le
          outer (inj₂ (inj₁ le)) = from-meet≤p le
          outer (inj₂ (inj₂ le)) = inner (W-⋁< q₋ j′ le)
```

#### Lemma 5.48

```agda
      -- 5.43 (6): (W) on q_{k*} = q_k ∧ κ(q_k) ≤ u.
      qₖ₋≰u : ¬ x k ₋ ≤ u
      qₖ₋≰u le = outer (W (x k) (κ (x k)) p (Y ∨ x j′) (≤-trans (≤-reflexive′ (a∧κ iₖ)) le))
        where
        qₖ₋≤m : x k ₋ ≤ x k ∧ κ (x k)
        qₖ₋≤m = ∧-greatest (₋≤ (x k)) (₋≤κ (x k))

        inner : (x k ≤ Y ∨ x j′ ⊎ κ (x k) ≤ Y ∨ x j′) ⊎ ((Σ ℕ λ i → i <ℕ j′ × x k ∧ κ (x k) ≤ x i ₋) ⊎ x k ∧ κ (x k) ≤ x j′) → ⊥
        inner (inj₁ (inj₁ le′))               = from-qₖ (≤∨ʳ le′)
        inner (inj₁ (inj₂ le′))               = Last.contradiction (≤∨ʳ le′)
        inner (inj₂ (inj₁ (i , i<j′ , le′)))  = from-qₖ₋≤qᵢ₋ i i<j′ (≤-trans qₖ₋≤m le′)
        inner (inj₂ (inj₂ le′))               = from-qₖ₋≤qⱼ′ (≤-trans qₖ₋≤m le′)

        outer : (x k ≤ u ⊎ κ (x k) ≤ u) ⊎ (x k ∧ κ (x k) ≤ p ⊎ x k ∧ κ (x k) ≤ Y ∨ x j′) → ⊥
        outer (inj₁ (inj₁ le′)) = from-qₖ le′
        outer (inj₁ (inj₂ le′)) = Last.contradiction le′
        outer (inj₂ (inj₁ le′)) = from-qₖ₋≤p (≤-trans qₖ₋≤m le′)
        outer (inj₂ (inj₂ le′)) = inner (W-⋁< q₋ j′ le′)

      -- Lemma 5.43 with t = q_{k*} gives ⋁ᵢ₍ₖ qᵢ₋ ≰ κ(p), against Lemma 5.47.
      contradiction : ⊥
      contradiction =
        SubsC.Lemma543.lemma-5-43 sub bt (x k ₋) p₋≰q₀₋ (≤-trans (₋≤ p) p≤qₖ₋) p<qₖ₋
                                  (≤-trans (₋≤ (x k)) qₖ≤p∨κp) (B3 ≤ℕ-refl) qₖ₋≰u (λ pBq₀ → B→≰κ pBq₀ q₀≤κp)
                                  (⋁<-least q₋ λ i i<k → ≤-trans (₋≤ (x i)) (xᵢ≤κp i<k))

    -- Lemma 5.48: with q_k A₂ p, q₀ ≤ κ(p) and p₋ ≮ q₀₋, p = q_{k*}.
    lemma-5-48 : ∀ {k x} (sub : Sub (suc k) x) (bt : BType k x) → x k A₂ x (suc k)
               → x 0 ≤ κ (x (suc k)) → ¬ (x (suc k) ₋ < x 0 ₋) → x (suc k) ≡ x k ₋
    lemma-5-48 {zero}   sub bt hA₂ q₀≤κp _       = ⊥-elim (A→≰κ (proj₁ hA₂) q₀≤κp)
    lemma-5-48 {suc j′} sub bt hA₂ q₀≤κp ¬p₋<q₀₋ =
      decidable-stable (_ ≟ _) λ ne → Setting.contradiction sub bt hA₂ q₀≤κp ¬p₋<q₀₋ ne
```
