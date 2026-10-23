---
layout: default
file: "src/Lattices/Nation/Subsequences.lagda.md"
title: "Lattices.Nation.Subsequences module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Lemmas 5.43 to 5.46: subsequences of a minimal C-cycle ending in an A

This is the [Lattices.Nation.Subsequences][] module of the [agda-lattices][]
library.

Lemmas 5.43 to 5.46 of [Freese, Ježek, and Nation (1995)][] (pp. 115 to 117)
study a subsequence `q₀, …, q_k, p` of a minimal C-cycle in an S-lattice with
`q₀, …, q_k` a B-type sequence and `q_k A p`, and conclude, under conditions on
the kind of the `A` and on `q₀`, that `p₋ < q₀₋`, that `p₋₋ < q₀₋`, or that
`⋁ᵢ₍ₖ qᵢ ≤ κ(p)` and `p = q_{k*}`.  They rest on Lemma 5.42
([Lattices.Nation.Lemma542][]) and on Lemma 5.43, which excludes a
configuration of Lemma 5.40 ([Lattices.Nation.Configurations][]).  The
conventions are those of [Lattices.Nation.BType][]: the subsequence is a family
`x` read at the indices up to `k + 1`, with `p` at `k + 1`.

The module checks in 1.8 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Subsequences where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n ; m≤n⇒m<n∨m≡n ; n≢0⇒n>0 ; 1+n≢0
                                                         ; +-monoˡ-< ; +-monoˡ-≤ )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-trans to ≤ℕ-trans
                                                            ; <-trans to <ℕ-trans ; <-≤-trans to <ℕ-≤-trans
                                                            ; <-irrefl to <ℕ-irrefl )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType     as BTypeModule
import Lattices.Nation.Lemma542  as Lemma542Module
open import Lattices.Nation.Configurations  using ( module ConfigurationsDual )
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```
-->

#### Lemma 5.43

Let `q₀, …, q_j, p` with `j ≥ 1` be a subsequence and `t` an element such that
`q₀, …, q_j` is a B-type sequence, `p₋ ≰ q₀₋`, `p₋ ≤ q_{j*}`, `p < t ≤ κ(p)*`,
`t ≤ κ(q_{j-1})`, `t ≰ p ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1}`, and `p B q₀` fails.  Then
`⋁ᵢ₍ⱼ qᵢ₋ ≰ κ(p)`.  Supposing otherwise, every `qᵢ`, `i < j`, lies below `κ(p)`
too, by the free star principle and the failure of `p B q₀`, and
`a = p ∨ ⋁ᵢ₍ⱼ qᵢ₋`, `a₀ = t ∨ ⋁ᵢ₍ⱼ qᵢ₋`, `b = p₋ ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1}` and
`b₀ = κ(p)` form the configuration of Lemma 5.40; its eight conditions are
verified as in the book, the last two by (W) applied to `a₀ ∧ b ≤ a` and to
`a ∧ b₀ ≤ b`, over the joinands of `a` and of `b`.  In the last case the book
treats a meet below `q_{j-1}` through `j = 1`; here, as the book's remark
intends, such a meet is `q_{j-1}` itself or lies below `q_{j-1*}`, and both are
excluded by (B1) or, when `j = 1`, by `a ≤ κ(q₀)` and `p₋ ≰ q₀₋`.

```agda
module Subsequences {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                    (laws : LatticeTableLaws _∧_ _∨_)
                    (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                    (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  module L542 = Lemma542Module.Lemma542 laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least ; W-⋁<
                ; keep-then ; keep-then-≤ ; keep-then-> ; keep-then-mono ; keep-then-bound )
  open ConfigurationsDual laws w using ( no-config₄₀ )

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞
    open BT.InCycle 𝒞

    module Lemma543 {j′ : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub (suc (suc j′)) x) (bt : BType (suc j′) x)
                    (t : Fin (suc n)) where
      open BType bt

      p : Fin (suc n)
      p = x (suc (suc j′))

      q₋ : ℕ → Fin (suc n)
      q₋ i = x i ₋

      X Y : Fin (suc n)
      X = ⋁< q₋ (suc j′)
      Y = ⋁< q₋ j′

      irr : ∀ {i} → i ≤ℕ suc (suc j′) → HasOneLowerCover (x i)
      irr = Sub-irr sub

      iₚ : HasOneLowerCover p
      iₚ = irr ≤ℕ-refl

      j′≤ : j′ ≤ℕ suc (suc j′)
      j′≤ = <⇒≤ (<ℕ-trans (n<1+n j′) (n<1+n (suc j′)))

      -- X ≤ κ(q_{j-1}), by (B2) and q_{j-1*} ≤ κ(q_{j-1}).
      X≤κⱼ′ : X ≤ κ (x j′)
      X≤κⱼ′ = ∨-least (⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (B2 i<j′ (<⇒≤ (n<1+n j′)))) (₋≤κ (x j′))

      lemma-5-43 : ¬ p ₋ ≤ q₋ 0 → p ₋ ≤ q₋ (suc j′) → p < t → t ≤ p ∨ κ p → t ≤ κ (x j′)
                 → ¬ t ≤ p ∨ (Y ∨ x j′) → ¬ (p B x 0) → ¬ X ≤ κ p
      lemma-5-43 p₋≰q₀₋ p₋≤qⱼ₋ p<t t≤κp⁺ t≤κⱼ′ t≰ ¬pBq₀ X≤κp = no-config₄₀ (record
        { a≤a₀ = ∨-mono (proj₁ p<t) ≤-refl ; b≤b₀ = b≤κp ; a≰b₀ = λ h → a≰κ iₚ (≤-trans ∨-upperˡ h)
        ; b≰a₀ = λ b≤a₀ → a≰κ (irr j′≤) (≤-trans qⱼ′≤b (≤-trans b≤a₀ a₀≤κⱼ′))
        ; a₀≰ = λ a₀≤ → t≰ (≤-trans ∨-upperˡ (≤-trans a₀≤ a∨b≤R))
        ; b₀≰ = b₀≰ ; a₀∧b≰ = a₀∧b≰ ; a∧b₀≰ = a∧b₀≰ })
        where
        a a₀ b R : Fin (suc n)
        a  = p ∨ X
        a₀ = t ∨ X
        b  = (p ₋) ∨ (Y ∨ x j′)
        R  = p ∨ (Y ∨ x j′)

        -- Every q_i, i ≤ j - 1, lies below κ p: by the free star principle, or for i = 0 since p B q₀ fails.
        qᵢ≤κp : ∀ i → i ≤ℕ j′ → x i ≤ κ p
        qᵢ≤κp zero     _     = decidable-stable (x 0 ≤? κ p) λ q₀≰ →
          ¬pBq₀ (B-from-κ iₚ (irr z≤n) (λ e → <ℕ-irrefl (sym (Sub-distinct sub ≤ℕ-refl z≤n e)) (s≤s z≤n))
                   (≤-trans (⋁<-upper q₋ (s≤s z≤n)) X≤κp) q₀≰)
        qᵢ≤κp (suc i) si≤j′ =
          Sub-freeStar′ sub ≤ℕ-refl si≤ (λ e → <ℕ-irrefl (sym e) si<) (λ e → <ℕ-irrefl e (<ℕ-trans si< (n<1+n _)))
                        (λ { (_ , ()) }) (≤-trans (⋁<-upper q₋ (s≤s si≤j′)) X≤κp)
          where
          si< : suc i <ℕ suc (suc j′)
          si< = s≤s (s≤s (<⇒≤ si≤j′))

          si≤ : suc i ≤ℕ suc (suc j′)
          si≤ = <⇒≤ si<

        b≤κp : b ≤ κ p
        b≤κp = ∨-least (₋≤κ p) (∨-least (⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (qᵢ≤κp i (<⇒≤ i<j′))) (qᵢ≤κp j′ ≤ℕ-refl))

        qⱼ′≤b : x j′ ≤ b
        qⱼ′≤b = ≤∨ʳ ∨-upperʳ

        a₀≤κⱼ′ : a₀ ≤ κ (x j′)
        a₀≤κⱼ′ = ∨-least t≤κⱼ′ X≤κⱼ′

        a≤κⱼ′ : a ≤ κ (x j′)
        a≤κⱼ′ = ∨-least (≤-trans (proj₁ p<t) t≤κⱼ′) X≤κⱼ′

        -- a ∨ b ≤ p ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1}, the element of condition (6).
        a∨b≤R : a ∨ b ≤ R
        a∨b≤R = ∨-least (∨-least ∨-upperˡ (≤∨ʳ (∨-mono ≤-refl (₋≤ (x j′))))) (∨-least (≤∨ˡ (₋≤ p)) ∨-upperʳ)

        b₀≰ : ¬ κ p ≤ a ∨ b
        b₀≰ κp≤ = t≰ (≤-trans t≤κp⁺ (≤-trans (∨-least (≤∨ˡ ∨-upperˡ) κp≤) a∨b≤R))

        -- An element above p₋ and above every q_{i*}, i ≤ j - 1, lies below no q_{i*}, i ≤ j - 1.
        above-none : ∀ {m} → p ₋ ≤ m → (∀ i → i ≤ℕ j′ → q₋ i ≤ m) → ∀ i → i ≤ℕ j′ → ¬ m ≤ q₋ i
        above-none p₋≤m _    zero     _      m≤q₀₋  = p₋≰q₀₋ (≤-trans p₋≤m m≤q₀₋)
        above-none _    q≤m  (suc i)  si≤j′  m≤qᵢ₋  =
          B1 (s≤s (<⇒≤ si≤j′)) (≤-trans (q≤m i (<⇒≤ si≤j′)) (≤-trans m≤qᵢ₋ (₋≤ (x (suc i)))))

        -- Such an element below q_{j-1} is q_{j-1}, which is impossible too.
        above-not-qⱼ′ : ∀ {m} → p ₋ ≤ m → (∀ i → i ≤ℕ j′ → q₋ i ≤ m) → m ≤ a → ¬ m ≤ x j′
        above-not-qⱼ′ {m} p₋≤m q≤m m≤a m≤qⱼ′ = decide j′ refl
          where
          m≡qⱼ′ : m ≡ x j′
          m≡qⱼ′ = decidable-stable (m ≟ x j′) λ m≢qⱼ′ → above-none p₋≤m q≤m j′ ≤ℕ-refl (<→≤₋′ m≤qⱼ′ m≢qⱼ′)

          decide : ∀ j″ → j′ ≡ j″ → ⊥
          decide zero      j′≡0  = a≰κ (irr j′≤) (≤-trans (≤-reflexive′ (sym m≡qⱼ′)) (≤-trans m≤a a≤κⱼ′))
          decide (suc j″)  j′≡   = B1 (subst (λ i → suc j″ ≤ℕ suc i) (sym j′≡) (s≤s (<⇒≤ (n<1+n j″))))
                                      (≤-trans (q≤m j″ (subst (j″ ≤ℕ_) (sym j′≡) (<⇒≤ (n<1+n j″))))
                                               (≤-reflexive′ (trans m≡qⱼ′ (cong x j′≡))))

        -- Condition (7): a₀ ∧ b ≰ a, by (W) over the joinands of a.
        a₀∧b≰ : ¬ a₀ ∧ b ≤ a
        a₀∧b≰ h = cases (W a₀ b p X h)
          where
          p₋≤m : p ₋ ≤ a₀ ∧ b
          p₋≤m = ∧-greatest (≤∨ˡ (≤-trans (₋≤ p) (proj₁ p<t))) ∨-upperˡ

          q≤m : ∀ i → i ≤ℕ j′ → q₋ i ≤ a₀ ∧ b
          q≤m i i≤j′ = ∧-greatest (≤∨ʳ (⋁<-upper q₋ (s≤s i≤j′))) (≤∨ʳ (≤-trans (<→≤₋-or i i≤j′) ≤-refl))
            where
            <→≤₋-or : ∀ i → i ≤ℕ j′ → q₋ i ≤ Y ∨ x j′
            <→≤₋-or i i≤j′ = decide (m≤n⇒m<n∨m≡n i≤j′)
              where
              decide : i <ℕ j′ ⊎ i ≡ j′ → q₋ i ≤ Y ∨ x j′
              decide (inj₁ i<j′)  = ≤∨ˡ (⋁<-upper q₋ i<j′)
              decide (inj₂ refl)  = ≤∨ʳ (₋≤ (x i))

          cases : (a₀ ≤ a ⊎ b ≤ a) ⊎ (a₀ ∧ b ≤ p ⊎ a₀ ∧ b ≤ X) → ⊥
          cases (inj₁ (inj₁ a₀≤a))   = t≰ (≤-trans ∨-upperˡ (≤-trans (≤∨ˡ a₀≤a) a∨b≤R))
          cases (inj₁ (inj₂ b≤a))    = a≰κ (irr j′≤) (≤-trans qⱼ′≤b (≤-trans b≤a a≤κⱼ′))
          cases (inj₂ (inj₁ m≤p))    = B1 ≤ℕ-refl (≤-trans (q≤m j′ ≤ℕ-refl)
                                         (≤-trans (subst (a₀ ∧ b ≤_) (a∧κ iₚ) (∧-greatest m≤p (≤-trans ∧-lowerʳ b≤κp)))
                                                  (≤-trans p₋≤qⱼ₋ (₋≤ (x (suc j′))))))
          cases (inj₂ (inj₂ m≤X))    = inner (W-⋁< q₋ (suc j′) {⊥ᴸ} (≤∨ˡ m≤X))
            where
            inner : (a₀ ≤ X ∨ ⊥ᴸ ⊎ b ≤ X ∨ ⊥ᴸ) ⊎ ((Σ ℕ λ i → i <ℕ suc j′ × a₀ ∧ b ≤ q₋ i) ⊎ a₀ ∧ b ≤ ⊥ᴸ) → ⊥
            inner (inj₁ (inj₁ a₀≤))             = cases (inj₁ (inj₁ (≤-trans a₀≤ (∨-least ∨-upperʳ (⊥ᴸ-least a)))))
            inner (inj₁ (inj₂ b≤))              = cases (inj₁ (inj₂ (≤-trans b≤ (∨-least ∨-upperʳ (⊥ᴸ-least a)))))
            inner (inj₂ (inj₁ (i , i<sj′ , m≤)))  = above-none p₋≤m q≤m i (s≤s⁻¹ i<sj′) m≤
            inner (inj₂ (inj₂ m≤⊥))             = p₋≰q₀₋ (≤-trans p₋≤m (≤-trans m≤⊥ (⊥ᴸ-least _)))

        -- Condition (8): a ∧ b₀ ≰ b, by (W) over the joinands of b.
        a∧b₀≰ : ¬ a ∧ κ p ≤ b
        a∧b₀≰ h = cases (W a (κ p) (p ₋) (Y ∨ x j′) h)
          where
          p₋≤m : p ₋ ≤ a ∧ κ p
          p₋≤m = ∧-greatest (≤∨ˡ (₋≤ p)) (₋≤κ p)

          q≤m : ∀ i → i ≤ℕ j′ → q₋ i ≤ a ∧ κ p
          q≤m i i≤j′ = ∧-greatest (≤∨ʳ (⋁<-upper q₋ (s≤s i≤j′))) (≤-trans (⋁<-upper q₋ (s≤s i≤j′)) X≤κp)

          cases : (a ≤ b ⊎ κ p ≤ b) ⊎ (a ∧ κ p ≤ p ₋ ⊎ a ∧ κ p ≤ Y ∨ x j′) → ⊥
          cases (inj₁ (inj₁ a≤b))    = a≰κ iₚ (≤-trans ∨-upperˡ (≤-trans a≤b b≤κp))
          cases (inj₁ (inj₂ κp≤b))   = b₀≰ (≤∨ʳ κp≤b)
          cases (inj₂ (inj₁ m≤p₋))   = B1 ≤ℕ-refl (≤-trans (q≤m j′ ≤ℕ-refl) (≤-trans m≤p₋ (≤-trans p₋≤qⱼ₋ (₋≤ (x (suc j′))))))
          cases (inj₂ (inj₂ m≤Yq))   = inner (W-⋁< q₋ j′ {x j′} m≤Yq)
            where
            inner : (a ≤ Y ∨ x j′ ⊎ κ p ≤ Y ∨ x j′) ⊎ ((Σ ℕ λ i → i <ℕ j′ × a ∧ κ p ≤ q₋ i) ⊎ a ∧ κ p ≤ x j′) → ⊥
            inner (inj₁ (inj₁ a≤))              = cases (inj₁ (inj₁ (≤∨ʳ a≤)))
            inner (inj₁ (inj₂ κp≤))             = cases (inj₁ (inj₂ (≤∨ʳ κp≤)))
            inner (inj₂ (inj₁ (i , i<j′ , m≤)))  = above-none p₋≤m q≤m i (<⇒≤ i<j′) m≤
            inner (inj₂ (inj₂ m≤qⱼ′))           = above-not-qⱼ′ p₋≤m q≤m ∧-lowerˡ m≤qⱼ′
```

#### Lemmas 5.44, 5.45 and 5.46

Each reads Lemma 5.42 contrapositively.  For Lemma 5.44, with `q_k A₁ p`, case 1
gives `p₋ ≤ q₀₋`; were `p₋ = q₀₋`, the sequence has at least two members (else
`p ≤ q_{k*} = p₋`), and case 1 for `q₁, …, q_k, p` gives `q₀₋ = p₋ ≤ q₁₋`,
against (B1).  For Lemma 5.46, with `q_k A₂ p`, `p B q₀` failing and
`q₀ ≰ κ(p)`, also `q₀₋ ≰ κ(p)`, so `q₀₋ ≠ p₋₋`, and `p₋₋ ≰ q₀₋` would be case 2.
Lemma 5.45, for `q_k A₂ p₁ A₂ p₂`, is the book's induction on `k`: the induction
hypothesis gives `p₂₋ < q₁₋`; supposing `p₂₋ ≰ q₀₋`, Lemma 5.36 gives
`p₂ = p₁₋`, case 2 of Lemma 5.42 gives `⋁ᵢ₍ⱼ qᵢ ≤ κ(p₁)`, Lemma 5.43 for
`q₀, …, q_j, p₂` with `t = p₁` gives `⋁ᵢ₍ⱼ qᵢ₋ ≰ κ(p₂)`, and (W) applied to
`p₂ = q_k ∧ κ(p₁) ≤ p₂₋ ∨ ⋁ᵢ₍ⱼ qᵢ₋` fails in every disjunct.  The subsequence
`q₀, …, q_j, p₂` is the family `x ∘ keep-then j (k + 2)` of
[Lattices.Nation.BType][], and Lemma 5.43's hypotheses are stated of `p₂` through
an equation `x′ (j + 1) ≡ p₂` that a `refl` pattern discharges
(`apply-5-43`{.AgdaFunction}).  The induction of Lemma 5.45 reads `q₁, …, q_k`
through `BType-shift`{.AgdaFunction}; so does the second application of Lemma
5.42 in Lemma 5.44.

```agda
    module L542C = L542.InCycle 𝒞

    -- Lemma 5.42 (1), read contrapositively: with q_k A₁ p, p₋ ≤ q₀₋.
    lemma-5-42-1 : ∀ {k x} → Sub (suc k) x → BType k x → x k A₁ x (suc k) → x (suc k) ₋ ≤ x 0 ₋
    lemma-5-42-1 sub bt hA₁ = decidable-stable (_ ≤? _) λ h → lemma-5-42 (case₁ hA₁ h)
      where open L542C.Setting sub bt (proj₁ hA₁)

    -- With q_k A₁ p, p₋ ≠ q₀₋: were they equal, a single member would give p ≤ q₀₋ = p₋,
    -- and more members give q₀₋ = p₋ ≤ q₁₋ by Lemma 5.42 (1) for q₁, …, q_k, p, against (B1).
    lemma-5-44-ne : ∀ k {x} → Sub (suc k) x → BType k x → x k A₁ x (suc k) → x (suc k) ₋ ≢ x 0 ₋
    lemma-5-44-ne zero {x} sub bt hA₁ e =
      proj₂ (proj₂ (A-irr (proj₁ hA₁)))
            (≤-antisym (₋≤ (x 1)) (≤-trans (<→≤₋ (A→< (proj₁ hA₁))) (≤-reflexive′ (sym e))))
    lemma-5-44-ne (suc k′) {x} sub bt hA₁ e =
      BType.B1 bt (s≤s z≤n) (≤-trans (≤-reflexive′ (sym e)) (≤-trans p₋≤q₁₋ (₋≤ (x 1))))
      where
      p₋≤q₁₋ : x (suc (suc k′)) ₋ ≤ x 1 ₋
      p₋≤q₁₋ = lemma-5-42-1 (Sub-restrict sub suc (λ i<j _ → s≤s i<j) (λ i≤ → s≤s i≤))
                             (BType-shift 1 k′ ≤ℕ-refl bt) hA₁

    -- Lemma 5.44: with q_k A₁ p, p₋ < q₀₋.
    lemma-5-44 : ∀ {k x} → Sub (suc k) x → BType k x → x k A₁ x (suc k) → x (suc k) ₋ < x 0 ₋
    lemma-5-44 {k} sub bt hA₁ = lemma-5-42-1 sub bt hA₁ , lemma-5-44-ne k sub bt hA₁

    -- Lemma 5.46: with q_k A₂ p, p B q₀ failing and q₀ ≰ κ(p), p₋₋ < q₀₋.
    lemma-5-46 : ∀ {k x} (sub : Sub (suc k) x) (bt : BType k x) (hA₂ : x k A₂ x (suc k))
               → ¬ (x (suc k) B x 0) → ¬ x 0 ≤ κ (x (suc k)) → (x (suc k) ₋) ₋ < x 0 ₋
    lemma-5-46 {k} {x} sub bt hA₂ ¬pBq₀ q₀≰κp = decidable-stable (_ ≤? _) contra , ne
      where
      module S = L542C.Setting sub bt (proj₁ hA₂)

      p : Fin (suc n)
      p = x (suc k)

      -- q₀₋ ≰ κ(p), else p B q₀ by Lemma 2.58.
      q₀₋≰κp : ¬ x 0 ₋ ≤ κ p
      q₀₋≰κp h = ¬pBq₀ (B-from-κ (Sub-irr sub ≤ℕ-refl) (Sub-irr sub z≤n)
                                 (λ e → 1+n≢0 (Sub-distinct sub ≤ℕ-refl z≤n e)) h q₀≰κp)

      ne : (p ₋) ₋ ≢ x 0 ₋
      ne e = q₀₋≰κp (subst (_≤ κ p) e (≤-trans (₋≤ (p ₋)) (₋≤κ p)))

      -- Were p₋₋ ≰ q₀₋, case (2) of Lemma 5.42 would give ⋁ᵢ₍ⱼ qᵢ ≤ κ(p) with j ≥ 1, against q₀ ≰ κ(p).
      contra : ¬ (p ₋) ₋ ≤ x 0 ₋ → ⊥
      contra h = q₀≰κp (≤-trans (⋁<-upper x 0<j) ⋁<≤κp)
        where
        ⋁<≤κp : ⋁< x S.j ≤ κ p
        ⋁<≤κp = decidable-stable (_ ≤? _) λ h′ → S.lemma-5-42 (S.case₂ hA₂ h h′ ¬pBq₀)

        p₋≤qⱼ₋ : p ₋ ≤ x S.j ₋
        p₋≤qⱼ₋ = subst (_≤ x S.j ₋) (proj₂ hA₂) S.t≤qⱼ₋

        0<j : 0 <ℕ S.j
        0<j = n≢0⇒n>0 λ j≡0 → h (≤-trans (₋≤ (p ₋)) (subst (λ z → p ₋ ≤ x z ₋) j≡0 p₋≤qⱼ₋))

    -- The setting of Lemma 5.45: q₀, …, q_k, p₁, p₂ a subsequence, q₀, …, q_k a B-type sequence,
    -- q_k A₂ p₁ A₂ p₂.
    module Lemma545 {k : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub (suc (suc k)) x) (bt : BType k x)
                    (hA₂₁ : x k A₂ x (suc k)) (hA₂₂ : x (suc k) A₂ x (suc (suc k))) where
      open BType bt

      p₁ p₂ : Fin (suc n)
      p₁ = x (suc k)
      p₂ = x (suc (suc k))

      irr : ∀ {i} → i ≤ℕ suc (suc k) → HasOneLowerCover (x i)
      irr = Sub-irr sub

      iₖ : HasOneLowerCover (x k)
      iₖ = irr (≤ℕ-trans (n≤1+n k) (n≤1+n (suc k)))

      i₁ : HasOneLowerCover p₁
      i₁ = irr (n≤1+n (suc k))

      i₂ : HasOneLowerCover p₂
      i₂ = irr ≤ℕ-refl

      -- Consequences of q_k A p₁ A p₂.
      p₁≤qₖ₋ : p₁ ≤ x k ₋
      p₁≤qₖ₋ = <→≤₋ (A→< (proj₁ hA₂₁))

      p₁≤κqₖ : p₁ ≤ κ (x k)
      p₁≤κqₖ = ≤-trans p₁≤qₖ₋ (₋≤κ (x k))

      qₖ≤p₁∨κp₁ : x k ≤ p₁ ∨ κ p₁
      qₖ≤p₁∨κp₁ = proj₂ (proj₂ (proj₂ (proj₁ hA₂₁)))

      p₂≤p₁ : p₂ ≤ p₁
      p₂≤p₁ = proj₁ (A→< (proj₁ hA₂₂))

      p₂≤κqₖ : p₂ ≤ κ (x k)
      p₂≤κqₖ = ≤-trans p₂≤p₁ p₁≤κqₖ

      -- Lemma 5.36 on q_k, p₁, p₂: p₂ = p₁₋.
      p₂≡p₁₋ : p₂ ≡ p₁ ₋
      p₂≡p₁₋ = proj₁ (lemma-5-36 (Sub-restrict sub (_+ k) (λ i<j _ → +-monoˡ-< k i<j) (+-monoˡ-≤ k))
                                  hA₂₁ (proj₁ hA₂₂))

      p₂≤κp₁ : p₂ ≤ κ p₁
      p₂≤κp₁ = subst (_≤ κ p₁) (sym p₂≡p₁₋) (₋≤κ p₁)

      -- q₀, …, q_k, p₁ in the setting of Lemma 5.42, whose t = q_k ∧ κ(p₁) is p₂.
      subₚ : Sub (suc k) x
      subₚ = Sub-prefix sub (n≤1+n (suc k))

      module S = L542C.Setting subₚ bt (proj₁ hA₂₁)

      t≡p₂ : S.t ≡ p₂
      t≡p₂ = trans (proj₂ hA₂₁) (sym p₂≡p₁₋)

      p₂≤qⱼ₋ : p₂ ≤ x S.j ₋
      p₂≤qⱼ₋ = subst (_≤ x S.j ₋) t≡p₂ S.t≤qⱼ₋

      p₂-least : ∀ i → i <ℕ S.j → ¬ p₂ ≤ x i ₋
      p₂-least i i<j = subst (λ z → ¬ z ≤ x i ₋) t≡p₂ (S.j-least i i<j)

      -- p₁ B q₀ fails, by the free star principle.
      ¬p₁Bq₀ : ¬ (p₁ B x 0)
      ¬p₁Bq₀ = Sub-freeStar sub (n≤1+n (suc k)) z≤n (λ ()) λ { (e , _) → <ℕ-irrefl e (n<1+n (suc k)) }

      -- Lemma 5.42 (2) for q₀, …, q_k, p₁, read contrapositively.
      ⋁<≤κp₁ : ¬ p₂ ₋ ≤ x 0 ₋ → ⋁< x S.j ≤ κ p₁
      ⋁<≤κp₁ h = decidable-stable (_ ≤? _) λ h′ →
        S.lemma-5-42 (S.case₂ hA₂₁ (subst (λ z → ¬ z ₋ ≤ x 0 ₋) p₂≡p₁₋ h) h′ ¬p₁Bq₀)

      -- The main case: p₂₋ ≰ q₀₋ and j = suc j′ ≥ 1, the least index with p₂ ≤ q_{j*}.
      module Main (h : ¬ p₂ ₋ ≤ x 0 ₋) (j′ : ℕ) (sj≤k : suc j′ ≤ℕ k) (p₂≤qⱼ₋ : p₂ ≤ x (suc j′) ₋)
                  (least : ∀ i → i <ℕ suc j′ → ¬ p₂ ≤ x i ₋) (⋁<≤ : ⋁< x (suc j′) ≤ κ p₁) where

        0<k : 0 <ℕ k
        0<k = ≤ℕ-trans (s≤s z≤n) sj≤k

        -- p₂ B q₀ fails: (W) on q_k ∧ κ(p₁) = p₂ ≤ p₂₋ ∨ q₀ fails in every disjunct.
        ¬p₂Bq₀ : ¬ (p₂ B x 0)
        ¬p₂Bq₀ p₂Bq₀ =
          cases (W (x k) (κ p₁) (p₂ ₋) (x 0) (subst (_≤ (p₂ ₋) ∨ x 0) (sym t≡p₂) (proj₁ (proj₂ (proj₂ (proj₂ p₂Bq₀))))))
          where
          p₂≢q₀ : p₂ ≢ x 0
          p₂≢q₀ = proj₁ (proj₂ (proj₂ p₂Bq₀))

          -- p₂₋ ∨ q₀ ≤ κ(q_k): p₂₋ ≤ p₁ ≤ q_{k*}, and q₀ ≤ κ(q_k) by (B2).
          rhs≤κqₖ : (p₂ ₋) ∨ x 0 ≤ κ (x k)
          rhs≤κqₖ = ∨-least (≤-trans (₋≤ p₂) p₂≤κqₖ) (B2 0<k ≤ℕ-refl)

          cases : (x k ≤ (p₂ ₋) ∨ x 0 ⊎ κ p₁ ≤ (p₂ ₋) ∨ x 0) ⊎ (x k ∧ κ p₁ ≤ p₂ ₋ ⊎ x k ∧ κ p₁ ≤ x 0) → ⊥
          cases (inj₁ (inj₁ qₖ≤))    = a≰κ iₖ (≤-trans qₖ≤ rhs≤κqₖ)
          cases (inj₁ (inj₂ κp₁≤))   = a≰κ iₖ (≤-trans qₖ≤p₁∨κp₁ (∨-least p₁≤κqₖ (≤-trans κp₁≤ rhs≤κqₖ)))
          cases (inj₂ (inj₁ m≤p₂₋))  = proj₂ i₂ (≤-antisym (₋≤ p₂) (subst (_≤ p₂ ₋) t≡p₂ m≤p₂₋))
          cases (inj₂ (inj₂ m≤q₀))   = h (≤-trans (₋≤ p₂) (<→≤₋′ (subst (_≤ x 0) t≡p₂ m≤q₀) p₂≢q₀))

        -- The subsequence q₀, …, q_j, p₂, read at the indices up to j + 1.
        m : ℕ
        m = suc (suc k)

        reindex : ℕ → ℕ
        reindex = keep-then (suc j′) m

        x′ : ℕ → Fin (suc n)
        x′ i = x (reindex i)

        sj≤m : suc j′ ≤ℕ m
        sj≤m = ≤ℕ-trans sj≤k (≤ℕ-trans (n≤1+n k) (n≤1+n (suc k)))

        sub′ : Sub (suc (suc j′)) x′
        sub′ = Sub-restrict sub reindex (keep-then-mono (s≤s (≤ℕ-trans sj≤k (n≤1+n k)))) (keep-then-bound sj≤m ≤ℕ-refl)

        bt′ : BType (suc j′) x′
        bt′ = BType-cong sj≤k (λ i i≤sj′ → cong x (keep-then-≤ i≤sj′)) bt

        x′ⱼ₊₁≡p₂ : x′ (suc (suc j′)) ≡ p₂
        x′ⱼ₊₁≡p₂ = cong x (keep-then-> (n<1+n (suc j′)))

        x′ⱼ≡ : x′ (suc j′) ≡ x (suc j′)
        x′ⱼ≡ = cong x (keep-then-≤ ≤ℕ-refl)

        x′ⱼ′≡ : x′ j′ ≡ x j′
        x′ⱼ′≡ = cong x (keep-then-≤ (n≤1+n j′))

        x′ᵢ≡ : ∀ {i} → i <ℕ suc (suc j′) → x′ i ≡ x i
        x′ᵢ≡ i<ssj′ = cong x (keep-then-≤ (s≤s⁻¹ i<ssj′))

        X′ Y′ : Fin (suc n)
        X′ = ⋁< (λ i → x′ i ₋) (suc j′)
        Y′ = ⋁< (λ i → x′ i ₋) j′

        -- Lemma 5.43 for q₀, …, q_j, p₂ with t = p₁, its hypotheses stated of p₂.
        apply-5-43 : ∀ p → x′ (suc (suc j′)) ≡ p
                   → ¬ p ₋ ≤ x′ 0 ₋ → p ₋ ≤ x′ (suc j′) ₋ → p < p₁ → p₁ ≤ p ∨ κ p → p₁ ≤ κ (x′ j′)
                   → ¬ p₁ ≤ p ∨ (Y′ ∨ x′ j′) → ¬ (p B x′ 0) → ¬ X′ ≤ κ p
        apply-5-43 _ refl = Lemma543.lemma-5-43 sub′ bt′ p₁

        -- 5.43 (5): p₁₋ = p₂ ≤ q_{j*} ≤ κ(q_{j-1}) by (B3), and the free star principle lifts it to p₁.
        p₁≤κqⱼ′ : p₁ ≤ κ (x j′)
        p₁≤κqⱼ′ = Sub-freeStar′ sub (≤ℕ-trans (n≤1+n j′) sj≤m) (n≤1+n (suc k))
                                 (λ e → <ℕ-irrefl e (≤ℕ-trans sj≤k (n≤1+n k)))
                                 (λ e → <ℕ-irrefl (sym e) (s≤s sj≤k)) (λ { (_ , ()) })
                                 (subst (_≤ κ (x j′)) p₂≡p₁₋ (≤-trans p₂≤qⱼ₋ (B3 sj≤k)))

        -- 5.43 (6): p₂ ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1} ≤ κ(p₁), while p₁ ≰ κ(p₁).
        p₁≰ : ¬ p₁ ≤ p₂ ∨ (Y′ ∨ x′ j′)
        p₁≰ le = a≰κ i₁ (≤-trans le (∨-least p₂≤κp₁ (∨-least Y′≤κp₁ x′ⱼ′≤κp₁)))
          where
          xᵢ≤κp₁ : ∀ {i} → i <ℕ suc j′ → x i ≤ κ p₁
          xᵢ≤κp₁ i<sj′ = ≤-trans (⋁<-upper x i<sj′) ⋁<≤

          Y′≤κp₁ : Y′ ≤ κ p₁
          Y′≤κp₁ = ⋁<-least (λ i → x′ i ₋) λ i i<j′ →
            ≤-trans (₋≤ (x′ i)) (subst (_≤ κ p₁) (sym (x′ᵢ≡ (<ℕ-trans i<j′ (<ℕ-trans (n<1+n j′) (n<1+n (suc j′))))))
                                        (xᵢ≤κp₁ (<ℕ-trans i<j′ (n<1+n j′))))

          x′ⱼ′≤κp₁ : x′ j′ ≤ κ p₁
          x′ⱼ′≤κp₁ = subst (_≤ κ p₁) (sym x′ⱼ′≡) (xᵢ≤κp₁ (n<1+n j′))

        X′≰κp₂ : ¬ X′ ≤ κ p₂
        X′≰κp₂ = apply-5-43 p₂ x′ⱼ₊₁≡p₂ h (subst (λ z → p₂ ₋ ≤ z ₋) (sym x′ⱼ≡) (≤-trans (₋≤ p₂) p₂≤qⱼ₋))
                            (A→< (proj₁ hA₂₂)) (proj₂ (proj₂ (proj₂ (proj₁ hA₂₂))))
                            (subst (λ z → p₁ ≤ κ z) (sym x′ⱼ′≡) p₁≤κqⱼ′) p₁≰ ¬p₂Bq₀

        -- ⋁ᵢ₍ⱼ qᵢ₋ ≤ κ(q_k), by (B2).
        X′≤κqₖ : X′ ≤ κ (x k)
        X′≤κqₖ = ⋁<-least (λ i → x′ i ₋) λ i i<sj′ →
          ≤-trans (₋≤ (x′ i)) (subst (_≤ κ (x k)) (sym (x′ᵢ≡ (<ℕ-trans i<sj′ (n<1+n (suc j′)))))
                                      (B2 (<ℕ-≤-trans i<sj′ sj≤k) ≤ℕ-refl))

        -- By Lemma 2.57, p₂ ≤ p₂₋ ∨ ⋁ᵢ₍ⱼ qᵢ₋; (W) on q_k ∧ κ(p₁) ≤ ⋁ᵢ₍ⱼ qᵢ₋ ∨ p₂₋ fails in every disjunct.
        final : ⊥
        final = cases (W-⋁< (λ i → x′ i ₋) (suc j′) (subst (_≤ X′ ∨ (p₂ ₋)) (sym t≡p₂) p₂≤))
          where
          p₂≤ : p₂ ≤ X′ ∨ (p₂ ₋)
          p₂≤ = ≤-trans (≰κ→ i₂ X′≰κp₂) (≤-reflexive′ ∨-comm-law)

          rhs≤κqₖ : X′ ∨ (p₂ ₋) ≤ κ (x k)
          rhs≤κqₖ = ∨-least X′≤κqₖ (≤-trans (₋≤ p₂) p₂≤κqₖ)

          cases : (x k ≤ X′ ∨ (p₂ ₋) ⊎ κ p₁ ≤ X′ ∨ (p₂ ₋))
                ⊎ ((Σ ℕ λ i → i <ℕ suc j′ × x k ∧ κ p₁ ≤ x′ i ₋) ⊎ x k ∧ κ p₁ ≤ p₂ ₋) → ⊥
          cases (inj₁ (inj₁ qₖ≤))              = a≰κ iₖ (≤-trans qₖ≤ rhs≤κqₖ)
          cases (inj₁ (inj₂ κp₁≤))             = a≰κ iₖ (≤-trans qₖ≤p₁∨κp₁ (∨-least p₁≤κqₖ (≤-trans κp₁≤ rhs≤κqₖ)))
          cases (inj₂ (inj₁ (i , i<sj′ , m≤))) =
            least i i<sj′ (subst (_≤ x i ₋) t≡p₂ (subst (λ z → x k ∧ κ p₁ ≤ z ₋) (x′ᵢ≡ (<ℕ-trans i<sj′ (n<1+n (suc j′)))) m≤))
          cases (inj₂ (inj₂ m≤p₂₋))            = proj₂ i₂ (≤-antisym (₋≤ p₂) (subst (_≤ p₂ ₋) t≡p₂ m≤p₂₋))

      -- The contradiction from p₂₋ ≰ q₀₋: at j = 0, p₂₋ ≤ p₂ ≤ q₀₋ directly.
      contradiction : ¬ p₂ ₋ ≤ x 0 ₋ → ⊥
      contradiction h = go S.j S.j≤k p₂≤qⱼ₋ p₂-least (⋁<≤κp₁ h)
        where
        go : ∀ j → j ≤ℕ k → p₂ ≤ x j ₋ → (∀ i → i <ℕ j → ¬ p₂ ≤ x i ₋) → ⋁< x j ≤ κ p₁ → ⊥
        go zero     _    p₂≤q₀₋ _     _   = h (≤-trans (₋≤ p₂) p₂≤q₀₋)
        go (suc j′) sj≤k p₂≤qⱼ₋ least ⋁<≤ = Main.final h j′ sj≤k p₂≤qⱼ₋ least ⋁<≤

    -- Lemma 5.45: with q_k A₂ p₁ A₂ p₂, p₂₋ < q₀₋.  The inequality is the contradiction above; the
    -- difference is direct for k = 0, and for k > 0 the induction hypothesis gives p₂₋ < q₁₋, so that
    -- p₂₋ = q₀₋ would put q₀₋ below q₁, against (B1).
    lemma-5-45 : ∀ k {x} (sub : Sub (suc (suc k)) x) (bt : BType k x)
               → x k A₂ x (suc k) → x (suc k) A₂ x (suc (suc k)) → x (suc (suc k)) ₋ < x 0 ₋
    lemma-5-45 zero {x} sub bt hA₂₁ hA₂₂ = decidable-stable (_ ≤? _) (Lemma545.contradiction sub bt hA₂₁ hA₂₂) , ne
      where
      p₂≤q₀₋ : x 2 ≤ x 0 ₋
      p₂≤q₀₋ = ≤-trans (<→≤₋ (A→< (proj₁ hA₂₂))) (≤-trans (₋≤ (x 1)) (<→≤₋ (A→< (proj₁ hA₂₁))))

      ne : x 2 ₋ ≢ x 0 ₋
      ne e = proj₂ (Sub-irr sub ≤ℕ-refl) (≤-antisym (₋≤ (x 2)) (≤-trans p₂≤q₀₋ (≤-reflexive′ (sym e))))
    lemma-5-45 (suc k′) {x} sub bt hA₂₁ hA₂₂ = decidable-stable (_ ≤? _) (Lemma545.contradiction sub bt hA₂₁ hA₂₂) , ne
      where
      ih : x (suc (suc (suc k′))) ₋ < x 1 ₋
      ih = lemma-5-45 k′ (Sub-restrict sub suc (λ i<j _ → s≤s i<j) (λ i≤ → s≤s i≤))
                      (BType-shift 1 k′ ≤ℕ-refl bt) hA₂₁ hA₂₂

      ne : x (suc (suc (suc k′))) ₋ ≢ x 0 ₋
      ne e = BType.B1 bt (s≤s z≤n) (≤-trans (≤-reflexive′ (sym e)) (≤-trans (proj₁ ih) (₋≤ (x 1))))
```
