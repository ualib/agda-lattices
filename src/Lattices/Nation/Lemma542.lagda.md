---
layout: default
file: "src/Lattices/Nation/Lemma542.lagda.md"
title: "Lattices.Nation.Lemma542 module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Lemma 5.42: a B-type sequence followed by an A, in three cases

This is the [Lattices.Nation.Lemma542][] module of the [agda-lattices][] library.

Lemma 5.42 of [Freese, Ježek, and Nation (1995)][] (pp. 114 to 115) is the
first of the lemmas that put restrictions on the subsequences of a minimal
C-cycle in an S-lattice, and the one the next six rest on.  Let
`q₀, …, q_k, p` be a subsequence with `q₀, …, q_k` a B-type sequence and
`q_k A p`, and let `j` be the least index with `q_k ∧ κ(p) ≤ q_{j*}`.  Then none
of the following takes place:

1.  `q_k A₁ p` and `p₋ ≰ q₀₋`;
2.  `q_k A₂ p`, `p₋₋ ≰ q₀₋`, `⋁ᵢ₍ⱼ qᵢ ≰ κ(p)`, and `p B q₀` fails;
3.  `q_k A₂ p`, `p₋ ≰ q₀₋`, `q₀ ≤ κ(p)`, and `⋁ᵢ₍ⱼ qᵢ ≰ κ(p)`.

The proof builds, from each case, the configuration of Lemma 5.38, with
`t = q_k ∧ κ(p)`, `r` one of `p₋`, `p₋₋` and `0` by the case, `a = p ∨ t`,
`b = r ∨ ⋁ᵢ₍ⱼ qᵢ₋`, `b₀ = r ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1}`, and `a₀, a₁` either
`q_k, q_{k*}` (when `j = k`) or a minimal element of the interval `[a, q_{k*}]`
not below `κ(q_{j-1})` and its lower cover in the interval (when `j < k`).  The
seven conditions are verified one by one as the book does, with the n-ary (W)
of [Lattices.Nation.BType][] where the book applies (W) to a join of several
elements, and the exclusion of the configuration
([Lattices.Nation.Configurations][]) ends the proof.  Two steps the book leaves
to the reader are made explicit: `t ≤ q_{j-1}` with `t ≰ q_{j-1*}` forces
`t = q_{j-1}`, which the book states, and `a` is join reducible in case 1
because `p` and `t` are incomparable, so that `a` is neither.

The three cases are a datatype, so that the lemma is one function to `⊥`;
later lemmas apply it by supplying a case, and read its contrapositive as the
book does ("by Lemma 5.42 (1), `p₋ ≤ q₀₋`").

The module checks in 0.9 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Lemma542 where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; ≤∧≢⇒< )
                                                   renaming ( _≟_ to _≟ℕ_ ; ≤-refl to ≤ℕ-refl ; ≤-trans to ≤ℕ-trans
                                                            ; <-trans to <ℕ-trans ; <-≤-trans to <ℕ-≤-trans
                                                            ; <-irrefl to <ℕ-irrefl )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; ¬? ; _×-dec_ ; decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType as BTypeModule
open import Lattices.Nation.Configurations  using ( module Configurations )
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```
-->

#### The setting

```agda
module Lemma542 {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least ; ⋁<-escape ; least-index ; minimal-with ; W-⋁< ; irr-∨ ; irr-⋁<
                ; module LowerCoverAbove )
  open Configurations laws w using ( no-config₃₈ )

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞
    open BT.InCycle 𝒞

    -- q 0, …, q k, p: a subsequence read at the indices up to suc k, q 0, …, q k a B-type sequence, q k A p.
    module Setting {k : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub (suc k) x) (bt : BType k x) (qₖAp : x k A x (suc k)) where
      open BType bt

      p t : Fin (suc n)
      p = x (suc k)
      t = x k ∧ κ p

      -- The lower covers of the sequence.
      q₋ : ℕ → Fin (suc n)
      q₋ i = x i ₋

      -- Join irreducibility of the members and of their lower covers.
      irr : ∀ {i} → i ≤ℕ suc k → HasOneLowerCover (x i)
      irr = Sub-irr sub

      ₋irr : ∀ {i} → i ≤ℕ suc k → HasOneLowerCover (x i ₋)
      ₋irr = Sub-₋irr 𝒞 sub

      k≤sk : k ≤ℕ suc k
      k≤sk = <⇒≤ (n<1+n k)

      iₖ : HasOneLowerCover (x k)
      iₖ = irr k≤sk

      iₚ : HasOneLowerCover p
      iₚ = irr ≤ℕ-refl

      -- Consequences of q k A p.
      p<qₖ : p < x k
      p<qₖ = A→< qₖAp

      qₖ≰κp : ¬ x k ≤ κ p
      qₖ≰κp = A→≰κ qₖAp

      qₖ≤p∨κp : x k ≤ p ∨ κ p
      qₖ≤p∨κp = proj₂ (proj₂ (proj₂ qₖAp))

      p≤qₖ₋ : p ≤ x k ₋
      p≤qₖ₋ = <→≤₋ p<qₖ

      p₋≤t : p ₋ ≤ t
      p₋≤t = ∧-greatest (≤-trans (₋≤ p) (proj₁ p<qₖ)) (₋≤κ p)

      t≤qₖ₋ : t ≤ x k ₋
      t≤qₖ₋ = <→≤₋′ ∧-lowerˡ λ t≡qₖ → qₖ≰κp (subst (_≤ κ p) t≡qₖ ∧-lowerʳ)

      -- The least index j with t ≤ q j ₋.
      private
        jdata : Σ ℕ λ j → j ≤ℕ k × t ≤ q₋ j × (∀ i → i <ℕ j → ¬ t ≤ q₋ i)
        jdata = least-index (λ i → t ≤? q₋ i) k t≤qₖ₋

      j : ℕ
      j = proj₁ jdata

      j≤k : j ≤ℕ k
      j≤k = proj₁ (proj₂ jdata)

      t≤qⱼ₋ : t ≤ q₋ j
      t≤qⱼ₋ = proj₁ (proj₂ (proj₂ jdata))

      j-least : ∀ i → i <ℕ j → ¬ t ≤ q₋ i
      j-least = proj₂ (proj₂ (proj₂ jdata))

      -- The three cases of the lemma.
      data Case : Type where
        case₁ : x k A₁ p → ¬ p ₋ ≤ q₋ 0 → Case
        case₂ : x k A₂ p → ¬ (p ₋) ₋ ≤ q₋ 0 → ¬ ⋁< x j ≤ κ p → ¬ (p B x 0) → Case
        case₃ : x k A₂ p → ¬ p ₋ ≤ q₋ 0 → x 0 ≤ κ p → ¬ ⋁< x j ≤ κ p → Case

      -- The element r of the proof: p₋, p₋₋, or the least element.
      r : Case → Fin (suc n)
      r (case₁ _ _)      = p ₋
      r (case₂ _ _ _ _)  = (p ₋) ₋
      r (case₃ _ _ _ _)  = ⊥ᴸ

      -- In every case p₋ ≰ q₀₋, so t ≰ q₀₋ and j ≥ 1.
      p₋≰q₀₋ : Case → ¬ p ₋ ≤ q₋ 0
      p₋≰q₀₋ (case₁ _ h)      = h
      p₋≰q₀₋ (case₂ _ h _ _)  = λ p₋≤ → h (≤-trans (₋≤ (p ₋)) p₋≤)
      p₋≰q₀₋ (case₃ _ h _ _)  = h

      t≰q₀₋ : Case → ¬ t ≤ q₋ 0
      t≰q₀₋ c t≤ = p₋≰q₀₋ c (≤-trans p₋≤t t≤)

      -- r ≤ t, and t ≰ r.
      r≤t : (c : Case) → r c ≤ t
      r≤t (case₁ _ _)             = p₋≤t
      r≤t (case₂ (_ , e) _ _ _)   = ≤-trans (₋≤ (p ₋)) (≤-reflexive′ (sym e))
      r≤t (case₃ _ _ _ _)         = ⊥ᴸ-least t

      t≰r : (c : Case) → ¬ t ≤ r c
      t≰r (case₁ (_ , p₋<t) _)      t≤r = proj₂ p₋<t (≤-antisym (proj₁ p₋<t) t≤r)
      t≰r (case₂ (_ , e) _ _ _)     t≤r = proj₂ (₋irr ≤ℕ-refl) (≤-antisym (₋≤ (p ₋)) (subst (_≤ (p ₋) ₋) e t≤r))
      t≰r (case₃ (_ , e) _ _ _)     t≤r = proj₂ (₋irr ≤ℕ-refl) (≤-antisym (₋≤ (p ₋)) (≤-trans (subst (_≤ ⊥ᴸ) e t≤r) (⊥ᴸ-least _)))

      -- In cases 1 and 2, r ≰ q₀₋; in case 3, q₀ ≤ κ p and ⋁ᵢ₍ⱼ qᵢ ≰ κ p.
      r-fact : (c : Case) → ¬ r c ≤ q₋ 0 ⊎ (x 0 ≤ κ p × ¬ ⋁< x j ≤ κ p)
      r-fact (case₁ _ h)            = inj₁ h
      r-fact (case₂ _ h _ _)        = inj₁ h
      r-fact (case₃ _ _ q₀≤κp ⋁≰)   = inj₂ (q₀≤κp , ⋁≰)
```

The lemma proper, with `j = suc j′` since `j ≥ 1`.  The facts about `a₀` and
`a₁` that the seven conditions use are collected in `Above`{.AgdaRecord}: `a`
lies below `a₁`, `a₁` is a lower cover of `a₀`, `a₀` lies below `q_k`, `a₁` lies
below `q_{k*}` and below `κ(q_{j-1})`, and either `a₀ = q_k` or `j < k` and
`a₀ ≰ κ(q_{j-1})`.

```agda
      module Main (c : Case) (j′ : ℕ) (j≡ : j ≡ suc j′) where

        sj′≤k : suc j′ ≤ℕ k
        sj′≤k = subst (_≤ℕ k) j≡ j≤k

        j′<sk : j′ <ℕ suc k
        j′<sk = <ℕ-≤-trans (n<1+n j′) (≤ℕ-trans sj′≤k k≤sk)

        t≤qⱼ′₊₁₋ : t ≤ q₋ (suc j′)
        t≤qⱼ′₊₁₋ = subst (λ i → t ≤ q₋ i) j≡ t≤qⱼ₋

        t≰qᵢ₋ : ∀ i → i ≤ℕ j′ → ¬ t ≤ q₋ i
        t≰qᵢ₋ i i≤j′ = j-least i (subst (i <ℕ_) (sym j≡) (s≤s i≤j′))

        -- The elements of the configuration.
        a b b₀ X Y : Fin (suc n)
        a  = p ∨ t
        Y  = ⋁< q₋ j′
        X  = ⋁< q₋ (suc j′)
        b  = r c ∨ X
        b₀ = r c ∨ (Y ∨ x j′)

        r≤a : r c ≤ a
        r≤a = ≤∨ʳ (r≤t c)

        -- Lemma 2.57 for p, read on t ≤ q_{j*} ≤ κ(q_{j-1}): p ≤ κ(q_{j-1}) by the free star principle.
        qⱼ′₊₁₋≤κⱼ′ : q₋ (suc j′) ≤ κ (x j′)
        qⱼ′₊₁₋≤κⱼ′ = B3 sj′≤k

        p≤κⱼ′ : suc j′ <ℕ k → p ≤ κ (x j′)
        p≤κⱼ′ sj′<k = Sub-freeStar′ sub (<⇒≤ j′<sk) ≤ℕ-refl (λ j′≡sk → <ℕ-irrefl j′≡sk j′<sk)
                        (λ sk≡sj′ → <ℕ-irrefl (sym sk≡sj′) (<ℕ-trans sj′<k (n<1+n k)))
                        (λ { (_ , ()) })
                        (≤-trans p₋≤t (≤-trans t≤qⱼ′₊₁₋ qⱼ′₊₁₋≤κⱼ′))

        a≤κⱼ′ : suc j′ <ℕ k → a ≤ κ (x j′)
        a≤κⱼ′ sj′<k = ∨-least (p≤κⱼ′ sj′<k) (≤-trans t≤qⱼ′₊₁₋ qⱼ′₊₁₋≤κⱼ′)

        a≤qₖ₋ : a ≤ x k ₋
        a≤qₖ₋ = ∨-least p≤qₖ₋ t≤qₖ₋

        -- a₀ and a₁, with the facts the conditions use.
        record Above : Type where
          field
            a₀ a₁    : Fin (suc n)
            a≤a₁     : a ≤ a₁
            a₁⋖a₀    : a₁ ⋖ a₀
            a₀≤qₖ    : a₀ ≤ x k
            a₁≤qₖ₋   : a₁ ≤ x k ₋
            a₁≤κⱼ′   : a₁ ≤ κ (x j′)
            which    : a₀ ≡ x k ⊎ (suc j′ <ℕ k × ¬ a₀ ≤ κ (x j′))

        above : Above
        above = decide (suc j′ ≟ℕ k)
          where
          decide : Dec (suc j′ ≡ k) → Above
          decide (yes sj′≡k) = record
            { a₀ = x k ; a₁ = x k ₋ ; a≤a₁ = a≤qₖ₋ ; a₁⋖a₀ = ₋⋖ iₖ ; a₀≤qₖ = ≤-refl ; a₁≤qₖ₋ = ≤-refl
            ; a₁≤κⱼ′ = subst (λ i → q₋ i ≤ κ (x j′)) sj′≡k qⱼ′₊₁₋≤κⱼ′ ; which = inj₁ refl }
          decide (no sj′≢k) = record
            { a₀ = a₀ ; a₁ = between ; a≤a₁ = a≤between ; a₁⋖a₀ = between⋖ a₁≢a₀
            ; a₀≤qₖ = ≤-trans a₀≤qₖ₋ (₋≤ (x k)) ; a₁≤qₖ₋ = ≤-trans (proj₁ (proj₁ (between⋖ a₁≢a₀))) a₀≤qₖ₋
            ; a₁≤κⱼ′ = a₁≤κ ; which = inj₂ (sj′<k , a₀≰κ) }
            where
            sj′<k : suc j′ <ℕ k
            sj′<k = ≤∧≢⇒< sj′≤k sj′≢k

            -- A minimal element of [a, q_{k*}] not below κ(q_{j-1}); q_{k*} is one by (B4).
            P? : ∀ y → Dec (a ≤ y × ¬ y ≤ κ (x j′))
            P? y = a ≤? y ×-dec ¬? (y ≤? κ (x j′))

            m : Σ (Fin (suc n)) λ m → m ≤ x k ₋ × (a ≤ m × ¬ m ≤ κ (x j′)) × (∀ y → y < m → ¬ (a ≤ y × ¬ y ≤ κ (x j′)))
            m = minimal-with P? (x k ₋) (a≤qₖ₋ , B4 sj′<k ≤ℕ-refl)

            a₀ : Fin (suc n)
            a₀ = proj₁ m

            a₀≤qₖ₋ : a₀ ≤ x k ₋
            a₀≤qₖ₋ = proj₁ (proj₂ m)

            a₀≰κ : ¬ a₀ ≤ κ (x j′)
            a₀≰κ = proj₂ (proj₁ (proj₂ (proj₂ m)))

            a<a₀ : a < a₀
            a<a₀ = proj₁ (proj₁ (proj₂ (proj₂ m))) , λ a≡a₀ → a₀≰κ (subst (_≤ κ (x j′)) a≡a₀ (a≤κⱼ′ sj′<k))

            open LowerCoverAbove a a₀ a<a₀

            a₁≤κ : between ≤ κ (x j′)
            a₁≤κ = between≤ λ y a≤y y<a₀ → decidable-stable (y ≤? κ (x j′)) λ y≰κ → proj₂ (proj₂ (proj₂ m)) y y<a₀ (a≤y , y≰κ)

            a₁≢a₀ : between ≢ a₀
            a₁≢a₀ e = a₀≰κ (subst (_≤ κ (x j′)) e a₁≤κ)

        open Above above

        -- b₀ ≤ κ(q_k): its joinands are r ≤ q_{k*}, the q_{i*} and q_{j-1}, all below κ(q_k) by (B2).
        b₀≤κₖ : b₀ ≤ κ (x k)
        b₀≤κₖ = ∨-least (≤-trans (r≤t c) (≤-trans t≤qₖ₋ (₋≤κ (x k))))
                        (∨-least (⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (B2 (<ℕ-trans i<j′ j′<k) ≤ℕ-refl))
                                 (B2 j′<k ≤ℕ-refl))
          where
          j′<k : j′ <ℕ k
          j′<k = <ℕ-≤-trans (n<1+n j′) sj′≤k

        -- X ≤ κ(q_{j-1}): the q_{i*} for i < j - 1 by (B2), and q_{j-1*} ≤ κ(q_{j-1}).
        X≤κⱼ′ : X ≤ κ (x j′)
        X≤κⱼ′ = ∨-least (⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (B2 i<j′ (<⇒≤ (<ℕ-≤-trans (n<1+n j′) sj′≤k))))
                        (₋≤κ (x j′))

        -- In cases 2 and 3 some q_i with i < j is not below κ p, hence neither is q_{i*}: for i ≥ 1 by the
        -- free star principle, for i = 0 because p B q₀ fails.  So X ≰ κ p.
        X≰κp : ¬ ⋁< x j ≤ κ p → ¬ (p B x 0) → ¬ X ≤ κ p
        X≰κp ⋁≰ ¬pBq₀ X≤κp = from (⋁<-escape x j ⋁≰)
          where
          from : Σ ℕ (λ i → i <ℕ j × ¬ x i ≤ κ p) → ⊥
          from (i , i<j , qᵢ≰κp) = ¬pBqᵢ (B-from-κ iₚ (irr i≤sk) p≢qᵢ (≤-trans (⋁<-upper q₋ i<sj′) X≤κp) qᵢ≰κp)
            where
            i<sj′ : i <ℕ suc j′
            i<sj′ = subst (i <ℕ_) j≡ i<j

            i<sk : i <ℕ suc k
            i<sk = <ℕ-≤-trans (<ℕ-≤-trans i<sj′ sj′≤k) k≤sk

            i≤sk : i ≤ℕ suc k
            i≤sk = <⇒≤ i<sk

            p≢qᵢ : p ≢ x i
            p≢qᵢ e = <ℕ-irrefl (sym (Sub-distinct sub ≤ℕ-refl i≤sk e)) i<sk

            ¬pBqᵢ : ¬ (p B x i)
            ¬pBqᵢ = split i i<sk
              where
              split : ∀ i → i <ℕ suc k → ¬ (p B x i)
              split zero     _     = ¬pBq₀
              split (suc i′) si<sk = Sub-freeStar sub ≤ℕ-refl (<⇒≤ si<sk)
                                       (λ si≡ssk → <ℕ-irrefl si≡ssk (<ℕ-trans si<sk (n<1+n (suc k)))) λ { (_ , ()) }

        -- In cases 2 and 3, t = p₋ and a = p.
        a≡p : x k A₂ p → a ≡ p
        a≡p (_ , e) = trans (cong (p ∨_) e) (∨-absorbʳ (₋≤ p))

        -- Condition (1) on a: join reducible in case 1, a ≤ a₋ ∨ b in cases 2 and 3.
        a-cond : ¬ HasOneLowerCover a ⊎ (HasOneLowerCover a × a ≤ (a ₋) ∨ b)
        a-cond = from c
          where
          -- p and t are incomparable in case 1, so a is neither.
          join-reducible : x k A₁ p → ¬ HasOneLowerCover a
          join-reducible (_ , p₋<t) one = cases (irr-∨ one refl)
            where
            cases : a ≡ p ⊎ a ≡ t → ⊥
            cases (inj₁ a≡p′)  = proj₂ p₋<t (≤-antisym (proj₁ p₋<t)
                                   (subst (t ≤_) (a∧κ iₚ) (∧-greatest (subst (t ≤_) a≡p′ ∨-upperʳ) ∧-lowerʳ)))
            cases (inj₂ a≡t)   = a≰κ iₚ (≤-trans (subst (p ≤_) a≡t ∨-upperˡ) ∧-lowerʳ)

          irr-below : (hA₂ : x k A₂ p) → ¬ X ≤ κ p → HasOneLowerCover a × a ≤ (a ₋) ∨ b
          irr-below hA₂ X≰ = subst HasOneLowerCover (sym (a≡p hA₂)) iₚ
                      , subst (λ y → y ≤ (y ₋) ∨ b) (sym (a≡p hA₂)) (≰κ→ iₚ λ b≤κp → X≰ (≤-trans ∨-upperʳ b≤κp))

          from : Case → ¬ HasOneLowerCover a ⊎ (HasOneLowerCover a × a ≤ (a ₋) ∨ b)
          from (case₁ hA₁ _)            = inj₁ (join-reducible hA₁)
          from (case₂ hA₂ _ ⋁≰ ¬pBq₀)   = inj₂ (irr-below hA₂ (X≰κp ⋁≰ ¬pBq₀))
          from (case₃ hA₂ _ q₀≤κp ⋁≰)   = inj₂ (irr-below hA₂ (X≰κp ⋁≰ λ pBq₀ → B→≰κ pBq₀ q₀≤κp))

        -- Condition (1) on b: b is join reducible, being the join of r and the q_{i*}, i < j, and none of them.
        b-red : ¬ HasOneLowerCover b
        b-red one = cases (irr-⋁< one q₋ (suc j′) {r c} ∨-comm-law)
          where
          -- q_{j-1*} ≤ b, while q_{j-1*} ≰ r, since r ≤ t ≤ q_{j*} and (B1).
          qⱼ′₋≤b : q₋ j′ ≤ b
          qⱼ′₋≤b = ≤∨ʳ (⋁<-upper q₋ (n<1+n j′))

          cases : b ≡ r c ⊎ (Σ ℕ λ i → i <ℕ suc j′ × b ≡ q₋ i) → ⊥
          cases (inj₁ b≡r) =
            B1 sj′≤k (≤-trans qⱼ′₋≤b (≤-trans (≤-reflexive′ b≡r) (≤-trans (r≤t c) (≤-trans t≤qⱼ′₊₁₋ (₋≤ (x (suc j′)))))))
          cases (inj₂ (zero , _ , b≡q₀₋)) = at-zero (r-fact c)
            where
            at-zero : ¬ r c ≤ q₋ 0 ⊎ (x 0 ≤ κ p × ¬ ⋁< x j ≤ κ p) → ⊥
            at-zero (inj₁ r≰q₀₋)          = r≰q₀₋ (≤-trans ∨-upperˡ (≤-reflexive′ b≡q₀₋))
            at-zero (inj₂ (q₀≤κp , ⋁≰))   =
              X≰κp ⋁≰ (λ pBq₀ → B→≰κ pBq₀ q₀≤κp) (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ b≡q₀₋) (≤-trans (₋≤ (x 0)) q₀≤κp)))
          cases (inj₂ (suc i′ , si′<sj′ , b≡qᵢ₋)) =
            B1 (≤ℕ-trans (s≤s⁻¹ si′<sj′) (<⇒≤ sj′≤k))
               (≤-trans (≤∨ʳ (⋁<-upper q₋ (<ℕ-trans (n<1+n i′) si′<sj′))) (≤-trans (≤-reflexive′ b≡qᵢ₋) (₋≤ (x (suc i′)))))

        -- Condition (3).
        b≤b₀ : b ≤ b₀
        b≤b₀ = ∨-mono ≤-refl (∨-mono ≤-refl (₋≤ (x j′)))

        -- Condition (4): a ≰ b₀, by (W) on t ≤ b₀.
        a≰b₀ : ¬ a ≤ b₀
        a≰b₀ a≤b₀ = cases (W (x k) (κ p) (r c) (Y ∨ x j′) (≤-trans ∨-upperʳ a≤b₀))
          where
          -- Neither q_k nor κ p lies below b₀, since b₀ ≤ κ(q_k).
          qₖ≰ : ∀ {z} → z ≤ b₀ → ¬ x k ≤ z
          qₖ≰ z≤b₀ qₖ≤z = a≰κ iₖ (≤-trans qₖ≤z (≤-trans z≤b₀ b₀≤κₖ))

          κp≰ : ∀ {z} → z ≤ b₀ → ¬ κ p ≤ z
          κp≰ z≤b₀ κp≤z = a≰κ iₖ (≤-trans qₖ≤p∨κp (∨-least (≤-trans p≤qₖ₋ (₋≤κ (x k))) (≤-trans κp≤z (≤-trans z≤b₀ b₀≤κₖ))))

          cases : (x k ≤ b₀ ⊎ κ p ≤ b₀) ⊎ (t ≤ r c ⊎ t ≤ Y ∨ x j′) → ⊥
          cases (inj₁ (inj₁ qₖ≤))   = qₖ≰ ≤-refl qₖ≤
          cases (inj₁ (inj₂ κp≤))   = κp≰ ≤-refl κp≤
          cases (inj₂ (inj₁ t≤r))   = t≰r c t≤r
          cases (inj₂ (inj₂ t≤Yx))  = inner (W-⋁< q₋ j′ {x j′} t≤Yx)
            where
            -- t = q_{j-1} would put q_{j-1*} ≤ q_{j*}, against (B1).
            t≢qⱼ′ : t ≢ x j′
            t≢qⱼ′ t≡qⱼ′ = B1 sj′≤k (≤-trans (₋≤ (x j′)) (≤-trans (≤-reflexive′ (sym t≡qⱼ′)) (≤-trans t≤qⱼ′₊₁₋ (₋≤ (x (suc j′))))))

            inner : (x k ≤ Y ∨ x j′ ⊎ κ p ≤ Y ∨ x j′) ⊎ ((Σ ℕ λ i → i <ℕ j′ × t ≤ q₋ i) ⊎ t ≤ x j′) → ⊥
            inner (inj₁ (inj₁ qₖ≤))             = qₖ≰ ∨-upperʳ qₖ≤
            inner (inj₁ (inj₂ κp≤))             = κp≰ ∨-upperʳ κp≤
            inner (inj₂ (inj₁ (i , i<j′ , t≤)))  = t≰qᵢ₋ i (<⇒≤ i<j′) t≤
            inner (inj₂ (inj₂ t≤qⱼ′))           = t≰qᵢ₋ j′ ≤ℕ-refl (<→≤₋′ t≤qⱼ′ t≢qⱼ′)

        -- q_{j-1*} ≰ q_k: the book's argument for condition (5).
        qⱼ′₋≰qₖ : ¬ x j′ ₋ ≤ x k
        qⱼ′₋≰qₖ qⱼ′₋≤qₖ = decide (suc j′ ≟ℕ k)
          where
          decide : Dec (suc j′ ≡ k) → ⊥
          decide (yes sj′≡k) = B1 sj′≤k (subst (λ i → x j′ ₋ ≤ x i) (sym sj′≡k) qⱼ′₋≤qₖ)
          decide (no sj′≢k) = from (Sub-inorder sub (<⇒≤ j′<sk) ≤ℕ-refl (inj₁ qⱼ′Ap))
            where
            sj′<k : suc j′ <ℕ k
            sj′<k = ≤∧≢⇒< sj′≤k sj′≢k

            -- q_{j-1*} ≰ κ p: else q_{j-1*} ≤ t ≤ q_{j*}.
            qⱼ′₋≰κp : ¬ x j′ ₋ ≤ κ p
            qⱼ′₋≰κp h = B1 sj′≤k (≤-trans (∧-greatest qⱼ′₋≤qₖ h) (≤-trans t≤qⱼ′₊₁₋ (₋≤ (x (suc j′)))))

            -- κ p ∨ p = κ p ∨ q_{j-1*}, so by (SD∨) p ≤ q_{j-1*}.
            e : κ p ∨ p ≡ κ p ∨ (x j′ ₋)
            e = ≤-antisym (∨-least ∨-upperˡ (≤-trans (≰κ→ iₚ qⱼ′₋≰κp) (∨-mono (₋≤κ p) ≤-refl)))
                          (∨-least ∨-upperˡ (≤-trans qⱼ′₋≤qₖ (≤-trans qₖ≤p∨κp (∨-least ∨-upperʳ ∨-upperˡ))))

            p≤qⱼ′₋ : p ≤ x j′ ₋
            p≤qⱼ′₋ = decidable-stable (p ≤? x j′ ₋) λ p≰ →
              a≰κ iₚ (≤-from-∨ (trans ∨-comm-law (trans (sd∨ (κ p) p (x j′ ₋) e)
                        (∨-absorbʳ (≤-trans (<→≤₋′ ∧-lowerˡ (λ m≡p → p≰ m≡p)) (₋≤κ p))))))

            -- q_{j-1*} < q_k, and by (B4) q_{j-1} ≤ q_{k*}; so p < q_{j-1} ≤ q_k ≤ p ∨ κ p: q_{j-1} A p.
            qⱼ′₋<qₖ : x j′ ₋ < x k
            qⱼ′₋<qₖ = qⱼ′₋≤qₖ , λ e′ → t≰qᵢ₋ j′ ≤ℕ-refl (subst (t ≤_) (sym e′) ∧-lowerˡ)

            qⱼ′≤qₖ₋ : x j′ ≤ x k ₋
            qⱼ′≤qₖ₋ = ≤-trans (≰κ→ (irr (<⇒≤ j′<sk)) (B4 sj′<k ≤ℕ-refl)) (∨-least (<→≤₋ qⱼ′₋<qₖ) ≤-refl)

            qⱼ′Ap : x j′ A p
            qⱼ′Ap = irr (<⇒≤ j′<sk) , iₚ
                  , (≤-trans p≤qⱼ′₋ (₋≤ (x j′)) , λ p≡qⱼ′ → <ℕ-irrefl (sym (Sub-distinct sub ≤ℕ-refl (<⇒≤ j′<sk) p≡qⱼ′)) j′<sk)
                  , ≤-trans qⱼ′≤qₖ₋ (≤-trans (₋≤ (x k)) qₖ≤p∨κp)

            from : suc k ≡ suc j′ ⊎ (j′ ≡ suc k × suc k ≡ 0) → ⊥
            from (inj₁ sk≡sj′)  = <ℕ-irrefl (sym sk≡sj′) (<ℕ-trans sj′<k (n<1+n k))
            from (inj₂ (_ , ()))

        -- Condition (5).
        b≰a₀ : ¬ b ≤ a₀
        b≰a₀ b≤a₀ = qⱼ′₋≰qₖ (≤-trans (≤∨ʳ (⋁<-upper q₋ (n<1+n j′))) (≤-trans b≤a₀ a₀≤qₖ))

        -- Condition (6): a₀ ≰ a₁ ∨ b₀.
        a₀≰ : ¬ a₀ ≤ a₁ ∨ b₀
        a₀≰ a₀≤ = from which
          where
          a₁∨b₀≤κₖ : a₁ ∨ b₀ ≤ κ (x k)
          a₁∨b₀≤κₖ = ∨-least (≤-trans a₁≤qₖ₋ (₋≤κ (x k))) b₀≤κₖ

          from : a₀ ≡ x k ⊎ (suc j′ <ℕ k × ¬ a₀ ≤ κ (x j′)) → ⊥
          from (inj₁ a₀≡qₖ) = a≰κ iₖ (≤-trans (subst (_≤ a₁ ∨ b₀) a₀≡qₖ a₀≤) a₁∨b₀≤κₖ)
          from (inj₂ (sj′<k , a₀≰κⱼ′)) = a≰κ (irr j′≤sk) (≤-trans (≤∨ʳ ∨-upperʳ) (≤-trans ∨-upperʳ w≤κⱼ′))
            where
            j′≤sk : j′ ≤ℕ suc k
            j′≤sk = <⇒≤ j′<sk

            u : Fin (suc n)
            u = a₁ ∨ X

            qⱼ′≤ : x j′ ≤ (x j′ ₋) ∨ a₀
            qⱼ′≤ = ≰κ→ (irr j′≤sk) a₀≰κⱼ′

            X≤b₀ : X ≤ b₀
            X≤b₀ = ≤∨ʳ (∨-mono ≤-refl (₋≤ (x j′)))

            r≤u : r c ≤ u
            r≤u = ≤∨ˡ (≤-trans r≤a a≤a₁)

            -- u ∨ a₀ = a₀ ∨ b₀ = u ∨ q_{j-1}.
            e₁ : u ∨ a₀ ≡ a₀ ∨ b₀
            e₁ = ≤-antisym (∨-least (∨-least (≤∨ˡ (proj₁ (proj₁ a₁⋖a₀))) (≤∨ʳ X≤b₀)) ∨-upperˡ)
                           (∨-least ∨-upperʳ (∨-least (≤∨ˡ r≤u) (∨-least (≤∨ˡ (≤∨ʳ ∨-upperˡ))
                                                                  (≤-trans qⱼ′≤ (∨-least (≤∨ˡ (≤∨ʳ ∨-upperʳ)) ∨-upperʳ)))))

            e₂ : u ∨ x j′ ≡ a₀ ∨ b₀
            e₂ = ≤-antisym (∨-least (∨-least (≤∨ˡ (proj₁ (proj₁ a₁⋖a₀))) (≤∨ʳ X≤b₀)) (≤∨ʳ (≤∨ʳ ∨-upperʳ)))
                           (∨-least (≤-trans a₀≤ (∨-least (≤∨ˡ ∨-upperˡ) b₀≤u∨qⱼ′)) b₀≤u∨qⱼ′)
              where
              b₀≤u∨qⱼ′ : b₀ ≤ u ∨ x j′
              b₀≤u∨qⱼ′ = ∨-least (≤∨ˡ r≤u) (∨-least (≤∨ˡ (≤∨ʳ ∨-upperˡ)) ∨-upperʳ)

            -- q_{j-1} ≰ a₀, so a₀ ∧ q_{j-1} ≤ q_{j-1*} ≤ X, and (SD∨) gives a₀ ∨ b₀ = u ≤ κ(q_{j-1}).
            a₀∧qⱼ′≤X : a₀ ∧ x j′ ≤ X
            a₀∧qⱼ′≤X = ≤-trans (<→≤₋′ ∧-lowerʳ λ m≡qⱼ′ → qⱼ′₋≰qₖ (≤-trans (₋≤ (x j′)) (≤-trans (subst (_≤ a₀) m≡qⱼ′ ∧-lowerˡ) a₀≤qₖ)))
                               ∨-upperʳ

            w≤κⱼ′ : a₀ ∨ b₀ ≤ κ (x j′)
            w≤κⱼ′ = ≤-trans (≤-reflexive′ (sym e₁))
                            (≤-trans (≤-reflexive′ (trans (sd∨ u a₀ (x j′) (trans e₁ (sym e₂))) (∨-absorbʳ (≤-trans a₀∧qⱼ′≤X ∨-upperʳ))))
                                     (∨-least a₁≤κⱼ′ X≤κⱼ′))

        -- Condition (7): b₀ ≰ a₁ ∨ b.
        b₀≰ : ¬ b₀ ≤ a₁ ∨ b
        b₀≰ b₀≤ = a≰κ (irr (<⇒≤ j′<sk)) (≤-trans (≤∨ʳ ∨-upperʳ)
                    (≤-trans b₀≤ (∨-least a₁≤κⱼ′ (∨-least (≤-trans r≤a (≤-trans a≤a₁ a₁≤κⱼ′)) X≤κⱼ′))))

        -- The configuration of Lemma 5.38, which cannot exist.
        contradiction : ⊥
        contradiction = no-config₃₈ (record
          { b-red = b-red ; a-cond = a-cond ; a≤a₁ = a≤a₁ ; a₁⋖a₀ = a₁⋖a₀ ; b≤b₀ = b≤b₀
          ; a≰b₀ = a≰b₀ ; b≰a₀ = b≰a₀ ; a₀≰ = a₀≰ ; b₀≰ = b₀≰ })

      -- Lemma 5.42: none of the three cases takes place.
      lemma-5-42 : Case → ⊥
      lemma-5-42 c = split j refl
        where
        split : ∀ j″ → j ≡ j″ → ⊥
        split zero      j≡0 = t≰q₀₋ c (subst (λ i → t ≤ q₋ i) j≡0 t≤qⱼ₋)
        split (suc j′)  j≡  = Main.contradiction c j′ j≡
```
