---
layout: default
file: "src/Lattices/Nation/Lemma547.lagda.md"
title: "Lattices.Nation.Lemma547 module"
date: "2026-10-22"
author: "the agda-algebras development team"
check-cost: heavy
---

### Lemma 5.47: a B-type sequence below κ(p) ending in an A₂

This is the [Lattices.Nation.Lemma547][] module of the [agda-lattices][]
library.

Lemma 5.47 of [Freese, Ježek, and Nation (1995)][] (pp. 117 to 119) takes a
subsequence `q₀, …, q_k, p` of a minimal C-cycle in an S-lattice with
`q₀, …, q_k` a B-type sequence and `q_k A₂ p`, and concludes, when `q₀ ≤ κ(p)`
and `p₋ ≮ q₀₋`, that `p₋ ≰ q₀₋` and `⋁ᵢ₍ₖ qᵢ ≤ κ(p)`.  It is the case Lemma
5.46 leaves open, the one in which `p B r` may follow with `q₀ ≤ κ(p)`, and
the first of the preliminaries to Lemma 5.51, which extends a B-type sequence
through such a `p`.

The proof is the book's up to its last case.  With `j ≥ 1` the least index with
`p₋ ≤ q_{j*}`, case (3) of Lemma 5.42 gives `⋁ᵢ₍ⱼ qᵢ ≤ κ(p)`, and the claim is
that `j = k`.  Otherwise Lemma 5.43 is applied to `q₀, …, q_j, p` with
`t = κ(p)* ∧ κ(q_{j-1})`, whose hypotheses hold except perhaps (6),
`t ≰ u` for `u = p ∨ ⋁ᵢ₍ⱼ₋₁ qᵢ₋ ∨ q_{j-1}`, and (6) is proved by applying (W)
to `t ≤ u`.  Its surviving disjunct is `κ(q_{j-1}) ≤ u`, which puts `q_{j*}`
below `u`, and a second application of (W), to
`q_j ∧ (q_{j*} ∨ q_{j+1*}) = q_{j*} ≤ u`, leaves `q_{j+1*} ≤ u`.  Here the book
derives `q_{j-1} ≤ q_{j+1*}` from (SD∨), as this module does, and then asserts
`q_{j+1} ≤ κ(q_{j-1})*`, which does not follow: only `q_{j+1*} ≤ u` is known.
Nation's original (Trans. Amer. Math. Soc. 269 (1982), Lemma 3.5, pp. 326 and
327) continues instead: `j + 1 < k` by (B1), a third application of (W), to
`q_{j+1} ∧ (q_{j+1*} ∨ q_{j+2*}) = q_{j+1*} ≤ u`, leaves only
`q_{j+1*} ≤ q_{j-1}`, hence `q_{j+1*} = q_{j-1}`; then `q_{j+1} ≤ κ(p)` by the
free star principle and `p₋ ≰ q_{j+1*}`, so the lemma itself, for the shorter
sequence `q_{j+1}, …, q_k, p`, gives `⋁_{j<i<k} qᵢ ≤ κ(p)`; and since
`⋁ᵢ₍ₖ qᵢ ≰ κ(p)` was supposed, `q_j ≰ κ(p)`, so `p < q_j ≤ q_{j*} ∨ q_{k*} ≤ κ(p)*`
and `q_j A p`, against the minimality of the cycle.  The module follows Nation,
with the lemma proved by induction on a bound for `k`
(`lemma-5-47-bounded`{.AgdaFunction}) so that the recursive application to the
shorter sequence is structural; `lemma-5-47`{.AgdaFunction} instantiates the
bound.  Nation's `t` is `κ(p)* ∧ (p ∨ ⋁ᵢ₍ⱼ qᵢ₋)`; the book's `t` serves the
same argument and is kept.

The module checks in 3.1 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).  Its cost puts it under
the barrel policy: the front matter carries `check-cost: heavy`, and no barrel
imports it.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Lemma547 where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n ; m≤n⇒m<n∨m≡n ; m∸n+n≡m ; m<m+n
                                                         ; +-monoˡ-< ; +-monoˡ-≤ )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-reflexive to ≤ℕ-reflexive
                                                            ; ≤-trans to ≤ℕ-trans ; <-trans to <ℕ-trans
                                                            ; <-≤-trans to <ℕ-≤-trans ; <-irrefl to <ℕ-irrefl )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; cong ; cong₂ ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType         as BTypeModule
import Lattices.Nation.Lemma542      as Lemma542Module
import Lattices.Nation.Subsequences  as SubsequencesModule
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### The statement, with a bound on the length

```agda
module Lemma547 {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least ; ⋁<-around ; ⋁<-cong ; W-⋁<
                ; keep-then ; keep-then-≤ ; keep-then-> ; keep-then-mono ; keep-then-bound )
  module L542 = Lemma542Module.Lemma542 laws sd w
  module Subs = SubsequencesModule.Subsequences laws sd w

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 hiding ( k )
    open BT.InCycle 𝒞
    module L542C = L542.InCycle 𝒞
    module SubsC = Subs.InCycle 𝒞

    -- The lemma for every subsequence q₀, …, q_k, p with k ≤ b.
    Statement : ℕ → Type
    Statement b = ∀ k {x : ℕ → Fin (suc n)} → k ≤ℕ b → (sub : Sub (suc k) x) (bt : BType k x)
                → x k A₂ x (suc k) → x 0 ≤ κ (x (suc k)) → ¬ (x (suc k) ₋ < x 0 ₋)
                → (¬ x (suc k) ₋ ≤ x 0 ₋) × (⋁< x k ≤ κ (x (suc k)))
```

#### The argument, for k ≥ 1

The sequence has at least two members, since `q₀ ≤ κ(p)` while `q_k ≰ κ(p)`.

```agda
    module Main (b′ : ℕ) (ih : Statement b′) (k₁ : ℕ) {x : ℕ → Fin (suc n)} (k≤b : suc k₁ ≤ℕ suc b′)
                (sub : Sub (suc (suc k₁)) x) (bt : BType (suc k₁) x) (hA₂ : x (suc k₁) A₂ x (suc (suc k₁)))
                (q₀≤κp : x 0 ≤ κ (x (suc (suc k₁)))) (¬p₋<q₀₋ : ¬ (x (suc (suc k₁)) ₋ < x 0 ₋)) where
      open BType bt

      k : ℕ
      k = suc k₁

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

      qₖ≤p∨κp : x k ≤ p ∨ κ p
      qₖ≤p∨κp = proj₂ (proj₂ (proj₂ hA))

      -- p₋ ≠ q₀₋: for k = 1 by (B1), as p₋ ≤ q_{1*}; for k ≥ 2, q_{k*} ≰ κ(q₀) by (B4), so p₋ = q₀₋ ≤ q_{k*}
      -- would give q₀ ≤ q₀₋ ∨ q_{k*} = q_{k*}, whence q₀ ≤ q_k ∧ κ(p) = p₋ = q₀₋.
      p₋≢q₀₋ : p ₋ ≢ x 0 ₋
      p₋≢q₀₋ = ne k₁ sub bt hA₂ q₀≤κp
        where
        ne : ∀ k₁ {x : ℕ → Fin (suc n)} (sub : Sub (suc (suc k₁)) x) (bt : BType (suc k₁) x)
           → x (suc k₁) A₂ x (suc (suc k₁)) → x 0 ≤ κ (x (suc (suc k₁))) → x (suc (suc k₁)) ₋ ≢ x 0 ₋
        ne zero     {x} sub bt hA₂ _ e =
          BType.B1 bt ≤ℕ-refl
            (≤-trans (≤-reflexive′ (sym e)) (≤-trans (₋≤ (x 2)) (≤-trans (<→≤₋ (A→< (proj₁ hA₂))) (₋≤ (x 1)))))
        ne (suc k₂) {x} sub bt hA₂ q₀≤κp e = proj₂ (Sub-irr sub z≤n) (≤-antisym (₋≤ (x 0)) q₀≤q₀₋)
          where
          q₀≤q₀₋∨qₖ₋ : x 0 ≤ (x 0 ₋) ∨ (x (suc (suc k₂)) ₋)
          q₀≤q₀₋∨qₖ₋ = ≰κ→ (Sub-irr sub z≤n) (BType.B4 bt (s≤s (s≤s z≤n)) ≤ℕ-refl)

          q₀≤qₖ₋ : x 0 ≤ x (suc (suc k₂)) ₋
          q₀≤qₖ₋ = ≤-trans q₀≤q₀₋∨qₖ₋
                     (∨-least (≤-trans (≤-reflexive′ (sym e)) (≤-trans (₋≤ _) (<→≤₋ (A→< (proj₁ hA₂))))) ≤-refl)

          q₀≤q₀₋ : x 0 ≤ x 0 ₋
          q₀≤q₀₋ = ≤-trans (∧-greatest (≤-trans q₀≤qₖ₋ (₋≤ _)) q₀≤κp)
                           (≤-trans (≤-reflexive′ (proj₂ hA₂)) (≤-reflexive′ e))

      p₋≰q₀₋ : ¬ p ₋ ≤ x 0 ₋
      p₋≰q₀₋ le = ¬p₋<q₀₋ (le , p₋≢q₀₋)

      -- The least index j with p₋ ≤ q_{j*}, in the setting of Lemma 5.42, and case (3) of that lemma.
      module S = L542C.Setting sub bt hA

      ⋁<S≤κp : ⋁< x S.j ≤ κ p
      ⋁<S≤κp = decidable-stable (_ ≤? _) λ h → S.lemma-5-42 (S.case₃ hA₂ p₋≰q₀₋ q₀≤κp h)

      -- A member below κ(p) that the cycle's minimality excludes: q_j A p for an index j < k.
      minimality : ∀ {j} → suc j ≤ℕ k → ¬ x j A p
      minimality {j} sj≤k qⱼAp = from (Sub-inorder sub (≤ℕ-trans (<⇒≤ sj≤k) (n≤1+n k)) ≤ℕ-refl (inj₁ qⱼAp))
        where
        from : suc k ≡ suc j ⊎ (j ≡ suc k × suc k ≡ 0) → ⊥
        from (inj₁ e)       = <ℕ-irrefl (sym e) (s≤s sj≤k)
        from (inj₂ (_ , ()))
```

The case `j < k`, where `⋁ᵢ₍ₖ qᵢ ≰ κ(p)` is supposed and refuted.

```agda
      module JLess (j′ : ℕ) (sj′<k : suc j′ <ℕ k) (p₋≤qⱼ₋ : p ₋ ≤ x (suc j′) ₋)
                   (least : ∀ i → i <ℕ suc j′ → ¬ p ₋ ≤ x i ₋) (⋁<ⱼ≤κp : ⋁< x (suc j′) ≤ κ p)
                   (¬⋁<ₖ≤κp : ¬ ⋁< x k ≤ κ p) where

        j : ℕ
        j = suc j′

        -- Index bookkeeping.
        j≤k : j ≤ℕ k
        j≤k = <⇒≤ sj′<k

        j′<k : j′ <ℕ k
        j′<k = <ℕ-trans (n<1+n j′) sj′<k

        j′≤k : j′ ≤ℕ k
        j′≤k = <⇒≤ j′<k

        sj≤k : suc j ≤ℕ k
        sj≤k = sj′<k

        j≤sk : j ≤ℕ suc k
        j≤sk = ≤ℕ-trans j≤k (n≤1+n k)

        j′≤sk : j′ ≤ℕ suc k
        j′≤sk = ≤ℕ-trans j′≤k (n≤1+n k)

        sj≤sk : suc j ≤ℕ suc k
        sj≤sk = ≤ℕ-trans sj≤k (n≤1+n k)

        j<sk : j <ℕ suc k
        j<sk = <ℕ-trans sj′<k (n<1+n k)

        iⱼ′ : HasOneLowerCover (x j′)
        iⱼ′ = irr j′≤sk

        iⱼ : HasOneLowerCover (x j)
        iⱼ = irr j≤sk

        iⱼ₊₁ : HasOneLowerCover (x (suc j))
        iⱼ₊₁ = irr sj≤sk

        -- The members before q_j lie below κ(p).
        xᵢ≤κp : ∀ {i} → i <ℕ j → x i ≤ κ p
        xᵢ≤κp i<j = ≤-trans (⋁<-upper x i<j) ⋁<ⱼ≤κp

        -- p ≤ κ(q_{j-1}) and p ≤ κ(q_j), by the free star principle from p₋ ≤ q_{j*} ≤ κ(q_{j-1}) (B3) and
        -- p₋ ≤ q_{j*} ≤ κ(q_j).
        p≤κqⱼ′ : p ≤ κ (x j′)
        p≤κqⱼ′ = Sub-freeStar′ sub j′≤sk ≤ℕ-refl (λ e → <ℕ-irrefl e (<ℕ-trans j′<k (n<1+n k)))
                               (λ e → <ℕ-irrefl (sym e) j<sk) (λ { (_ , ()) })
                               (≤-trans p₋≤qⱼ₋ (B3 j≤k))

        p≤κqⱼ : p ≤ κ (x j)
        p≤κqⱼ = Sub-freeStar′ sub j≤sk ≤ℕ-refl (λ e → <ℕ-irrefl e j<sk)
                              (λ e → <ℕ-irrefl (sym e) (s≤s sj′<k)) (λ { (_ , ()) })
                              (≤-trans p₋≤qⱼ₋ (₋≤κ (x j)))

        -- Y = ⋁ᵢ₍ⱼ₋₁ qᵢ₋ and u = p ∨ Y ∨ q_{j-1}, the right side of 5.43 (6), and its bounds.
        Y u : Fin (suc n)
        Y = ⋁< q₋ j′
        u = p ∨ (Y ∨ x j′)

        Y≤ : ∀ {z} → (∀ i → i <ℕ j′ → x i ≤ z) → Y ≤ z
        Y≤ f = ⋁<-least q₋ λ i i<j′ → ≤-trans (₋≤ (x i)) (f i i<j′)

        u≤ : ∀ {z} → p ≤ z → (∀ i → i ≤ℕ j′ → x i ≤ z) → u ≤ z
        u≤ p≤z f = ∨-least p≤z (∨-least (Y≤ λ i i<j′ → f i (<⇒≤ i<j′)) (f j′ ≤ℕ-refl))

        u≤κqₖ : u ≤ κ (x k)
        u≤κqₖ = u≤ (≤-trans p≤qₖ₋ (₋≤κ (x k))) λ i i≤j′ → B2 (≤ℕ-trans (s≤s i≤j′) j′<k) ≤ℕ-refl

        u≤κqⱼ : u ≤ κ (x j)
        u≤κqⱼ = u≤ p≤κqⱼ λ i i≤j′ → B2 (s≤s i≤j′) j≤k

        u≤κqⱼ′* : u ≤ κ (x j′) ∨ x j′
        u≤κqⱼ′* = u≤ (≤∨ˡ p≤κqⱼ′) λ i i≤j′ → cases i (m≤n⇒m<n∨m≡n i≤j′)
          where
          cases : ∀ i → i <ℕ j′ ⊎ i ≡ j′ → x i ≤ κ (x j′) ∨ x j′
          cases i (inj₁ i<j′) = ≤∨ˡ (B2 i<j′ j′≤k)
          cases i (inj₂ e)    = subst (λ z → x z ≤ κ (x j′) ∨ x j′) (sym e) ∨-upperʳ

        u≤p∨κp : u ≤ p ∨ κ p
        u≤p∨κp = u≤ ∨-upperˡ λ i i≤j′ → ≤∨ʳ (xᵢ≤κp (s≤s i≤j′))

        -- t = κ(p)* ∧ κ(q_{j-1}).
        t : Fin (suc n)
        t = (p ∨ κ p) ∧ κ (x j′)

        p≤t : p ≤ t
        p≤t = ∧-greatest ∨-upperˡ p≤κqⱼ′

        p₋≤t : p ₋ ≤ t
        p₋≤t = ≤-trans (₋≤ p) p≤t

        t≤κqⱼ′ : t ≤ κ (x j′)
        t≤κqⱼ′ = ∧-lowerʳ

        -- p ≠ t: q_{j-1*} ≤ t, so p = t would give q_{j-1*} ≤ p ∧ κ(p) = p₋ ≤ q_j, against (B1).
        p<t : p < t
        p<t = p≤t , λ p≡t → B1 j≤k (≤-trans (qⱼ′₋≤p₋ p≡t) (≤-trans p₋≤qⱼ₋ (₋≤ (x j))))
          where
          qⱼ′₋≤κp : x j′ ₋ ≤ κ p
          qⱼ′₋≤κp = ≤-trans (₋≤ (x j′)) (xᵢ≤κp (n<1+n j′))

          qⱼ′₋≤t : x j′ ₋ ≤ t
          qⱼ′₋≤t = ∧-greatest (≤∨ʳ qⱼ′₋≤κp) (₋≤κ (x j′))

          qⱼ′₋≤p₋ : p ≡ t → x j′ ₋ ≤ p ₋
          qⱼ′₋≤p₋ p≡t = ≤-trans (∧-greatest (subst (x j′ ₋ ≤_) (sym p≡t) qⱼ′₋≤t) qⱼ′₋≤κp) (≤-reflexive′ (a∧κ iₚ))
```

The sub-case `q_{j*} ≤ p` of (†): `q_{j*}` is `p` or `p₋`, `j + 1 < k` by
(B1), and (B4) puts `q_j` below `q_{k*}`; the first alternative makes `q_j A p`,
the second `q_j ≤ q_k ∧ κ(p) = q_{j*}`.

```agda
        module QjBelowP (qⱼ₋≤p : x j ₋ ≤ p) where
          qⱼ₋≤qₖ₋ : x j ₋ ≤ x k ₋
          qⱼ₋≤qₖ₋ = ≤-trans qⱼ₋≤p p≤qₖ₋

          sj≢k : suc j ≢ k
          sj≢k e = B1 sj≤k (subst (λ z → x j ₋ ≤ x z) (sym e) (≤-trans qⱼ₋≤qₖ₋ (₋≤ (x k))))

          ssj≤k : suc (suc j) ≤ℕ k
          ssj≤k = from (m≤n⇒m<n∨m≡n sj≤k)
            where
            from : suc j <ℕ k ⊎ suc j ≡ k → suc (suc j) ≤ℕ k
            from (inj₁ lt) = lt
            from (inj₂ e)  = ⊥-elim (sj≢k e)

          qⱼ≤qₖ₋ : x j ≤ x k ₋
          qⱼ≤qₖ₋ = ≤-trans (≰κ→ iⱼ (B4 ssj≤k ≤ℕ-refl)) (∨-least qⱼ₋≤qₖ₋ ≤-refl)

          p≤qⱼ→p<qⱼ : p ≤ x j → p < x j
          p≤qⱼ→p<qⱼ le = le , λ e → <ℕ-irrefl (sym (Sub-distinct sub ≤ℕ-refl j≤sk e)) j<sk

          contradiction : ⊥
          contradiction = decide (x j ₋ ≟ p)
            where
            decide : Dec (x j ₋ ≡ p) → ⊥
            decide (yes e) =
              minimality sj≤k (iⱼ , iₚ , p≤qⱼ→p<qⱼ (≤-trans (≤-reflexive′ (sym e)) (₋≤ (x j)))
                                       , ≤-trans qⱼ≤qₖ₋ (≤-trans (₋≤ (x k)) qₖ≤p∨κp))
            decide (no ne) =
              proj₂ iⱼ (≤-antisym (₋≤ (x j))
                                  (≤-trans (∧-greatest (≤-trans qⱼ≤qₖ₋ (₋≤ (x k))) qⱼ≤κp)
                                           (≤-trans (≤-reflexive′ qₖ∧κp≡p₋) (≤-reflexive′ (sym qⱼ₋≡p₋)))))
              where
              qⱼ₋≡p₋ : x j ₋ ≡ p ₋
              qⱼ₋≡p₋ = ≤-antisym (<→≤₋′ qⱼ₋≤p ne) p₋≤qⱼ₋

              p≰qⱼ : ¬ p ≤ x j
              p≰qⱼ le = proj₂ iₚ (≤-antisym (₋≤ p) (subst (p ≤_) qⱼ₋≡p₋ (<→≤₋′ le (proj₂ (p≤qⱼ→p<qⱼ le)))))

              qⱼ≤κp : x j ≤ κ p
              qⱼ≤κp = →≤κ iₚ λ le → p≰qⱼ (≤-trans le (∨-least (≤-trans (≤-reflexive′ (sym qⱼ₋≡p₋)) (₋≤ (x j))) ≤-refl))
```

The sub-case `q_{j+1*} ≤ u` of (†), Nation's continuation.

```agda
        module Sub2 (qⱼ₋≤u : x j ₋ ≤ u) (qⱼ₊₁₋≤u : x (suc j) ₋ ≤ u) where
          -- (B4): q_{j+1*} ≰ κ(q_{j-1}).
          qⱼ₊₁₋≰κqⱼ′ : ¬ x (suc j) ₋ ≤ κ (x j′)
          qⱼ₊₁₋≰κqⱼ′ = B4 (n<1+n j) sj≤k

          -- κ(q_{j-1}) ∨ q_{j-1} = κ(q_{j-1}) ∨ q_{j+1*}, by Lemma 2.57 and q_{j+1*} ≤ u ≤ κ(q_{j-1})*.
          e₁ : κ (x j′) ∨ x j′ ≡ κ (x j′) ∨ (x (suc j) ₋)
          e₁ = ≤-antisym (∨-least ∨-upperˡ (κ<→≤ iⱼ′ (∨-upperˡ , λ e → qⱼ₊₁₋≰κqⱼ′ (≤ᵈ→ (sym e)))))
                         (∨-least ∨-upperˡ (≤-trans qⱼ₊₁₋≤u u≤κqⱼ′*))

          -- (SD∨) then gives κ(q_{j-1}) ∨ q_{j-1} = κ(q_{j-1}) ∨ (q_{j-1} ∧ q_{j+1*}), so q_{j-1} ≤ q_{j+1*}.
          qⱼ′≤qⱼ₊₁₋ : x j′ ≤ x (suc j) ₋
          qⱼ′≤qⱼ₊₁₋ = decidable-stable (_ ≤? _) λ ne →
            a≰κ iⱼ′ (≤-trans (≤-trans ∨-upperʳ (≤-reflexive′ (sd∨ (κ (x j′)) (x j′) (x (suc j) ₋) e₁)))
                             (∨-least ≤-refl (≤-trans (<→≤₋′ ∧-lowerˡ ne) (₋≤κ (x j′)))))

          -- j + 1 ≠ k: else q_{j-1} ≤ q_{k*} ∧ κ(p) = p₋ ≤ q_{j*}, and q_{j-1*} ≤ q_j contradicts (B1).
          sj≢k : suc j ≢ k
          sj≢k e = B1 j≤k (≤-trans (₋≤ (x j′)) (≤-trans qⱼ′≤p₋ (≤-trans p₋≤qⱼ₋ (₋≤ (x j)))))
            where
            qⱼ′≤qₖ₋ : x j′ ≤ x k ₋
            qⱼ′≤qₖ₋ = subst (λ z → x j′ ≤ x z ₋) e qⱼ′≤qⱼ₊₁₋

            qⱼ′≤p₋ : x j′ ≤ p ₋
            qⱼ′≤p₋ = ≤-trans (∧-greatest (≤-trans qⱼ′≤qₖ₋ (₋≤ (x k))) (xᵢ≤κp (n<1+n j′))) (≤-reflexive′ qₖ∧κp≡p₋)

          ssj≤k : suc (suc j) ≤ℕ k
          ssj≤k = from (m≤n⇒m<n∨m≡n sj≤k)
            where
            from : suc j <ℕ k ⊎ suc j ≡ k → suc (suc j) ≤ℕ k
            from (inj₁ lt) = lt
            from (inj₂ e)  = ⊥-elim (sj≢k e)

          sj<sk : suc j <ℕ suc k
          sj<sk = <ℕ-trans ssj≤k (n<1+n k)

          -- p ≤ κ(q_{j+1}), by the free star principle from p₋ ≤ q_{j*} ≤ q_j ≤ κ(q_{j+1}) (B2).
          p≤κqⱼ₊₁ : p ≤ κ (x (suc j))
          p≤κqⱼ₊₁ = Sub-freeStar′ sub sj≤sk ≤ℕ-refl (λ e → <ℕ-irrefl e sj<sk)
                                  (λ e → <ℕ-irrefl (sym e) (s≤s ssj≤k)) (λ { (_ , ()) })
                                  (≤-trans p₋≤qⱼ₋ (≤-trans (₋≤ (x j)) (B2 (n<1+n j) sj≤k)))

          u≤κqⱼ₊₁ : u ≤ κ (x (suc j))
          u≤κqⱼ₊₁ = u≤ p≤κqⱼ₊₁ λ i i≤j′ → B2 (≤ℕ-trans (s≤s i≤j′) (n≤1+n j)) sj≤k

          -- (W) on q_{j+1} ∧ (q_{j+1*} ∨ q_{j+2*}) = q_{j+1*} ≤ u fails in every disjunct but q_{j+1*} ≤ q_{j-1}.
          meet : Fin (suc n)
          meet = x (suc j) ∧ ((x (suc j) ₋) ∨ (x (suc (suc j)) ₋))

          qⱼ₊₁₋≤meet : x (suc j) ₋ ≤ meet
          qⱼ₊₁₋≤meet = ∧-greatest (₋≤ _) ∨-upperˡ

          meet≤u : meet ≤ u
          meet≤u = ≤-trans (≤-trans (∧-monoʳ (∨-least (₋≤κ (x (suc j))) (B3 ssj≤k))) (≤-reflexive′ (a∧κ iⱼ₊₁)))
                           qⱼ₊₁₋≤u

          from-qⱼ₊₁ : ¬ x (suc j) ≤ u
          from-qⱼ₊₁ le = a≰κ iⱼ₊₁ (≤-trans le u≤κqⱼ₊₁)

          from-join : ¬ (x (suc j) ₋) ∨ (x (suc (suc j)) ₋) ≤ u
          from-join le = B4 (n<1+n (suc j)) ssj≤k (≤-trans ∨-upperʳ (≤-trans le u≤κqⱼ))

          from-meet≤p : ¬ meet ≤ p
          from-meet≤p le = qⱼ₊₁₋≰κqⱼ′ (≤-trans qⱼ₊₁₋≤meet (≤-trans le p≤κqⱼ′))

          from-meet≤qᵢ₋ : ∀ i → i <ℕ j′ → ¬ meet ≤ x i ₋
          from-meet≤qᵢ₋ i i<j′ le =
            qⱼ₊₁₋≰κqⱼ′ (≤-trans qⱼ₊₁₋≤meet (≤-trans le (≤-trans (₋≤ (x i)) (B2 i<j′ j′≤k))))
```

The remaining disjunct, `q_{j+1*} = q_{j-1}`: the lemma for the shorter
sequence `q_{j+1}, …, q_k, p`, read as the family `i ↦ x (i + (j + 1))`, and
`q_j A p`.

```agda
          module Equal (e : x (suc j) ₋ ≡ x j′) where
            -- q_{j+1} ≤ κ(p), by the free star principle from q_{j+1*} = q_{j-1} ≤ κ(p).
            qⱼ₊₁≤κp : x (suc j) ≤ κ p
            qⱼ₊₁≤κp = Sub-freeStar′ sub ≤ℕ-refl sj≤sk (λ e′ → <ℕ-irrefl (sym e′) sj<sk)
                                    (λ e′ → <ℕ-irrefl e′ (<ℕ-trans sj<sk (n<1+n (suc k)))) (λ { (_ , ()) })
                                    (subst (_≤ κ p) (sym e) (xᵢ≤κp (n<1+n j′)))

            -- p₋ ≰ q_{j+1*} = q_{j-1}: equality contradicts (B1), and p₋ ≤ q_{j-1*} the choice of j.
            ¬p₋≤qⱼ₊₁₋ : ¬ p ₋ ≤ x (suc j) ₋
            ¬p₋≤qⱼ₊₁₋ le = decide (p ₋ ≟ x j′)
              where
              decide : Dec (p ₋ ≡ x j′) → ⊥
              decide (yes e′) = B1 j≤k (≤-trans (₋≤ (x j′)) (≤-trans (≤-reflexive′ (sym e′)) (≤-trans p₋≤qⱼ₋ (₋≤ (x j)))))
              decide (no ne)  = least j′ (n<1+n j′) (<→≤₋′ (subst (p ₋ ≤_) e le) ne)

            -- The shorter sequence, its length k′ = k ∸ (j + 1), and the induction hypothesis.
            m : ℕ
            m = suc j

            k′ : ℕ
            k′ = k ∸ m

            e″ : k′ + m ≡ k
            e″ = m∸n+n≡m sj≤k

            x″ : ℕ → Fin (suc n)
            x″ i = x (i + m)

            sub″ : Sub (suc k′) x″
            sub″ = Sub-restrict sub (_+ m) (λ i<i′ _ → +-monoˡ-< m i<i′)
                                λ {i} i≤sk′ → subst (i + m ≤ℕ_) (cong suc e″) (+-monoˡ-≤ m i≤sk′)

            bt″ : BType k′ x″
            bt″ = BType-shiftʳ m k′ (≤ℕ-reflexive e″) bt

            hA₂″ : x″ k′ A₂ x″ (suc k′)
            hA₂″ = subst (λ z → x z A₂ x (suc z)) (sym e″) hA₂

            q₀″≤κp″ : x″ 0 ≤ κ (x″ (suc k′))
            q₀″≤κp″ = subst (λ z → x m ≤ κ (x (suc z))) (sym e″) qⱼ₊₁≤κp

            ¬p₋<q₀₋″ : ¬ (x″ (suc k′) ₋ < x″ 0 ₋)
            ¬p₋<q₀₋″ (le , _) = ¬p₋≤qⱼ₊₁₋ (subst (λ z → x (suc z) ₋ ≤ x m ₋) e″ le)

            k′≤b′ : k′ ≤ℕ b′
            k′≤b′ = s≤s⁻¹ (<ℕ-≤-trans (subst (k′ <ℕ_) e″ (m<m+n k′ (s≤s z≤n))) k≤b)

            ⋁<″≤κp : ⋁< x″ k′ ≤ κ p
            ⋁<″≤κp = subst (λ z → ⋁< x″ k′ ≤ κ (x (suc z))) e″
                           (proj₂ (ih k′ k′≤b′ sub″ bt″ hA₂″ q₀″≤κp″ ¬p₋<q₀₋″))

            -- q_j ≰ κ(p), as ⋁ᵢ₍ₖ qᵢ ≰ κ(p) while every other member lies below κ(p).
            qⱼ≰κp : ¬ x j ≤ κ p
            qⱼ≰κp le = ¬⋁<ₖ≤κp (⋁<-around x m k low λ i i<k′ → ≤-trans (⋁<-upper x″ i<k′) ⋁<″≤κp)
              where
              low : ∀ i → i <ℕ m → x i ≤ κ p
              low i i<m = cases (m≤n⇒m<n∨m≡n (s≤s⁻¹ i<m))
                where
                cases : i <ℕ j ⊎ i ≡ j → x i ≤ κ p
                cases (inj₁ i<j) = xᵢ≤κp i<j
                cases (inj₂ e′)  = subst (λ z → x z ≤ κ p) (sym e′) le

            -- Hence p < q_j, and q_j ≤ q_{j*} ∨ q_{k*} ≤ κ(p)* by (B4): q_j A p.
            p<qⱼ : p < x j
            p<qⱼ = ≤-trans (≰κ→ iₚ qⱼ≰κp) (∨-least (≤-trans p₋≤qⱼ₋ (₋≤ (x j))) ≤-refl)
                  , λ e′ → <ℕ-irrefl (sym (Sub-distinct sub ≤ℕ-refl j≤sk e′)) j<sk

            qⱼ≤κp* : x j ≤ p ∨ κ p
            qⱼ≤κp* = ≤-trans (≰κ→ iⱼ (B4 ssj≤k ≤ℕ-refl))
                             (∨-least (≤-trans qⱼ₋≤u u≤p∨κp) (≤-trans (₋≤ (x k)) qₖ≤p∨κp))

            contradiction : ⊥
            contradiction = minimality sj≤k (iⱼ , iₚ , p<qⱼ , qⱼ≤κp*)

          from-meet≤qⱼ′ : ¬ meet ≤ x j′
          from-meet≤qⱼ′ le = Equal.contradiction (≤-antisym (≤-trans qⱼ₊₁₋≤meet le) qⱼ′≤qⱼ₊₁₋)

          contradiction : ⊥
          contradiction = outer (W (x (suc j)) ((x (suc j) ₋) ∨ (x (suc (suc j)) ₋)) p (Y ∨ x j′) meet≤u)
            where
            inner : (x (suc j) ≤ Y ∨ x j′ ⊎ (x (suc j) ₋) ∨ (x (suc (suc j)) ₋) ≤ Y ∨ x j′)
                  ⊎ ((Σ ℕ λ i → i <ℕ j′ × meet ≤ x i ₋) ⊎ meet ≤ x j′) → ⊥
            inner (inj₁ (inj₁ le))               = from-qⱼ₊₁ (≤∨ʳ le)
            inner (inj₁ (inj₂ le))               = from-join (≤∨ʳ le)
            inner (inj₂ (inj₁ (i , i<j′ , le)))  = from-meet≤qᵢ₋ i i<j′ le
            inner (inj₂ (inj₂ le))               = from-meet≤qⱼ′ le

            outer : (x (suc j) ≤ u ⊎ (x (suc j) ₋) ∨ (x (suc (suc j)) ₋) ≤ u) ⊎ (meet ≤ p ⊎ meet ≤ Y ∨ x j′) → ⊥
            outer (inj₁ (inj₁ le)) = from-qⱼ₊₁ le
            outer (inj₁ (inj₂ le)) = from-join le
            outer (inj₂ (inj₁ le)) = from-meet≤p le
            outer (inj₂ (inj₂ le)) = inner (W-⋁< q₋ j′ le)
```

The case `κ(q_{j-1}) ≤ u` of the first application of (W), (†).

```agda
        module Dagger (κqⱼ′≤u : κ (x j′) ≤ u) where
          qⱼ₋≤u : x j ₋ ≤ u
          qⱼ₋≤u = ≤-trans (B3 j≤k) κqⱼ′≤u

          -- q_j ∧ (q_{j*} ∨ q_{j+1*}) = q_{j*} ≤ u, as q_{j+1*} ≤ κ(q_j) by (B3).
          meet : Fin (suc n)
          meet = x j ∧ ((x j ₋) ∨ (x (suc j) ₋))

          qⱼ₋≤meet : x j ₋ ≤ meet
          qⱼ₋≤meet = ∧-greatest (₋≤ (x j)) ∨-upperˡ

          meet≤u : meet ≤ u
          meet≤u = ≤-trans (≤-trans (∧-monoʳ (∨-least (₋≤κ (x j)) (B3 sj≤k))) (≤-reflexive′ (a∧κ iⱼ))) qⱼ₋≤u

          from-qⱼ : ¬ x j ≤ u
          from-qⱼ le = a≰κ iⱼ (≤-trans le u≤κqⱼ)

          from-join : ¬ (x j ₋) ∨ (x (suc j) ₋) ≤ u
          from-join le = Sub2.contradiction qⱼ₋≤u (≤-trans ∨-upperʳ le)

          from-meet≤p : ¬ meet ≤ p
          from-meet≤p le = QjBelowP.contradiction (≤-trans qⱼ₋≤meet le)

          from-meet≤qᵢ₋ : ∀ i → i <ℕ j′ → ¬ meet ≤ x i ₋
          from-meet≤qᵢ₋ i i<j′ le = least i (<ℕ-trans i<j′ (n<1+n j′)) (≤-trans p₋≤qⱼ₋ (≤-trans qⱼ₋≤meet le))

          -- q_{j*} ≤ q_{j-1}: equality contradicts (B1), and q_{j*} ≤ q_{j-1*} the choice of j.
          from-meet≤qⱼ′ : ¬ meet ≤ x j′
          from-meet≤qⱼ′ le = decide (x j ₋ ≟ x j′)
            where
            decide : Dec (x j ₋ ≡ x j′) → ⊥
            decide (yes e) = B1 j≤k (≤-trans (₋≤ (x j′)) (≤-trans (≤-reflexive′ (sym e)) (₋≤ (x j))))
            decide (no ne) = least j′ (n<1+n j′) (≤-trans p₋≤qⱼ₋ (<→≤₋′ (≤-trans qⱼ₋≤meet le) ne))

          contradiction : ⊥
          contradiction = outer (W (x j) ((x j ₋) ∨ (x (suc j) ₋)) p (Y ∨ x j′) meet≤u)
            where
            inner : (x j ≤ Y ∨ x j′ ⊎ (x j ₋) ∨ (x (suc j) ₋) ≤ Y ∨ x j′)
                  ⊎ ((Σ ℕ λ i → i <ℕ j′ × meet ≤ x i ₋) ⊎ meet ≤ x j′) → ⊥
            inner (inj₁ (inj₁ le))               = from-qⱼ (≤∨ʳ le)
            inner (inj₁ (inj₂ le))               = from-join (≤∨ʳ le)
            inner (inj₂ (inj₁ (i , i<j′ , le)))  = from-meet≤qᵢ₋ i i<j′ le
            inner (inj₂ (inj₂ le))               = from-meet≤qⱼ′ le

            outer : (x j ≤ u ⊎ (x j ₋) ∨ (x (suc j) ₋) ≤ u) ⊎ (meet ≤ p ⊎ meet ≤ Y ∨ x j′) → ⊥
            outer (inj₁ (inj₁ le)) = from-qⱼ le
            outer (inj₁ (inj₂ le)) = from-join le
            outer (inj₂ (inj₁ le)) = from-meet≤p le
            outer (inj₂ (inj₂ le)) = inner (W-⋁< q₋ j′ le)
```

Hypothesis (6) of Lemma 5.43, and the lemma applied to `q₀, …, q_j, p`.

```agda
        -- (W) on t = κ(p)* ∧ κ(q_{j-1}) ≤ u: κ(p)* ≤ u puts q_k below κ(q_k); κ(q_{j-1}) ≤ u is (†);
        -- t ≤ p contradicts p < t; t ≤ q_{i*} for i < j - 1, and t ≤ q_{j-1}, contradict the choice of j.
        from-κp* : ¬ p ∨ κ p ≤ u
        from-κp* le = a≰κ iₖ (≤-trans qₖ≤p∨κp (≤-trans le u≤κqₖ))

        from-t≤qᵢ₋ : ∀ i → i <ℕ j′ → ¬ t ≤ x i ₋
        from-t≤qᵢ₋ i i<j′ le = least i (<ℕ-trans i<j′ (n<1+n j′)) (≤-trans p₋≤t le)

        from-t≤qⱼ′ : ¬ t ≤ x j′
        from-t≤qⱼ′ le = least j′ (n<1+n j′) (≤-trans p₋≤t (<→≤₋′ le λ t≡qⱼ′ → a≰κ iⱼ′ (subst (_≤ κ (x j′)) t≡qⱼ′ t≤κqⱼ′)))

        t≰u : ¬ t ≤ u
        t≰u t≤u = outer (W (p ∨ κ p) (κ (x j′)) p (Y ∨ x j′) t≤u)
          where
          inner : (p ∨ κ p ≤ Y ∨ x j′ ⊎ κ (x j′) ≤ Y ∨ x j′) ⊎ ((Σ ℕ λ i → i <ℕ j′ × t ≤ x i ₋) ⊎ t ≤ x j′) → ⊥
          inner (inj₁ (inj₁ le))               = from-κp* (≤∨ʳ le)
          inner (inj₁ (inj₂ le))               = Dagger.contradiction (≤∨ʳ le)
          inner (inj₂ (inj₁ (i , i<j′ , le)))  = from-t≤qᵢ₋ i i<j′ le
          inner (inj₂ (inj₂ le))               = from-t≤qⱼ′ le

          outer : (p ∨ κ p ≤ u ⊎ κ (x j′) ≤ u) ⊎ (t ≤ p ⊎ t ≤ Y ∨ x j′) → ⊥
          outer (inj₁ (inj₁ le)) = from-κp* le
          outer (inj₁ (inj₂ le)) = Dagger.contradiction le
          outer (inj₂ (inj₁ le)) = proj₂ p<t (≤-antisym p≤t le)
          outer (inj₂ (inj₂ le)) = inner (W-⋁< q₋ j′ le)

        -- Lemma 5.43 for q₀, …, q_j, p, the family x ∘ keep-then j (k + 1), gives ⋁ᵢ₍ⱼ qᵢ₋ ≰ κ(p),
        -- against ⋁ᵢ₍ⱼ qᵢ ≤ κ(p).
        contradiction : ⊥
        contradiction = X′≰κp (⋁<-least (λ i → x′ i ₋) λ i i<j → ≤-trans (₋≤ (x′ i)) (subst (_≤ κ p) (sym (x′ᵢ≡ (<ℕ-trans i<j (n<1+n j)))) (xᵢ≤κp i<j)))
          where
          reindex : ℕ → ℕ
          reindex = keep-then j (suc k)

          x′ : ℕ → Fin (suc n)
          x′ i = x (reindex i)

          sub′ : Sub (suc j) x′
          sub′ = Sub-restrict sub reindex (keep-then-mono (s≤s j≤k)) (keep-then-bound j≤sk ≤ℕ-refl)

          bt′ : BType j x′
          bt′ = BType-cong j≤k (λ i i≤j → cong x (keep-then-≤ i≤j)) bt

          x′ᵢ≡ : ∀ {i} → i <ℕ suc j → x′ i ≡ x i
          x′ᵢ≡ i<sj = cong x (keep-then-≤ (s≤s⁻¹ i<sj))

          x′ⱼ₊₁≡p : x′ (suc j) ≡ p
          x′ⱼ₊₁≡p = cong x (keep-then-> (n<1+n j))

          x′ⱼ≡ : x′ j ≡ x j
          x′ⱼ≡ = x′ᵢ≡ (n<1+n j)

          x′ⱼ′≡ : x′ j′ ≡ x j′
          x′ⱼ′≡ = x′ᵢ≡ (<ℕ-trans (n<1+n j′) (n<1+n j))

          Y′ : Fin (suc n)
          Y′ = ⋁< (λ i → x′ i ₋) j′

          Y′≡Y : Y′ ≡ Y
          Y′≡Y = ⋁<-cong j′ λ i i<j′ → cong _₋ (x′ᵢ≡ (<ℕ-trans i<j′ (<ℕ-trans (n<1+n j′) (n<1+n j))))

          -- Lemma 5.43 with its hypotheses stated of p.
          apply-5-43 : ∀ p′ → x′ (suc j) ≡ p′
                     → ¬ p′ ₋ ≤ x′ 0 ₋ → p′ ₋ ≤ x′ j ₋ → p′ < t → t ≤ p′ ∨ κ p′ → t ≤ κ (x′ j′)
                     → ¬ t ≤ p′ ∨ (Y′ ∨ x′ j′) → ¬ (p′ B x′ 0) → ¬ ⋁< (λ i → x′ i ₋) j ≤ κ p′
          apply-5-43 _ refl = SubsC.Lemma543.lemma-5-43 sub′ bt′ t

          X′≰κp : ¬ ⋁< (λ i → x′ i ₋) j ≤ κ p
          X′≰κp = apply-5-43 p x′ⱼ₊₁≡p p₋≰q₀₋ (subst (λ z → p ₋ ≤ z ₋) (sym x′ⱼ≡) p₋≤qⱼ₋) p<t ∧-lowerˡ
                             (subst (λ z → t ≤ κ z) (sym x′ⱼ′≡) t≤κqⱼ′)
                             (λ le → t≰u (subst (t ≤_) (cong₂ (λ a b → p ∨ (a ∨ b)) Y′≡Y x′ⱼ′≡) le))
                             (λ pBq₀ → B→≰κ pBq₀ q₀≤κp)

      -- The result: j = k gives the second conclusion at once, and j < k is refuted above.
      result : (¬ p ₋ ≤ x 0 ₋) × (⋁< x k ≤ κ p)
      result = p₋≰q₀₋ , go S.j S.j≤k (subst (_≤ x S.j ₋) qₖ∧κp≡p₋ S.t≤qⱼ₋)
                           (λ i i<j → subst (λ z → ¬ z ≤ x i ₋) qₖ∧κp≡p₋ (S.j-least i i<j)) ⋁<S≤κp
        where
        go : ∀ j → j ≤ℕ k → p ₋ ≤ x j ₋ → (∀ i → i <ℕ j → ¬ p ₋ ≤ x i ₋) → ⋁< x j ≤ κ p → ⋁< x k ≤ κ p
        go zero     _   p₋≤q₀₋ _     _  = ⊥-elim (p₋≰q₀₋ p₋≤q₀₋)
        go (suc j′) j≤k p₋≤qⱼ₋ least le = split (m≤n⇒m<n∨m≡n j≤k)
          where
          split : suc j′ <ℕ k ⊎ suc j′ ≡ k → ⋁< x k ≤ κ p
          split (inj₂ e)   = subst (λ z → ⋁< x z ≤ κ p) e le
          split (inj₁ lt)  = decidable-stable (_ ≤? _) (JLess.contradiction j′ lt p₋≤qⱼ₋ least le)
```

#### Lemma 5.47

```agda
    -- The induction on the bound, with k = 0 excluded by q₀ ≤ κ(p) and q_k ≰ κ(p).
    lemma-5-47-bounded : ∀ b → Statement b
    lemma-5-47-bounded zero     zero     {x} _   sub bt hA₂ q₀≤κp _ = ⊥-elim (A→≰κ (proj₁ hA₂) q₀≤κp)
    lemma-5-47-bounded zero     (suc k₁) {x} ()
    lemma-5-47-bounded (suc b′) zero     {x} _   sub bt hA₂ q₀≤κp _ = ⊥-elim (A→≰κ (proj₁ hA₂) q₀≤κp)
    lemma-5-47-bounded (suc b′) (suc k₁) {x} k≤b sub bt hA₂ q₀≤κp ¬p₋<q₀₋ =
      Main.result b′ (lemma-5-47-bounded b′) k₁ k≤b sub bt hA₂ q₀≤κp ¬p₋<q₀₋

    -- Lemma 5.47: with q_k A₂ p, q₀ ≤ κ(p) and p₋ ≮ q₀₋, p₋ ≰ q₀₋ and ⋁ᵢ₍ₖ qᵢ ≤ κ(p).
    lemma-5-47 : ∀ {k x} (sub : Sub (suc k) x) (bt : BType k x) → x k A₂ x (suc k)
               → x 0 ≤ κ (x (suc k)) → ¬ (x (suc k) ₋ < x 0 ₋)
               → (¬ x (suc k) ₋ ≤ x 0 ₋) × (⋁< x k ≤ κ (x (suc k)))
    lemma-5-47 {k} = lemma-5-47-bounded k k ≤ℕ-refl
```
