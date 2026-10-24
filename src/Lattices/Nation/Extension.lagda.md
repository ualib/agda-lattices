---
layout: default
file: "src/Lattices/Nation/Extension.lagda.md"
title: "Lattices.Nation.Extension module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Lemmas 5.49 and 5.50: across an A₂ followed by a B

This is the [Lattices.Nation.Extension][] module of the [agda-lattices][]
library.

Lemmas 5.49 and 5.50 of [Freese, Ježek, and Nation (1995)][] (pp. 120 to 122)
prepare the extension of a B-type sequence through an `A₂` followed by `B`'s
(Lemma 5.51).  Lemma 5.49 holds in any S-lattice: if `p A₂ q B₁ r`, then
`p ≤ q ∨ r`; it is Lemma 5.39 for `a = q ∨ r`, `b = κ(q)` and `c = p`, whose
five alternatives are each refuted or each yield the conclusion, with (SD∨)
and (W).  Lemma 5.50 takes a subsequence `q₀, …, q_k, p₀, p₁` of a minimal
C-cycle with `k ≥ 1`, `q₀, …, q_k` a B-type sequence, `q_k A₂ p₀ B p₁`,
`q₀ ≤ κ(p₀)` and `p₀₋ ≮ q₀₋`, and concludes `⋁ᵢ≤ₖ qᵢ ≤ p₀ ∨ p₁`.  Supposing
otherwise, Lemmas 5.47 and 5.48 give `⋁ᵢ₍ₖ qᵢ ≤ κ(p₀)` and `p₀ = q_{k*}`, (W)
shows `p₁₋ ≰ p₀₋`, so `p₀ B₁ p₁` and Lemma 5.49 gives `q_k ≤ p₀ ∨ p₁`, hence
`q_k ≤ p₀ ∨ p₁₋`; and `a = q_k`, `a₀ = ⋁ᵢ≤ₖ qᵢ ∧ (p₀ ∨ p₁)`, `b = p₀₋ ∨ p₁₋`,
`b₀ = κ(p₀) ∧ (p₀ ∨ p₁)` form the configuration of Lemma 5.38, with `a₁` the
lower cover of `a₀`, which is join irreducible because it is a proper meet
(`meet-irr`{.AgdaFunction}).  Condition 5.38 (6) uses (SD∨) with two joinands
on the right (`sd∨-two`{.AgdaFunction}): `x ∨ y = x ∨ (z₁ ∨ z₂)` gives
`x ∨ y = x ∨ (y ∧ z₁) ∨ (y ∧ z₂)`, by two applications of the law.  Nation's
paper has the lemmas as its Lemma 3.7 and the claim `q_k ≤ p₀ ∨ p₁` of its
proof, with the same arguments.

The module checks in 1.9 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Extension where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; suc )
                                                   renaming ( _≤_ to _≤ℕ_ )
open import Data.Nat.Properties                    using ( n<1+n ; n≤1+n )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-trans to ≤ℕ-trans ; <-trans to <ℕ-trans
                                                            ; <-irrefl to <ℕ-irrefl )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType     as BTypeModule
import Lattices.Nation.Lemma547  as Lemma547Module
import Lattices.Nation.Lemma548  as Lemma548Module
open import Lattices.Nation.Configurations  using ( module Configurations )
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### Lemma 5.49

```agda
module Extension {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                 (laws : LatticeTableLaws _∧_ _∨_)
                 (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                 (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least )
  open Configurations laws w using ( Config₃₈ ; no-config₃₈ ; Config₃₉ ; no-config₃₉ ; meet-irr )
  module L547 = Lemma547Module.Lemma547 laws sd w
  module L548 = Lemma548Module.Lemma548 laws sd w

  -- (SD∨) with two joinands on the right: x ∨ y = x ∨ (z₁ ∨ z₂) gives x ∨ y = x ∨ ((y ∧ z₁) ∨ (y ∧ z₂)),
  -- by the law for x ∨ z₂ and then for x ∨ (y ∧ z₁).
  sd∨-two : ∀ x y z₁ z₂ → x ∨ y ≡ x ∨ (z₁ ∨ z₂) → x ∨ y ≡ x ∨ ((y ∧ z₁) ∨ (y ∧ z₂))
  sd∨-two x y z₁ z₂ e =
    ≤-antisym (∨-least ∨-upperˡ y≤) (∨-least ∨-upperˡ (∨-least (∧ˡ≤ ∨-upperʳ) (∧ˡ≤ ∨-upperʳ)))
    where
    z₁≤ : z₁ ≤ x ∨ y
    z₁≤ = ≤-trans (≤∨ʳ ∨-upperˡ) (≤-reflexive′ (sym e))

    z₂≤ : z₂ ≤ x ∨ y
    z₂≤ = ≤-trans (≤∨ʳ ∨-upperʳ) (≤-reflexive′ (sym e))

    y≤z₁z₂ : y ≤ x ∨ (z₁ ∨ z₂)
    y≤z₁z₂ = ≤-trans ∨-upperʳ (≤-reflexive′ e)

    eA : (x ∨ z₂) ∨ y ≡ (x ∨ z₂) ∨ (y ∧ z₁)
    eA = sd∨ (x ∨ z₂) y z₁
           (≤-antisym (∨-least ∨-upperˡ (≤-trans y≤z₁z₂ (∨-least (≤∨ˡ ∨-upperˡ) (∨-least ∨-upperʳ (≤∨ˡ ∨-upperʳ)))))
                      (∨-least ∨-upperˡ (≤-trans z₁≤ (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ))))

    x′ : Fin (suc n)
    x′ = x ∨ (y ∧ z₁)

    x′∨y≡ : x′ ∨ y ≡ x ∨ y
    x′∨y≡ = ≤-antisym (∨-least (∨-least ∨-upperˡ (∧ˡ≤ ∨-upperʳ)) ∨-upperʳ) (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ)

    x′∨z₂≡ : x′ ∨ z₂ ≡ x ∨ y
    x′∨z₂≡ = ≤-antisym (∨-least (∨-least ∨-upperˡ (∧ˡ≤ ∨-upperʳ)) z₂≤)
                       (≤-trans (≤-trans (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ) (≤-reflexive′ eA))
                                (∨-least (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ) (≤∨ˡ ∨-upperʳ)))

    eB : x′ ∨ y ≡ x′ ∨ (y ∧ z₂)
    eB = sd∨ x′ y z₂ (trans x′∨y≡ (sym x′∨z₂≡))

    y≤ : y ≤ x ∨ ((y ∧ z₁) ∨ (y ∧ z₂))
    y≤ = ≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ eB) (∨-least (∨-least ∨-upperˡ (≤∨ʳ ∨-upperˡ)) (≤∨ʳ ∨-upperʳ)))

  -- Lemma 5.49: if p A₂ q B₁ r, then p ≤ q ∨ r.
  lemma-5-49 : ∀ {p q r} → p A₂ q → q B₁ r → p ≤ q ∨ r
  lemma-5-49 {p} {q} {r} (pAq , p∧κq≡q₋) (qBr , r₋≰q) = decidable-stable (_ ≤? _) λ p≰ → no-config₃₉ (config p≰)
    where
    iq : HasOneLowerCover q
    iq = proj₁ (B-irr qBr)

    q≤p : q ≤ p
    q≤p = proj₁ (A→< pAq)

    p≤q∨κq : p ≤ q ∨ κ q
    p≤q∨κq = proj₂ (proj₂ (proj₂ pAq))

    q≤q₋∨r : q ≤ (q ₋) ∨ r
    q≤q₋∨r = proj₁ (proj₂ (proj₂ (proj₂ qBr)))

    r₋≤κq : r ₋ ≤ κ q
    r₋≤κq = B→₋≤κ qBr

    q₋≰r : ¬ q ₋ ≤ r
    q₋≰r le = B→≰ qBr (≤-trans q≤q₋∨r (∨-least le ≤-refl))

    r₋≤a∧b : r ₋ ≤ (q ∨ r) ∧ κ q
    r₋≤a∧b = ∧-greatest (≤∨ʳ (₋≤ r)) r₋≤κq

    q∧r≤q₋ : q ∧ r ≤ q ₋
    q∧r≤q₋ = <→≤₋′ ∧-lowerˡ λ e → B→≰ qBr (subst (_≤ r) e ∧-lowerʳ)

    -- Case (5): κ(q) ≤ q ∨ r ∨ p makes r ∨ p = r ∨ κ(q), so r ∨ p = r ∨ (p ∧ κ(q)) = r ∨ q₋ by (SD∨).
    from-5 : κ q ≤ (q ∨ r) ∨ p → p ≤ q ∨ r
    from-5 h = ≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨ r p (κ q) e))
                                         (∨-least ∨-upperʳ (≤-trans (≤-reflexive′ p∧κq≡q₋) (≤∨ˡ (₋≤ q)))))
      where
      e : r ∨ p ≡ r ∨ κ q
      e = ≤-antisym (∨-least ∨-upperˡ (≤-trans p≤q∨κq (∨-least (≤-trans q≤q₋∨r (∨-least (≤∨ʳ (₋≤κ q)) ∨-upperˡ)) ∨-upperʳ)))
                    (∨-least ∨-upperˡ (≤-trans h (∨-least (∨-least (≤∨ʳ q≤p) ∨-upperˡ) ∨-upperʳ)))

    -- Case (4): q ∨ r ≤ κ(q) ∨ p makes κ(q) ∨ q = κ(q) ∨ r, so κ(q) ∨ q = κ(q) ∨ (q ∧ r) ≤ κ(q) by (SD∨).
    e₄ : q ∨ r ≤ κ q ∨ p → κ q ∨ q ≡ κ q ∨ r
    e₄ h = ≤-antisym (∨-least ∨-upperˡ (≤-trans q≤q₋∨r (∨-monoˡ (₋≤κ q))))
                     (∨-least ∨-upperˡ (≤-trans (≤-trans ∨-upperʳ h)
                                                (∨-least ∨-upperˡ (≤-trans p≤q∨κq (≤-reflexive′ ∨-comm-law)))))

    -- Case (1): κ(q) ∧ (p ∨ r₋) ≤ q ∨ r, and (W) fails in every disjunct that does not give p ≤ q ∨ r.
    config : ¬ p ≤ q ∨ r → Config₃₉ (q ∨ r) (κ q) p
    config p≰ = record
      { c₁ = λ h → cases (W (κ q) (p ∨ (r ₋)) q r (≤-trans (∧-monoʳ (∨-monoʳ r₋≤a∧b)) h))
      ; c₂ = λ h → a≰κ iq (≤-trans (∧-greatest ∨-upperˡ (≤∨ˡ q≤p)) h)
      ; c₃ = λ h → r₋≰q (≤-trans (≤-trans (∧-greatest (≤-trans r₋≤a∧b h) r₋≤κq) (≤-reflexive′ p∧κq≡q₋)) (₋≤ q))
      ; c₄ = λ h → a≰κ iq (≤-trans (≤-trans ∨-upperʳ (≤-reflexive′ (sd∨ (κ q) q r (e₄ h))))
                                    (∨-least ≤-refl (≤-trans q∧r≤q₋ (₋≤κ q))))
      ; c₅ = λ h → p≰ (from-5 h) }
      where
      cases : (κ q ≤ q ∨ r ⊎ p ∨ (r ₋) ≤ q ∨ r) ⊎ (κ q ∧ (p ∨ (r ₋)) ≤ q ⊎ κ q ∧ (p ∨ (r ₋)) ≤ r) → ⊥
      cases (inj₁ (inj₁ h)) = p≰ (from-5 (≤∨ˡ h))
      cases (inj₁ (inj₂ h)) = p≰ (≤-trans ∨-upperˡ h)
      cases (inj₂ (inj₁ h)) = r₋≰q (≤-trans (∧-greatest r₋≤κq ∨-upperʳ) h)
      cases (inj₂ (inj₂ h)) = q₋≰r (≤-trans (∧-greatest (₋≤κ q) (≤∨ˡ (≤-trans (₋≤ q) q≤p))) h)
```

#### Lemma 5.50

```agda
  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 hiding ( k )
    open BT.InCycle 𝒞
    open L547.InCycle 𝒞 using ( lemma-5-47 )
    open L548.InCycle 𝒞 using ( lemma-5-48 )

    -- q₀, …, q_k, p₀, p₁ with k = j′ + 1, q_k A₂ p₀ B p₁, q₀ ≤ κ(p₀) and p₀₋ ≮ q₀₋, and ⋁ᵢ≤ₖ qᵢ ≰ p₀ ∨ p₁ supposed.
    module Lemma550 {j′ : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub (suc (suc (suc j′))) x) (bt : BType (suc j′) x)
                    (hA₂ : x (suc j′) A₂ x (suc (suc j′))) (hB : x (suc (suc j′)) B x (suc (suc (suc j′))))
                    (q₀≤κp₀ : x 0 ≤ κ (x (suc (suc j′)))) (¬p₀₋<q₀₋ : ¬ (x (suc (suc j′)) ₋ < x 0 ₋))
                    (¬⋁≤ : ¬ ⋁< x (suc (suc j′)) ≤ x (suc (suc j′)) ∨ x (suc (suc (suc j′)))) where
      open BType bt

      k : ℕ
      k = suc j′

      p₀ p₁ Q : Fin (suc n)
      p₀ = x (suc k)
      p₁ = x (suc (suc k))
      Q = ⋁< x (suc k)

      irr : ∀ {i} → i ≤ℕ suc (suc k) → HasOneLowerCover (x i)
      irr = Sub-irr sub

      i₁ : HasOneLowerCover p₁
      i₁ = irr ≤ℕ-refl

      i₀ : HasOneLowerCover p₀
      i₀ = irr (n≤1+n (suc k))

      k≤l : k ≤ℕ suc (suc k)
      k≤l = ≤ℕ-trans (n≤1+n k) (n≤1+n (suc k))

      iₖ : HasOneLowerCover (x k)
      iₖ = irr k≤l

      j′≤l : j′ ≤ℕ suc (suc k)
      j′≤l = ≤ℕ-trans (n≤1+n j′) k≤l

      iⱼ′ : HasOneLowerCover (x j′)
      iⱼ′ = irr j′≤l

      -- Lemmas 5.47 and 5.48 for q₀, …, q_k, p₀.
      subₚ : Sub (suc k) x
      subₚ = Sub-prefix sub (n≤1+n (suc k))

      ⋁<ₖ≤κp₀ : ⋁< x k ≤ κ p₀
      ⋁<ₖ≤κp₀ = proj₂ (lemma-5-47 subₚ bt hA₂ q₀≤κp₀ ¬p₀₋<q₀₋)

      p₀≡qₖ₋ : p₀ ≡ x k ₋
      p₀≡qₖ₋ = lemma-5-48 subₚ bt hA₂ q₀≤κp₀ ¬p₀₋<q₀₋

      -- Consequences of q_k A₂ p₀ and of p₀ B p₁.
      p₀<qₖ : p₀ < x k
      p₀<qₖ = A→< (proj₁ hA₂)

      p₀≤κqₖ : p₀ ≤ κ (x k)
      p₀≤κqₖ = subst (_≤ κ (x k)) (sym p₀≡qₖ₋) (₋≤κ (x k))

      p₀≰p₁ : ¬ p₀ ≤ p₁
      p₀≰p₁ = B→≰ hB

      p₀≤p₀₋∨p₁ : p₀ ≤ (p₀ ₋) ∨ p₁
      p₀≤p₀₋∨p₁ = proj₁ (proj₂ (proj₂ (proj₂ hB)))

      p₀≰p₀₋∨p₁₋ : ¬ p₀ ≤ (p₀ ₋) ∨ (p₁ ₋)
      p₀≰p₀₋∨p₁₋ = proj₂ (proj₂ (proj₂ (proj₂ hB)))

      p₁₋≤κp₀ : p₁ ₋ ≤ κ p₀
      p₁₋≤κp₀ = B→₋≤κ hB

      p₀≤κp₁ : p₀ ≤ κ p₁
      p₀≤κp₁ = B→≤κ hB

      p₁≰κp₀ : ¬ p₁ ≤ κ p₀
      p₁≰κp₀ = B→≰κ hB

      p₀₋≰p₁₋ : ¬ p₀ ₋ ≤ p₁ ₋
      p₀₋≰p₁₋ le = p₀≰p₁ (≤-trans p₀≤p₀₋∨p₁ (∨-least (≤-trans le (₋≤ p₁)) ≤-refl))

      -- The first observation: q_k ≤ p₀ ∨ p₁ implies q_k ≤ p₀ ∨ p₁₋, by the free star principle and Lemma 2.57.
      step1 : x k ≤ p₀ ∨ p₁ → x k ≤ p₀ ∨ (p₁ ₋)
      step1 le = subst (λ z → x k ≤ z ∨ (p₁ ₋)) (sym p₀≡qₖ₋) (≰κ→ iₖ p₁₋≰κqₖ)
        where
        p₁≰κqₖ : ¬ p₁ ≤ κ (x k)
        p₁≰κqₖ h = a≰κ iₖ (≤-trans le (∨-least p₀≤κqₖ h))

        p₁₋≰κqₖ : ¬ p₁ ₋ ≤ κ (x k)
        p₁₋≰κqₖ h = p₁≰κqₖ (Sub-freeStar′ sub k≤l ≤ℕ-refl (λ e → <ℕ-irrefl e (<ℕ-trans (n<1+n k) (n<1+n (suc k))))
                                          (λ e → <ℕ-irrefl (sym e) (n<1+n (suc k))) (λ { (_ , ()) }) h)

      -- p₁₋ ≰ p₀₋: otherwise (W) on p₀ = q_k ∧ (p₀ ∨ q_{k-1}) ≤ p₀₋ ∨ p₁ fails in every disjunct.
      p₁₋≰p₀₋ : ¬ p₁ ₋ ≤ p₀ ₋
      p₁₋≰p₀₋ le = cases (W (x k) (p₀ ∨ x j′) (p₀ ₋) p₁ (≤-trans meet≤p₀ p₀≤p₀₋∨p₁))
        where
        meet≤p₀ : x k ∧ (p₀ ∨ x j′) ≤ p₀
        meet≤p₀ = ≤-trans (∧-monoʳ (∨-least p₀≤κqₖ (B2 (n<1+n j′) ≤ℕ-refl)))
                          (≤-trans (≤-reflexive′ (a∧κ iₖ)) (≤-reflexive′ (sym p₀≡qₖ₋)))

        p₀≤meet : p₀ ≤ x k ∧ (p₀ ∨ x j′)
        p₀≤meet = ∧-greatest (proj₁ p₀<qₖ) ∨-upperˡ

        p₀≤κqⱼ′ : p₀ ≤ κ (x j′)
        p₀≤κqⱼ′ = subst (_≤ κ (x j′)) (sym p₀≡qₖ₋) (B3 ≤ℕ-refl)

        p₁≤κqⱼ′ : p₁ ≤ κ (x j′)
        p₁≤κqⱼ′ = Sub-freeStar′ sub j′≤l ≤ℕ-refl (λ e → <ℕ-irrefl e (<ℕ-trans (n<1+n j′) (<ℕ-trans (n<1+n k) (n<1+n (suc k)))))
                                (λ e → <ℕ-irrefl (sym e) (<ℕ-trans (n<1+n k) (n<1+n (suc k)))) (λ { (_ , ()) })
                                (≤-trans le (≤-trans (₋≤ p₀) p₀≤κqⱼ′))

        cases : (x k ≤ (p₀ ₋) ∨ p₁ ⊎ p₀ ∨ x j′ ≤ (p₀ ₋) ∨ p₁) ⊎ (x k ∧ (p₀ ∨ x j′) ≤ p₀ ₋ ⊎ x k ∧ (p₀ ∨ x j′) ≤ p₁) → ⊥
        cases (inj₁ (inj₁ h)) =
          proj₂ p₀<qₖ (≤-antisym (proj₁ p₀<qₖ) (≤-trans (step1 (≤-trans h (∨-monoˡ (₋≤ p₀)))) (∨-least ≤-refl (≤-trans le (₋≤ p₀)))))
        cases (inj₁ (inj₂ h)) = a≰κ iⱼ′ (≤-trans (≤-trans ∨-upperʳ h) (∨-least (≤-trans (₋≤ p₀) p₀≤κqⱼ′) p₁≤κqⱼ′))
        cases (inj₂ (inj₁ h)) = proj₂ i₀ (≤-antisym (₋≤ p₀) (≤-trans p₀≤meet h))
        cases (inj₂ (inj₂ h)) = p₀≰p₁ (≤-trans p₀≤meet h)

      -- Hence p₀ B₁ p₁, and Lemma 5.49 gives q_k ≤ p₀ ∨ p₁, so q_k ≤ p₀ ∨ p₁₋.
      p₁₋≰p₀ : ¬ p₁ ₋ ≤ p₀
      p₁₋≰p₀ le = p₁₋≰p₀₋ (<→≤₋′ le λ e → p₀≰p₁ (≤-trans (≤-reflexive′ (sym e)) (₋≤ p₁)))

      qₖ≤p₀∨p₁ : x k ≤ p₀ ∨ p₁
      qₖ≤p₀∨p₁ = lemma-5-49 hA₂ (hB , p₁₋≰p₀)

      qₖ≤p₀∨p₁₋ : x k ≤ p₀ ∨ (p₁ ₋)
      qₖ≤p₀∨p₁₋ = step1 qₖ≤p₀∨p₁

      -- ⋁ᵢ₍ₖ qᵢ ∨ p₀ lies below κ(q_k), by (B2) and p₀ = q_{k*}.
      X : Fin (suc n)
      X = ⋁< x k ∨ p₀

      X≤κqₖ : X ≤ κ (x k)
      X≤κqₖ = ∨-least (⋁<-least x λ i i<k → B2 i<k ≤ℕ-refl) p₀≤κqₖ

      -- A joinand z of ⋁ᵢ≤ₖ qᵢ ∨ z with q_k ≤ p₀ ∨ z: (SD∨) on X ∨ q_k = X ∨ z, and q_k ∧ z ≤ p₀, put q_k below κ(q_k).
      absorb : ∀ z → z ≤ Q → x k ≤ p₀ ∨ z → ¬ x k ≤ z → ⊥
      absorb z z≤Q qₖ≤p₀∨z qₖ≰z =
        a≰κ iₖ (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨ X (x k) z e)) (∨-least X≤κqₖ (≤-trans qₖ∧z≤p₀ p₀≤κqₖ))))
        where
        e : X ∨ x k ≡ X ∨ z
        e = ≤-antisym (∨-least ∨-upperˡ (≤-trans qₖ≤p₀∨z (∨-least (≤∨ˡ ∨-upperʳ) ∨-upperʳ)))
                      (∨-least ∨-upperˡ (≤-trans z≤Q (∨-least (≤∨ˡ ∨-upperˡ) ∨-upperʳ)))

        qₖ∧z≤p₀ : x k ∧ z ≤ p₀
        qₖ∧z≤p₀ = subst (x k ∧ z ≤_) (sym p₀≡qₖ₋) (<→≤₋′ ∧-lowerˡ λ e′ → qₖ≰z (subst (_≤ z) e′ ∧-lowerʳ))

      -- p₁ ≰ ⋁ᵢ≤ₖ qᵢ, as p₀ ≰ p₁; and p₁₋ ≰ ⋁ᵢ≤ₖ qᵢ likewise, as p₀ ≰ p₀₋ ∨ p₁₋.
      p₁≰Q : ¬ p₁ ≤ Q
      p₁≰Q le = absorb p₁ le qₖ≤p₀∨p₁ λ h → p₀≰p₁ (≤-trans (proj₁ p₀<qₖ) h)

      p₁₋≰Q : ¬ p₁ ₋ ≤ Q
      p₁₋≰Q le = absorb (p₁ ₋) le qₖ≤p₀∨p₁₋ λ h → p₀≰p₀₋∨p₁₋ (≤-trans (proj₁ p₀<qₖ) (≤∨ʳ h))

      -- The configuration of Lemma 5.38.
      a a₀ a₁ b b₀ : Fin (suc n)
      a = x k
      a₀ = Q ∧ (p₀ ∨ p₁)
      a₁ = a₀ ₋
      b = (p₀ ₋) ∨ (p₁ ₋)
      b₀ = κ p₀ ∧ (p₀ ∨ p₁)

      a≤a₀ : a ≤ a₀
      a≤a₀ = ∧-greatest (⋁<-upper x (n<1+n k)) qₖ≤p₀∨p₁

      -- a ≠ a₀: otherwise (W) on a₀ = ⋁ᵢ≤ₖ qᵢ ∧ (p₀ ∨ p₁) ≤ p₀ ∨ p₁₋ fails in every disjunct.
      a≢a₀ : a ≢ a₀
      a≢a₀ e = cases (W Q (p₀ ∨ p₁) p₀ (p₁ ₋) (≤-trans (≤-reflexive′ (sym e)) qₖ≤p₀∨p₁₋))
        where
        cases : (Q ≤ p₀ ∨ (p₁ ₋) ⊎ p₀ ∨ p₁ ≤ p₀ ∨ (p₁ ₋)) ⊎ (a₀ ≤ p₀ ⊎ a₀ ≤ p₁ ₋) → ⊥
        cases (inj₁ (inj₁ h)) = ¬⋁≤ (≤-trans h (∨-monoʳ (₋≤ p₁)))
        cases (inj₁ (inj₂ h)) = a≰κ i₁ (≤-trans ∨-upperʳ (≤-trans h (∨-least p₀≤κp₁ (₋≤κ p₁))))
        cases (inj₂ (inj₁ h)) = proj₂ p₀<qₖ (≤-antisym (proj₁ p₀<qₖ) (≤-trans a≤a₀ h))
        cases (inj₂ (inj₂ h)) = p₀≰p₁ (≤-trans (proj₁ p₀<qₖ) (≤-trans a≤a₀ (≤-trans h (₋≤ p₁))))

      a<a₀ : a < a₀
      a<a₀ = a≤a₀ , a≢a₀

      -- a₀ is a proper meet, hence join irreducible, and a₁ = a₀₋ is its lower cover above a.
      ia₀ : HasOneLowerCover a₀
      ia₀ = meet-irr ⊥≢a₀ (∧-lowerˡ , λ e → ¬⋁≤ (≤-trans (≤-reflexive′ (sym e)) ∧-lowerʳ))
                          (∧-lowerʳ , λ e → p₁≰Q (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sym e)) ∧-lowerˡ))) refl
        where
        ⊥≢a₀ : ⊥ᴸ ≢ a₀
        ⊥≢a₀ e = proj₂ iₖ (≤-antisym (₋≤ (x k)) (≤-trans (≤-trans a≤a₀ (≤-reflexive′ (sym e))) (⊥ᴸ-least _)))

      a≤a₁ : a ≤ a₁
      a≤a₁ = <→≤₋ a<a₀

      -- 5.38 (6): p₀ ∨ p₁ ≤ a₀ ∨ b₀ makes p₀ ∨ p₁ = p₀ ∨ (a₀ ∨ b₀), so by (SD∨) with two joinands
      -- p₀ ∨ p₁ = p₀ ∨ (p₁ ∧ a₀) ∨ (p₁ ∧ b₀) ≤ p₀ ∨ p₁₋ ≤ κ(p₁).
      from-6 : p₀ ∨ p₁ ≤ a₀ ∨ b₀ → ⊥
      from-6 h = a≰κ i₁ (≤-trans ∨-upperʳ (≤-trans (≤-reflexive′ (sd∨-two p₀ p₁ a₀ b₀ e))
                                                   (∨-least p₀≤κp₁ (∨-least (≤-trans p₁∧a₀≤p₁₋ (₋≤κ p₁)) (≤-trans p₁∧b₀≤p₁₋ (₋≤κ p₁))))))
        where
        e : p₀ ∨ p₁ ≡ p₀ ∨ (a₀ ∨ b₀)
        e = ≤-antisym (∨-least ∨-upperˡ (≤-trans ∨-upperʳ (≤-trans h ∨-upperʳ))) (∨-least ∨-upperˡ (∨-least ∧-lowerʳ ∧-lowerʳ))

        p₁∧a₀≤p₁₋ : p₁ ∧ a₀ ≤ p₁ ₋
        p₁∧a₀≤p₁₋ = <→≤₋′ ∧-lowerˡ λ e′ → p₁≰Q (≤-trans (subst (_≤ a₀) e′ ∧-lowerʳ) ∧-lowerˡ)

        p₁∧b₀≤p₁₋ : p₁ ∧ b₀ ≤ p₁ ₋
        p₁∧b₀≤p₁₋ = <→≤₋′ ∧-lowerˡ λ e′ → p₁≰κp₀ (≤-trans (subst (_≤ b₀) e′ ∧-lowerʳ) ∧-lowerˡ)

      config : Config₃₈ a a₀ a₁ b b₀
      config = record
        { b-red  = λ { (b₋≤b , b₋≢b) → b₋≢b (≤-antisym b₋≤b (∨-least (<→≤₋ p₀₋<b) (<→≤₋ p₁₋<b))) }
        ; a-cond = inj₂ (iₖ , ≤-trans qₖ≤p₀∨p₁₋ (∨-least (≤∨ˡ (≤-reflexive′ p₀≡qₖ₋)) (≤∨ʳ ∨-upperʳ)))
        ; a≤a₁   = a≤a₁
        ; a₁⋖a₀  = ₋⋖ ia₀
        ; b≤b₀   = ∧-greatest (∨-least (₋≤κ p₀) p₁₋≤κp₀) (∨-least (≤∨ˡ (₋≤ p₀)) (≤∨ʳ (₋≤ p₁)))
        ; a≰b₀   = a≰b₀
        ; b≰a₀   = b≰a₀
        ; a₀≰    = λ h → cases₆ (W Q (p₀ ∨ p₁) a₁ b₀ h)
        ; b₀≰    = λ h → cases₇ (W (κ p₀) (p₀ ∨ p₁) a₁ (p₁ ₋) (≤-trans h a₁∨b≤)) }
        where
        p₀₋<b : p₀ ₋ < b
        p₀₋<b = ∨-upperˡ , λ e → p₁₋≰p₀₋ (≤ᵈ→ (sym e))

        p₁₋<b : p₁ ₋ < b
        p₁₋<b = ∨-upperʳ , λ e → p₀₋≰p₁₋ (≤ᵈ→ (sym (trans e ∨-comm-law)))

        a≰b₀ : ¬ a ≤ b₀
        a≰b₀ h = a≰κ i₀ (≤-trans (proj₁ p₀<qₖ) (≤-trans h ∧-lowerˡ))

        -- 5.38 (5): b ≤ a₀ would put p₁₋ below ⋁ᵢ≤ₖ qᵢ.
        b≰a₀ : ¬ b ≤ a₀
        b≰a₀ h = p₁₋≰Q (≤-trans ∨-upperʳ (≤-trans h ∧-lowerˡ))

        cases₆ : (Q ≤ a₁ ∨ b₀ ⊎ p₀ ∨ p₁ ≤ a₁ ∨ b₀) ⊎ (a₀ ≤ a₁ ⊎ a₀ ≤ b₀) → ⊥
        cases₆ (inj₁ (inj₁ h)) = ¬⋁≤ (≤-trans h (∨-least (≤-trans (₋≤ a₀) ∧-lowerʳ) ∧-lowerʳ))
        cases₆ (inj₁ (inj₂ h)) = from-6 (≤-trans h (∨-monoˡ (₋≤ a₀)))
        cases₆ (inj₂ (inj₁ h)) = proj₂ ia₀ (≤-antisym (₋≤ a₀) h)
        cases₆ (inj₂ (inj₂ h)) = a≰b₀ (≤-trans a≤a₀ h)

        -- 5.38 (7): a₁ ∨ b = a₁ ∨ p₁₋, as p₀₋ < a ≤ a₁.
        a₁∨b≤ : a₁ ∨ b ≤ a₁ ∨ (p₁ ₋)
        a₁∨b≤ = ∨-least ∨-upperˡ (∨-least (≤∨ˡ (≤-trans (₋≤ p₀) (≤-trans (proj₁ p₀<qₖ) a≤a₁))) ∨-upperʳ)

        cases₇ : (κ p₀ ≤ a₁ ∨ (p₁ ₋) ⊎ p₀ ∨ p₁ ≤ a₁ ∨ (p₁ ₋)) ⊎ (b₀ ≤ a₁ ⊎ b₀ ≤ p₁ ₋) → ⊥
        cases₇ (inj₁ (inj₁ h)) =
          ¬⋁≤ (∨-least (≤-trans ⋁<ₖ≤κp₀ (≤-trans h (∨-least (≤-trans (₋≤ a₀) ∧-lowerʳ) (≤∨ʳ (₋≤ p₁))))) qₖ≤p₀∨p₁)
        cases₇ (inj₁ (inj₂ h)) =
          from-6 (≤-trans h (∨-least (≤∨ˡ (₋≤ a₀)) (≤∨ʳ (∧-greatest p₁₋≤κp₀ (≤∨ʳ (₋≤ p₁))))))
        cases₇ (inj₂ (inj₁ h)) = b≰a₀ (≤-trans (∧-greatest (∨-least (₋≤κ p₀) p₁₋≤κp₀) (∨-least (≤∨ˡ (₋≤ p₀)) (≤∨ʳ (₋≤ p₁))))
                                                (≤-trans h (₋≤ a₀)))
        cases₇ (inj₂ (inj₂ h)) = p₀₋≰p₁₋ (≤-trans (∧-greatest (₋≤κ p₀) (≤∨ˡ (₋≤ p₀))) h)

      contradiction : ⊥
      contradiction = no-config₃₈ config

    -- Lemma 5.50: with q_k A₂ p₀ B p₁, k ≥ 1, q₀ ≤ κ(p₀) and p₀₋ ≮ q₀₋, ⋁ᵢ≤ₖ qᵢ ≤ p₀ ∨ p₁.
    lemma-5-50 : ∀ {j′ x} (sub : Sub (suc (suc (suc j′))) x) (bt : BType (suc j′) x)
               → x (suc j′) A₂ x (suc (suc j′)) → x (suc (suc j′)) B x (suc (suc (suc j′)))
               → x 0 ≤ κ (x (suc (suc j′))) → ¬ (x (suc (suc j′)) ₋ < x 0 ₋)
               → ⋁< x (suc (suc j′)) ≤ x (suc (suc j′)) ∨ x (suc (suc (suc j′)))
    lemma-5-50 sub bt hA₂ hB q₀≤κp₀ ¬p₀₋<q₀₋ =
      decidable-stable (_ ≤? _) (Lemma550.contradiction sub bt hA₂ hB q₀≤κp₀ ¬p₀₋<q₀₋)
```
