---
layout: default
file: "src/Lattices/Nation/Lemma551.lagda.md"
title: "Lattices.Nation.Lemma551 module"
date: "2026-10-22"
author: "the agda-algebras development team"
check-cost: heavy
---

### Lemma 5.51: extending a B-type sequence through an A₂ and a run of B's

This is the [Lattices.Nation.Lemma551][] module of the [agda-lattices][]
library.

Lemma 5.51 of [Freese, Ježek, and Nation (1995)][] (pp. 122 and 123), the
critical lemma about B-type sequences, takes blocks `r_{i0} B … B r_{ikᵢ}`
(`i = 1, …, n`) of a minimal C-cycle in an S-lattice joined by
`r_{ikᵢ} A₂ r_{i+1,0}`, with `r₁₀ ≤ κ(r_{i0})` and `r_{i0*} ≮ r_{10*}` for
`i > 1`, and concludes that the sequence obtained by dropping the last member
of every block but the last is a B-type sequence.  Its proof is an induction
on `n` whose step extends the sequence of the first `n - 1` blocks by the last
block, and this module proves that step, for a *kept chain*: the flat family
`x` of all the members (a subsequence of the cycle, read at the indices up to
`N`), a reindexing `keep` naming the kept members, the B-type property of
`x ∘ keep`, and at each dropped member a *junction* (`Boundary`{.AgdaRecord}),
which records the B and the A₂ around it, the B-type property of the chain
kept up to it with the dropped member included, and the two hypotheses on the
member after it.  The step (`Extend`{.AgdaModule}) takes a chain whose last
step is a B, a further block `p₀, …, p_m` with `q_s A₂ p₀` (`q_s` the chain's
last member), `q₀ ≤ κ(p₀)` and `p₀₋ ≮ q₀₋`, and returns the chain
`q₀, …, q_{s-1}, p₀, …, p_m` with its junction at `q_{s-1}`.  Conditions
(B1) to (B3) and (B2) and (B4) between the parts follow the book: Lemmas 5.47
and 5.48 for `q₀, …, q_s, p₀`, Lemma 2.63 along the block, and for (B4) the
largest index `i` with `p_l ≤ κ(qᵢ)`, Lemma 5.50 for `q₀, …, q_s, p₀, p₁`, the
junction after `qᵢ` (or `q_s A₂ p₀` itself when `i = s - 1`) with Lemmas
5.47 and 5.48 for `q₀, …, qᵢ, u, v`, (W) on `u ∧ (v ∨ p_l) ≤ v₋ ∨ p_{l*}`, and
Lemma 5.43 for `q₀, …, qᵢ, u, v` with `t = κ(v)* ∧ (q_{i*} ∨ p_l)`.  The
book's exclusion of `qᵢ B₂ u` through the block structure is replaced by the
same (B3) and (B4) of the chain kept up to `u` when `i ≥ 1`, and by the
hypothesis `v₋ ≮ q₀₋` when `i = 0`.  Nation's paper states the lemma as its
Lemma 3.8, in this extension form.

The module checks in 4.9 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).  Its cost puts it under
the barrel policy: the front matter carries `check-cost: heavy`, and no barrel
imports it.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Lemma551 where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n ; m≤n⇒m<n∨m≡n ; m≤n+m ; m+n∸n≡m
                                                         ; m∸n+n≡m ; ≰⇒> ; +-cancelʳ-≤ ; +-monoˡ-< ; +-monoˡ-≤ ; ∸-monoˡ-≤
                                                         ; 1+n≢n ; suc-injective )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-trans to ≤ℕ-trans ; <-trans to <ℕ-trans
                                                            ; <-≤-trans to <ℕ-≤-trans ; ≤-<-trans to ≤ℕ-<-trans
                                                            ; <-irrefl to <ℕ-irrefl ; _≤?_ to _≤ℕ?_ )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function.Base                          using ( _∘_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.BType         as BTypeModule
import Lattices.Nation.Extension     as ExtensionModule
import Lattices.Nation.Lemma547      as Lemma547Module
import Lattices.Nation.Lemma548      as Lemma548Module
import Lattices.Nation.Subsequences  as SubsequencesModule
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### Kept chains

```agda
module Lemma551 {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( W ; ⋁< ; ⋁<-upper ; ⋁<-least ; W-⋁< ; B→κ< ; greatest-index
                ; after ; after-≤ ; after-suc ; after-+ ; after-mono ; after-bound )
  module L547 = Lemma547Module.Lemma547 laws sd w
  module L548 = Lemma548Module.Lemma548 laws sd w
  module Subs = SubsequencesModule.Subsequences laws sd w
  module Ext  = ExtensionModule.Extension laws sd w

  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 hiding ( k )
    open BT.InCycle 𝒞
    open L547.InCycle 𝒞 using ( lemma-5-47 )
    open L548.InCycle 𝒞 using ( lemma-5-48 )
    open Ext.InCycle 𝒞 using ( lemma-5-50 )
    module SubsC = Subs.InCycle 𝒞

    -- A B-type sequence q₀, …, q_i, u with u₋ ≤ q_i, i.e. q_i B₂ u: excluded by (B3) and (B4) when i ≥ 1,
    -- and reduced to u₋ ≤ q₀₋ when i = 0.
    no-B₂ : ∀ i {z : ℕ → Fin (suc n)} → BType (suc i) z → z (suc i) ₋ ≢ z i → ¬ z (suc i) ₋ ≤ z 0 ₋
          → ¬ z (suc i) ₋ ≤ z i
    no-B₂ zero     bt′ ne h0 le = h0 (<→≤₋′ le ne)
    no-B₂ (suc i₁) bt′ ne _  le = BType.B4 bt′ ≤ℕ-refl ≤ℕ-refl (≤-trans (<→≤₋′ le ne) (BType.B3 bt′ (n≤1+n (suc i₁))))

    -- The flat subsequence x of all the members, read at the indices up to N.
    module Flat {N : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub N x) where

      -- A junction of a kept chain at its index i: the dropped member u = x (suc (keep i)) and the member
      -- v = x (suc (suc (keep i))) after it, with the chain kept up to u a B-type sequence.
      record Boundary (keep : ℕ → ℕ) (i : ℕ) : Type where
        field
          u-step  : x (keep i) B x (suc (keep i))
          v-step  : x (suc (keep i)) A₂ x (suc (suc (keep i)))
          bt-u    : BType (suc i) (x ∘ after keep i (suc (keep i)))
          q₀≤κv   : x 0 ≤ κ (x (suc (suc (keep i))))
          ¬v₋<q₀₋ : ¬ (x (suc (suc (keep i))) ₋ < x 0 ₋)

      -- A kept chain q = x ∘ keep, read at the indices up to s: a B-type sequence whose consecutive members
      -- are consecutive in x and B-related, or two apart with a junction between them.
      record Chain (s : ℕ) (keep : ℕ → ℕ) : Type where
        field
          keep0 : keep 0 ≡ 0
          mono  : ∀ {i j} → i <ℕ j → j ≤ℕ s → keep i <ℕ keep j
          bound : ∀ {i} → i ≤ℕ s → keep i ≤ℕ N
          bt    : BType s (x ∘ keep)
          steps : ∀ i → i <ℕ s → (keep (suc i) ≡ suc (keep i) × x (keep i) B x (keep (suc i)))
                                ⊎ (keep (suc i) ≡ suc (suc (keep i)) × Boundary keep i)

      -- A junction is preserved by a reindexing that agrees up to its index.
      Boundary-resp : ∀ {k₁ k₂ i} → (∀ t → t ≤ℕ i → k₁ t ≡ k₂ t) → Boundary k₁ i → Boundary k₂ i
      Boundary-resp {k₁} {k₂} {i} f bd = record
        { u-step  = subst (λ z → x z B x (suc z)) eᵢ (Boundary.u-step bd)
        ; v-step  = subst (λ z → x (suc z) A₂ x (suc (suc z))) eᵢ (Boundary.v-step bd)
        ; bt-u    = BType-cong ≤ℕ-refl agree (Boundary.bt-u bd)
        ; q₀≤κv   = subst (λ z → x 0 ≤ κ (x (suc (suc z)))) eᵢ (Boundary.q₀≤κv bd)
        ; ¬v₋<q₀₋ = subst (λ z → ¬ (x (suc (suc z)) ₋ < x 0 ₋)) eᵢ (Boundary.¬v₋<q₀₋ bd) }
        where
        eᵢ : k₁ i ≡ k₂ i
        eᵢ = f i ≤ℕ-refl

        agree : ∀ t → t ≤ℕ suc i → x (after k₂ i (suc (k₂ i)) t) ≡ x (after k₁ i (suc (k₁ i)) t)
        agree t t≤si = cong x (cases (m≤n⇒m<n∨m≡n t≤si))
          where
          cases : t <ℕ suc i ⊎ t ≡ suc i → after k₂ i (suc (k₂ i)) t ≡ after k₁ i (suc (k₁ i)) t
          cases (inj₁ t<si) = trans (after-≤ k₂ i (suc (k₂ i)) (s≤s⁻¹ t<si)) (trans (sym (f t (s≤s⁻¹ t<si))) (sym (after-≤ k₁ i (suc (k₁ i)) (s≤s⁻¹ t<si))))
          cases (inj₂ e)    = subst (λ z → after k₂ i (suc (k₂ i)) z ≡ after k₁ i (suc (k₁ i)) z) (sym e)
                                    (trans (after-suc k₂ i (suc (k₂ i))) (trans (cong suc (sym eᵢ)) (sym (after-suc k₁ i (suc (k₁ i))))))

      -- A run of B's from the first member is a kept chain with the identity reindexing (Lemma 5.41).
      chain-of-Bs : ∀ s → s ≤ℕ N → (∀ i → i <ℕ s → x i B x (suc i)) → Chain s (λ t → t)
      chain-of-Bs s s≤N Bs = record
        { keep0 = refl
        ; mono  = λ i<j _ → i<j
        ; bound = λ i≤s → ≤ℕ-trans i≤s s≤N
        ; bt    = Lemma541.lemma-5-41 (Sub-prefix sub s≤N) (λ {i} si≤s → Bs i si≤s)
        ; steps = λ i i<s → inj₁ (refl , Bs i i<s) }
```

#### The extension step

```agda
      module Extend {s′ : ℕ} {keep : ℕ → ℕ} (ch : Chain (suc s′) keep) (direct : keep (suc s′) ≡ suc (keep s′))
                    (m : ℕ) (0<m : 0 <ℕ m) (block : m + suc (keep (suc s′)) ≤ℕ N)
                    (hA₂ : x (keep (suc s′)) A₂ x (suc (keep (suc s′))))
                    (Bs : ∀ l → l <ℕ m → x (l + suc (keep (suc s′))) B x (suc l + suc (keep (suc s′))))
                    (q₀≤κp₀ : x 0 ≤ κ (x (suc (keep (suc s′)))))
                    (¬p₀₋<q₀₋ : ¬ (x (suc (keep (suc s′))) ₋ < x 0 ₋)) where
        open Chain ch
        open BType bt

        S c₀ L′ : ℕ
        S = suc s′
        c₀ = suc (keep S)
        L′ = m + S

        q p : ℕ → Fin (suc n)
        q t = x (keep t)
        p l = x (l + c₀)

        keep′ : ℕ → ℕ
        keep′ = after keep s′ c₀

        y : ℕ → Fin (suc n)
        y t = x (keep′ t)

        u p₀ : Fin (suc n)
        u = q S
        p₀ = p 0

        -- Reading the families.
        y-q : ∀ {t} → t ≤ℕ s′ → y t ≡ q t
        y-q t≤s′ = cong x (after-≤ keep s′ c₀ t≤s′)

        y-p : ∀ l → y (l + S) ≡ p l
        y-p l = cong x (after-+ keep s′ c₀ l)

        y-p₀ : y S ≡ p₀
        y-p₀ = cong x (after-suc keep s′ c₀)

        q₀≡x₀ : q 0 ≡ x 0
        q₀≡x₀ = cong x keep0

        keep<c₀ : ∀ {t} → t ≤ℕ s′ → keep t <ℕ c₀
        keep<c₀ t≤s′ = <ℕ-trans (mono (s≤s t≤s′) ≤ℕ-refl) (n<1+n (keep S))

        -- The old chain, its last step q_{s′} B u, and the block as subsequences.
        sub-q : Sub S q
        sub-q = Sub-restrict sub keep mono bound

        qₛ′Bu : q s′ B u
        qₛ′Bu = from (steps s′ ≤ℕ-refl)
          where
          from : (keep S ≡ suc (keep s′) × x (keep s′) B x (keep S)) ⊎ (keep S ≡ suc (suc (keep s′)) × Boundary keep s′) → q s′ B u
          from (inj₁ (_ , h)) = h
          from (inj₂ (e , _)) = ⊥-elim (1+n≢n (suc-injective (trans (sym e) direct)))

        sub-p : Sub m p
        sub-p = Sub-restrict sub (_+ c₀) (λ i<j _ → +-monoˡ-< c₀ i<j) λ l≤m → ≤ℕ-trans (+-monoˡ-≤ c₀ l≤m) block

        bt-p : BType m p
        bt-p = Lemma541.lemma-5-41 sub-p (λ {l} sl≤m → Bs l sl≤m)

        module BP = BType bt-p

        -- κ increases along the block (Lemma 2.63).
        κp₀≤κp : ∀ l → l ≤ℕ m → κ p₀ ≤ κ (p l)
        κp₀≤κp zero    _    = ≤-refl
        κp₀≤κp (suc l) sl≤m = ≤-trans (κp₀≤κp l (≤ℕ-trans (n≤1+n l) sl≤m)) (proj₁ (B→κ< (Bs l sl≤m)))

        -- q₀, …, q_S, p₀, …, p_m as the family x ∘ ext.
        ext : ℕ → ℕ
        ext = after keep S c₀

        ext-q : ∀ {t} → t ≤ℕ S → x (ext t) ≡ q t
        ext-q t≤S = cong x (after-≤ keep S c₀ t≤S)

        ext-p₀ : x (ext (suc S)) ≡ p₀
        ext-p₀ = cong x (after-suc keep S c₀)

        ext-p₁ : x (ext (suc (suc S))) ≡ p 1
        ext-p₁ = cong x (after-+ keep S c₀ 1)

        ext-0 : x (ext 0) ≡ x 0
        ext-0 = trans (ext-q z≤n) q₀≡x₀

        sub-ext : Sub (m + suc S) (x ∘ ext)
        sub-ext = Sub-restrict sub ext (λ i<j _ → after-mono keep S c₀ mono (n<1+n (keep S)) i<j)
                                       (after-bound keep S c₀ bound (subst (λ z → z + c₀ ≤ℕ N) (sym (m+n∸n≡m m (suc S))) block))

        sub-ext₁ : Sub (suc S) (x ∘ ext)
        sub-ext₁ = Sub-prefix sub-ext (m≤n+m (suc S) m)

        sub-ext₂ : Sub (suc (suc S)) (x ∘ ext)
        sub-ext₂ = Sub-prefix sub-ext (+-monoˡ-≤ (suc S) 0<m)

        bt-ext : BType S (x ∘ ext)
        bt-ext = BType-cong ≤ℕ-refl (λ t t≤S → ext-q t≤S) bt

        hA₂′ : x (ext S) A₂ x (ext (suc S))
        hA₂′ = subst₂ _A₂_ (sym (ext-q ≤ℕ-refl)) (sym ext-p₀) hA₂

        q₀≤κp₀′ : x (ext 0) ≤ κ (x (ext (suc S)))
        q₀≤κp₀′ = subst₂ (λ a b → a ≤ κ b) (sym ext-0) (sym ext-p₀) q₀≤κp₀

        ¬p₀₋<q₀₋′ : ¬ (x (ext (suc S)) ₋ < x (ext 0) ₋)
        ¬p₀₋<q₀₋′ = subst₂ (λ a b → ¬ (a ₋ < b ₋)) (sym ext-p₀) (sym ext-0) ¬p₀₋<q₀₋

        -- Lemmas 5.47 and 5.48 for q₀, …, q_S, p₀.
        five47 : (¬ p₀ ₋ ≤ x 0 ₋) × (⋁< (x ∘ ext) S ≤ κ p₀)
        five47 = subst₂ (λ a b → (¬ a ₋ ≤ b ₋) × (⋁< (x ∘ ext) S ≤ κ a)) ext-p₀ ext-0
                        (lemma-5-47 sub-ext₁ bt-ext hA₂′ q₀≤κp₀′ ¬p₀₋<q₀₋′)

        p₀₋≰q₀₋ : ¬ p₀ ₋ ≤ x 0 ₋
        p₀₋≰q₀₋ = proj₁ five47

        qₜ≤κp₀ : ∀ {t} → t <ℕ S → q t ≤ κ p₀
        qₜ≤κp₀ {t} t<S = subst (_≤ κ p₀) (ext-q (<⇒≤ t<S)) (≤-trans (⋁<-upper (x ∘ ext) t<S) (proj₂ five47))

        qₜ≤κp : ∀ {t} → t <ℕ S → ∀ {l} → l ≤ℕ m → q t ≤ κ (p l)
        qₜ≤κp t<S l≤m = ≤-trans (qₜ≤κp₀ t<S) (κp₀≤κp _ l≤m)

        p₀≡u₋ : p₀ ≡ u ₋
        p₀≡u₋ = subst₂ (λ a b → a ≡ b ₋) ext-p₀ (ext-q ≤ℕ-refl) (lemma-5-48 sub-ext₁ bt-ext hA₂′ q₀≤κp₀′ ¬p₀₋<q₀₋′)

        p₀<u : p₀ < u
        p₀<u = A→< (proj₁ hA₂)

        u₋≤κqₛ′ : u ₋ ≤ κ (q s′)
        u₋≤κqₛ′ = B3 ≤ℕ-refl

        -- The free star principle between a kept member and a block member, through their positions in x.
        freeStar-qp : ∀ {t} → t ≤ℕ s′ → ∀ {l} → l ≤ℕ m → p l ₋ ≤ κ (q t) → p l ≤ κ (q t)
        freeStar-qp {t} t≤s′ {l} l≤m =
          Sub-freeStar′ sub (bound (≤ℕ-trans t≤s′ (n≤1+n s′))) (≤ℕ-trans (+-monoˡ-≤ c₀ l≤m) block)
                        (λ e → <ℕ-irrefl e (<ℕ-≤-trans (keep<c₀ t≤s′) (m≤n+m c₀ l)))
                        (λ e → <ℕ-irrefl (sym e) (<ℕ-≤-trans (s≤s (mono (s≤s t≤s′) ≤ℕ-refl)) (m≤n+m c₀ l)))
                        (λ { (_ , e) → contra (subst (c₀ ≤ℕ_) e (m≤n+m c₀ l)) })
          where
          contra : ¬ c₀ ≤ℕ 0
          contra ()

        -- Lemma 5.50 for q₀, …, q_S, p₀, p₁: p₁ ≰ κ(q_{s′}).
        p₁≰κqₛ′ : ¬ p 1 ≤ κ (q s′)
        p₁≰κqₛ′ p₁≤ = a≰κ (Sub-irr sub-q (n≤1+n s′))
          (≤-trans (subst (_≤ ⋁< (x ∘ ext) (suc S)) (ext-q (n≤1+n s′)) (⋁<-upper (x ∘ ext) (<ℕ-trans (n<1+n s′) (n<1+n S))))
                   (≤-trans (subst₂ (λ a b → ⋁< (x ∘ ext) (suc S) ≤ a ∨ b) ext-p₀ ext-p₁
                                    (lemma-5-50 sub-ext₂ bt-ext hA₂′ hB′ q₀≤κp₀′ ¬p₀₋<q₀₋′))
                            (∨-least (≤-trans (≤-reflexive′ p₀≡u₋) u₋≤κqₛ′) p₁≤)))
          where
          hB′ : x (ext (suc S)) B x (ext (suc (suc S)))
          hB′ = subst₂ _B_ (sym ext-p₀) (sym ext-p₁) (Bs 0 0<m)

        -- The first B of the block is not a B₂: by Lemma 5.50 for q₀, …, q_S, p₀, p₁, q_S ≤ p₀ ∨ p₁, while
        -- p₀ ∨ p₁ ≤ κ(q_S) when p₁₋ < p₀, p₁ by the free star principle.
        noB₂ : ¬ (p₀ B₂ p 1)
        noB₂ (_ , p₁₋<p₀) = a≰κ (Sub-irr sub-q ≤ℕ-refl) (≤-trans u≤ (∨-least p₀≤κu p₁≤κu))
          where
          hB′ : x (ext (suc S)) B x (ext (suc (suc S)))
          hB′ = subst₂ _B_ (sym ext-p₀) (sym ext-p₁) (Bs 0 0<m)

          u≤ : u ≤ p₀ ∨ p 1
          u≤ = ≤-trans (subst (_≤ ⋁< (x ∘ ext) (suc S)) (ext-q ≤ℕ-refl) (⋁<-upper (x ∘ ext) (n<1+n S)))
                       (subst₂ (λ a b → ⋁< (x ∘ ext) (suc S) ≤ a ∨ b) ext-p₀ ext-p₁
                               (lemma-5-50 sub-ext₂ bt-ext hA₂′ hB′ q₀≤κp₀′ ¬p₀₋<q₀₋′))

          p₀≤κu : p₀ ≤ κ u
          p₀≤κu = ≤-trans (<→≤₋ p₀<u) (₋≤κ u)

          c₀+1≤N : suc c₀ ≤ℕ N
          c₀+1≤N = ≤ℕ-trans (+-monoˡ-≤ c₀ 0<m) block

          p₁≤κu : p 1 ≤ κ u
          p₁≤κu = Sub-freeStar′ sub (bound ≤ℕ-refl) c₀+1≤N
                    (λ e → <ℕ-irrefl e (<ℕ-trans (n<1+n (keep S)) (n<1+n c₀)))
                    (λ e → <ℕ-irrefl (sym e) (n<1+n c₀)) (λ { (_ , ()) })
                    (≤-trans (proj₁ p₁₋<p₀) p₀≤κu)

        -- p_l₋ ≰ κ(p₀) for l ≥ 1 when p_l ≤ κ(q_{s′}): for l = 1 by Lemma 5.50, for l ≥ 2 by (B4) of the block.
        ¬pl₋≤κp₀ : ∀ l → l ≤ℕ m → 0 <ℕ l → p l ≤ κ (q s′) → ¬ p l ₋ ≤ κ p₀
        ¬pl₋≤κp₀ zero          _   ()
        ¬pl₋≤κp₀ (suc zero)    _   _ p₁≤ = ⊥-elim (p₁≰κqₛ′ p₁≤)
        ¬pl₋≤κp₀ (suc (suc l)) l≤m _ _   = BP.B4 (s≤s (s≤s z≤n)) l≤m
```

The junction after `qᵢ`, and the contradiction from `p_l ≤ κ(qᵢ)` at the
largest such `i`.

```agda
        module Junction (i₀ : ℕ) (i₀≤s′ : i₀ ≤ℕ s′) (l : ℕ) (l≤m : l ≤ℕ m)
                        (pl≤κqᵢ₀ : p l ≤ κ (q i₀)) (bd : Boundary keep i₀) (ssk≤N : suc (suc (keep i₀)) ≤ℕ N)
                        (v≤κpl : x (suc (suc (keep i₀))) ≤ κ (p l))
                        (¬pl₋≤κv : ¬ p l ₋ ≤ κ (x (suc (suc (keep i₀))))) where
          open Boundary bd

          u′ v′ : Fin (suc n)
          u′ = x (suc (keep i₀))
          v′ = x (suc (suc (keep i₀)))

          i₀≤S : i₀ ≤ℕ S
          i₀≤S = ≤ℕ-trans i₀≤s′ (n≤1+n s′)

          i₀<S : i₀ <ℕ S
          i₀<S = s≤s i₀≤s′

          -- q₀, …, q_{i₀}, u′, v′ as the family jx.
          jk : ℕ → ℕ
          jk = after keep i₀ (suc (keep i₀))

          jx : ℕ → Fin (suc n)
          jx = x ∘ jk

          jx-q : ∀ {t} → t ≤ℕ i₀ → jx t ≡ q t
          jx-q t≤i₀ = cong x (after-≤ keep i₀ (suc (keep i₀)) t≤i₀)

          jx-u : jx (suc i₀) ≡ u′
          jx-u = cong x (after-suc keep i₀ (suc (keep i₀)))

          jx-v : jx (suc (suc i₀)) ≡ v′
          jx-v = cong x (after-+ keep i₀ (suc (keep i₀)) 1)

          jx-0 : jx 0 ≡ x 0
          jx-0 = trans (jx-q z≤n) q₀≡x₀

          sub-j : Sub (suc (suc i₀)) jx
          sub-j = Sub-restrict sub jk (λ i<j _ → after-mono keep i₀ (suc (keep i₀)) (λ i<j′ j≤i₀ → mono i<j′ (≤ℕ-trans j≤i₀ i₀≤S)) (n<1+n _) i<j)
                                      (after-bound keep i₀ (suc (keep i₀)) (λ t≤i₀ → bound (≤ℕ-trans t≤i₀ i₀≤S))
                                                   (subst (λ z → z + suc (keep i₀) ≤ℕ N) (sym (m+n∸n≡m 1 i₀)) ssk≤N))

          module BU = BType bt-u

          iᵤ′ : HasOneLowerCover u′
          iᵤ′ = subst HasOneLowerCover jx-u (Sub-irr sub-j (n≤1+n (suc i₀)))

          iᵥ′ : HasOneLowerCover v′
          iᵥ′ = subst HasOneLowerCover jx-v (Sub-irr sub-j ≤ℕ-refl)

          iₚₗ : HasOneLowerCover (p l)
          iₚₗ = Sub-irr sub-p l≤m

          -- Lemmas 5.48 and 5.47 for q₀, …, q_{i₀}, u′, v′.
          hA₂ⱼ : jx (suc i₀) A₂ jx (suc (suc i₀))
          hA₂ⱼ = subst₂ _A₂_ (sym jx-u) (sym jx-v) v-step

          q₀≤κvⱼ : jx 0 ≤ κ (jx (suc (suc i₀)))
          q₀≤κvⱼ = subst₂ (λ a b → a ≤ κ b) (sym jx-0) (sym jx-v) q₀≤κv

          ¬v₋<q₀₋ⱼ : ¬ (jx (suc (suc i₀)) ₋ < jx 0 ₋)
          ¬v₋<q₀₋ⱼ = subst₂ (λ a b → ¬ (a ₋ < b ₋)) (sym jx-v) (sym jx-0) ¬v₋<q₀₋

          v′≡u′₋ : v′ ≡ u′ ₋
          v′≡u′₋ = subst₂ (λ a b → a ≡ b ₋) jx-v jx-u (lemma-5-48 sub-j bt-u hA₂ⱼ q₀≤κvⱼ ¬v₋<q₀₋ⱼ)

          five47ⱼ : (¬ jx (suc (suc i₀)) ₋ ≤ jx 0 ₋) × (⋁< jx (suc i₀) ≤ κ (jx (suc (suc i₀))))
          five47ⱼ = lemma-5-47 sub-j bt-u hA₂ⱼ q₀≤κvⱼ ¬v₋<q₀₋ⱼ

          v′₋≰q₀₋ : ¬ v′ ₋ ≤ x 0 ₋
          v′₋≰q₀₋ = subst₂ (λ a b → ¬ a ₋ ≤ b ₋) jx-v jx-0 (proj₁ five47ⱼ)

          qₜ≤κv′ : ∀ {t} → t ≤ℕ i₀ → q t ≤ κ v′
          qₜ≤κv′ {t} t≤i₀ = subst₂ (λ a b → a ≤ κ b) (jx-q t≤i₀) jx-v (≤-trans (⋁<-upper jx (s≤s t≤i₀)) (proj₂ five47ⱼ))

          -- (B1), (B2) and (B4) of q₀, …, q_{i₀}, u′ at u′.
          qᵢ₀₋≰u′ : ¬ q i₀ ₋ ≤ u′
          qᵢ₀₋≰u′ = subst₂ (λ a b → ¬ a ₋ ≤ b) (jx-q ≤ℕ-refl) jx-u (BU.B1 ≤ℕ-refl)

          qₜ≤κu′ : ∀ {t} → t ≤ℕ i₀ → q t ≤ κ u′
          qₜ≤κu′ t≤i₀ = subst₂ (λ a b → a ≤ κ b) (jx-q t≤i₀) jx-u (BU.B2 (s≤s t≤i₀) ≤ℕ-refl)

          u′₋≰κqₜ : ∀ {t} → t <ℕ i₀ → ¬ u′ ₋ ≤ κ (q t)
          u′₋≰κqₜ t<i₀ = subst₂ (λ a b → ¬ a ₋ ≤ κ b) jx-u (jx-q (<⇒≤ t<i₀)) (BU.B4 (s≤s t<i₀) ≤ℕ-refl)

          -- p_l ≤ κ(u′), as κ(q_{i₀}) < κ(u′) (Lemma 2.63); so u′ ≰ v′ ∨ p_l by Lemma 2.57 and u′ ∧ (v′ ∨ p_l) ≤ v′.
          pl≤κu′ : p l ≤ κ u′
          pl≤κu′ = ≤-trans pl≤κqᵢ₀ (proj₁ (B→κ< u-step))

          u′≰v′∨pl : ¬ u′ ≤ v′ ∨ p l
          u′≰v′∨pl le = ≤κ→ iᵤ′ pl≤κu′ (subst (λ z → u′ ≤ z ∨ p l) v′≡u′₋ le)

          meet≤v′ : u′ ∧ (v′ ∨ p l) ≤ v′
          meet≤v′ = subst (u′ ∧ (v′ ∨ p l) ≤_) (sym v′≡u′₋)
                          (<→≤₋′ ∧-lowerˡ λ e → u′≰v′∨pl (subst (_≤ v′ ∨ p l) e ∧-lowerʳ))

          v′≤meet : v′ ≤ u′ ∧ (v′ ∨ p l)
          v′≤meet = ∧-greatest (≤-trans (≤-reflexive′ v′≡u′₋) (₋≤ u′)) ∨-upperˡ

          -- v′ ≤ v′₋ ∨ p_{l*} by Lemma 2.57, and (W) on u′ ∧ (v′ ∨ p_l) ≤ v′₋ ∨ p_{l*} leaves v′ ≤ p_{l*}.
          v′≤pl₋ : v′ ≤ p l ₋
          v′≤pl₋ = cases (W u′ (v′ ∨ p l) (v′ ₋) (p l ₋) (≤-trans meet≤v′ (≰κ→ iᵥ′ ¬pl₋≤κv)))
            where
            cases : (u′ ≤ (v′ ₋) ∨ (p l ₋) ⊎ v′ ∨ p l ≤ (v′ ₋) ∨ (p l ₋))
                  ⊎ (u′ ∧ (v′ ∨ p l) ≤ v′ ₋ ⊎ u′ ∧ (v′ ∨ p l) ≤ p l ₋) → v′ ≤ p l ₋
            cases (inj₁ (inj₁ h)) = ⊥-elim (u′≰v′∨pl (≤-trans h (∨-mono (₋≤ v′) (₋≤ (p l)))))
            cases (inj₁ (inj₂ h)) =
              ⊥-elim (a≰κ iₚₗ (≤-trans ∨-upperʳ (≤-trans h (∨-least (≤-trans (₋≤ v′) v≤κpl) (₋≤κ (p l))))))
            cases (inj₂ (inj₁ h)) = ⊥-elim (proj₂ iᵥ′ (≤-antisym (₋≤ v′) (≤-trans v′≤meet h)))
            cases (inj₂ (inj₂ h)) = ≤-trans v′≤meet h

          -- v′ = u′₋ ≰ q_{i₀}: q_{i₀} B₂ u′ is excluded.
          u′₋≰qᵢ₀ : ¬ u′ ₋ ≤ q i₀
          u′₋≰qᵢ₀ = subst₂ (λ a b → ¬ a ₋ ≤ b) jx-u (jx-q ≤ℕ-refl) (no-B₂ i₀ bt-u ne h0)
            where
            ne : jx (suc i₀) ₋ ≢ jx i₀
            ne e = B→≰ u-step (≤-trans (≤-reflexive′ (trans (sym (jx-q ≤ℕ-refl)) (trans (sym e) (cong _₋ jx-u)))) (₋≤ u′))

            h0 : ¬ jx (suc i₀) ₋ ≤ jx 0 ₋
            h0 le = ¬v₋<q₀₋ (≤-trans (₋≤ v′) (≤-trans (≤-reflexive′ v′≡u′₋) le′) , λ e → proj₂ iᵥ′ (≤-antisym (₋≤ v′) (≤-trans (≤-reflexive′ v′≡u′₋) (≤-trans le′ (≤-reflexive′ (sym e))))))
              where
              le′ : u′ ₋ ≤ x 0 ₋
              le′ = subst₂ (λ a b → a ₋ ≤ b ₋) jx-u jx-0 le

          -- Lemma 5.43 for q₀, …, q_{i₀}, u′, v′ with t = κ(v′)* ∧ (q_{i₀*} ∨ p_l).
          t : Fin (suc n)
          t = (v′ ∨ κ v′) ∧ ((q i₀ ₋) ∨ p l)

          v′≤t : v′ ≤ t
          v′≤t = ∧-greatest ∨-upperˡ (≤∨ʳ (≤-trans v′≤pl₋ (₋≤ (p l))))

          qᵢ₀₋≤t : q i₀ ₋ ≤ t
          qᵢ₀₋≤t = ∧-greatest (≤∨ʳ (≤-trans (₋≤ (q i₀)) (qₜ≤κv′ ≤ℕ-refl))) ∨-upperˡ

          v′<t : v′ < t
          v′<t = v′≤t , λ e → qᵢ₀₋≰u′ (≤-trans qᵢ₀₋≤t (≤-trans (≤-reflexive′ (sym e)) (≤-trans (≤-reflexive′ v′≡u′₋) (₋≤ u′))))

          Y′ rhs : Fin (suc n)
          Y′ = ⋁< (λ s → jx s ₋) i₀
          rhs = v′ ∨ (Y′ ∨ q i₀)

          Y′≤ : ∀ {z} → (∀ s → s <ℕ i₀ → q s ≤ z) → Y′ ≤ z
          Y′≤ f = ⋁<-least (λ s → jx s ₋) λ s s<i₀ → ≤-trans (₋≤ (jx s)) (subst (_≤ _) (sym (jx-q (<⇒≤ s<i₀))) (f s s<i₀))

          rhs≤κu′ : rhs ≤ κ u′
          rhs≤κu′ = ∨-least (≤-trans (≤-reflexive′ v′≡u′₋) (₋≤κ u′))
                          (∨-least (Y′≤ λ s s<i₀ → qₜ≤κu′ (<⇒≤ s<i₀)) (qₜ≤κu′ ≤ℕ-refl))

          rhs≤κpl : rhs ≤ κ (p l)
          rhs≤κpl = ∨-least v≤κpl (∨-least (Y′≤ λ s s<i₀ → qₜ≤κp (<ℕ-trans s<i₀ i₀<S) l≤m) (qₜ≤κp i₀<S l≤m))

          u′≤v′∨κv′ : u′ ≤ v′ ∨ κ v′
          u′≤v′∨κv′ = proj₂ (proj₂ (proj₂ (proj₁ v-step)))

          -- 5.43 (6): (W) on t ≤ rhs fails in every disjunct.
          t≰rhs : ¬ t ≤ rhs
          t≰rhs t≤rhs = outer (W (v′ ∨ κ v′) ((q i₀ ₋) ∨ p l) v′ (Y′ ∨ q i₀) t≤rhs)
            where
            from-κv* : ¬ v′ ∨ κ v′ ≤ rhs
            from-κv* h = a≰κ iᵤ′ (≤-trans u′≤v′∨κv′ (≤-trans h rhs≤κu′))

            from-second : ¬ (q i₀ ₋) ∨ p l ≤ rhs
            from-second h = a≰κ iₚₗ (≤-trans ∨-upperʳ (≤-trans h rhs≤κpl))

            from-t≤qₛ₋ : ∀ s → s <ℕ i₀ → ¬ t ≤ jx s ₋
            from-t≤qₛ₋ s s<i₀ h =
              u′₋≰κqₜ s<i₀ (≤-trans (≤-reflexive′ (sym v′≡u′₋))
                                    (≤-trans v′≤t (≤-trans h (subst (λ z → z ₋ ≤ κ (q s)) (sym (jx-q (<⇒≤ s<i₀))) (₋≤κ (q s))))))

            from-t≤qᵢ₀ : ¬ t ≤ q i₀
            from-t≤qᵢ₀ h = u′₋≰qᵢ₀ (≤-trans (≤-reflexive′ (sym v′≡u′₋)) (≤-trans v′≤t h))

            inner : (v′ ∨ κ v′ ≤ Y′ ∨ q i₀ ⊎ (q i₀ ₋) ∨ p l ≤ Y′ ∨ q i₀)
                  ⊎ ((Σ ℕ λ s → s <ℕ i₀ × t ≤ jx s ₋) ⊎ t ≤ q i₀) → ⊥
            inner (inj₁ (inj₁ h))              = from-κv* (≤∨ʳ h)
            inner (inj₁ (inj₂ h))              = from-second (≤∨ʳ h)
            inner (inj₂ (inj₁ (s , s<i₀ , h))) = from-t≤qₛ₋ s s<i₀ h
            inner (inj₂ (inj₂ h))              = from-t≤qᵢ₀ h

            outer : (v′ ∨ κ v′ ≤ rhs ⊎ (q i₀ ₋) ∨ p l ≤ rhs) ⊎ (t ≤ v′ ⊎ t ≤ Y′ ∨ q i₀) → ⊥
            outer (inj₁ (inj₁ h)) = from-κv* h
            outer (inj₁ (inj₂ h)) = from-second h
            outer (inj₂ (inj₁ h)) = proj₂ v′<t (≤-antisym v′≤t h)
            outer (inj₂ (inj₂ h)) = inner (W-⋁< (λ s → jx s ₋) i₀ h)

          -- Lemma 5.43, its hypotheses stated of v′, u′, q_{i₀} and q₀.
          apply-5-43 : ∀ v″ u″ q″ q0″ → jx (suc (suc i₀)) ≡ v″ → jx (suc i₀) ≡ u″ → jx i₀ ≡ q″ → jx 0 ≡ q0″
                     → ¬ v″ ₋ ≤ q0″ ₋ → v″ ₋ ≤ u″ ₋ → v″ < t → t ≤ v″ ∨ κ v″ → t ≤ κ q″
                     → ¬ t ≤ v″ ∨ (Y′ ∨ q″) → ¬ (v″ B q0″) → ¬ ⋁< (λ s → jx s ₋) (suc i₀) ≤ κ v″
          apply-5-43 _ _ _ _ refl refl refl refl = SubsC.Lemma543.lemma-5-43 sub-j bt-u t

          contradiction : ⊥
          contradiction =
            apply-5-43 v′ u′ (q i₀) (x 0) jx-v jx-u (jx-q ≤ℕ-refl) jx-0
              v′₋≰q₀₋ (≤-trans (₋≤ v′) (≤-reflexive′ v′≡u′₋)) v′<t ∧-lowerˡ
              (≤-trans ∧-lowerʳ (∨-least (₋≤κ (q i₀)) pl≤κqᵢ₀)) t≰rhs (λ vBq₀ → B→≰κ vBq₀ q₀≤κv)
              (⋁<-least (λ s → jx s ₋) λ s s<si₀ →
                 ≤-trans (₋≤ (jx s)) (subst (_≤ κ v′) (sym (jx-q (s≤s⁻¹ s<si₀))) (qₜ≤κv′ (s≤s⁻¹ s<si₀))))

        -- The junction q_{s′} B u A₂ p₀ at the end of the chain.
        last-boundary : Boundary keep s′
        last-boundary = record
          { u-step  = subst (λ z → x (keep s′) B x z) direct qₛ′Bu
          ; v-step  = subst (λ z → x z A₂ x (suc z)) direct hA₂
          ; bt-u    = BType-cong ≤ℕ-refl agree bt
          ; q₀≤κv   = subst (λ z → x 0 ≤ κ (x (suc z))) direct q₀≤κp₀
          ; ¬v₋<q₀₋ = subst (λ z → ¬ (x (suc z) ₋ < x 0 ₋)) direct ¬p₀₋<q₀₋ }
          where
          agree : ∀ t′ → t′ ≤ℕ S → x (after keep s′ (suc (keep s′)) t′) ≡ x (keep t′)
          agree t′ t′≤S = cong x (cases (m≤n⇒m<n∨m≡n t′≤S))
            where
            cases : t′ <ℕ S ⊎ t′ ≡ S → after keep s′ (suc (keep s′)) t′ ≡ keep t′
            cases (inj₁ t′<S) = after-≤ keep s′ (suc (keep s′)) (s≤s⁻¹ t′<S)
            cases (inj₂ e)    = subst (λ z → after keep s′ (suc (keep s′)) z ≡ keep z) (sym e) (trans (after-suc keep s′ (suc (keep s′))) (sym direct))

        -- The largest index i₀ ≤ s′ with p_l ≤ κ(q_{i₀}), l ≥ 1: the step after q_{i₀} is a B to the next kept
        -- member, against the choice of i₀, or the junction after q_{i₀}, or q_{s′} B u A₂ p₀ when i₀ = s′.
        module AtMax (i₀ : ℕ) (i₀≤s′ : i₀ ≤ℕ s′) (l : ℕ) (l≤m : l ≤ℕ m) (0<l : 0 <ℕ l)
                     (Pi₀ : p l ≤ κ (q i₀)) (maximal : ∀ i′ → i₀ <ℕ i′ → i′ ≤ℕ s′ → ¬ p l ≤ κ (q i′)) where

          contradiction : ⊥
          contradiction = from (steps i₀ (s≤s i₀≤s′))
            where
            from : (keep (suc i₀) ≡ suc (keep i₀) × x (keep i₀) B x (keep (suc i₀)))
                 ⊎ (keep (suc i₀) ≡ suc (suc (keep i₀)) × Boundary keep i₀) → ⊥
            from (inj₁ (e , qBq′)) = direct-case (m≤n⇒m<n∨m≡n i₀≤s′)
              where
              direct-case : i₀ <ℕ s′ ⊎ i₀ ≡ s′ → ⊥
              direct-case (inj₁ i₀<s′) = maximal (suc i₀) (n<1+n i₀) i₀<s′ (≤-trans Pi₀ (proj₁ (B→κ< qBq′)))
              direct-case (inj₂ i₀≡s′) =
                Junction.contradiction s′ ≤ℕ-refl l l≤m (subst (λ z → p l ≤ κ (q z)) i₀≡s′ Pi₀) last-boundary
                  (subst (λ z → suc z ≤ℕ N) direct c₀≤N)
                  (subst (λ z → x (suc z) ≤ κ (p l)) direct (BP.B2 0<l l≤m))
                  (subst (λ z → ¬ p l ₋ ≤ κ (x (suc z))) direct (¬pl₋≤κp₀ l l≤m 0<l (subst (λ z → p l ≤ κ (q z)) i₀≡s′ Pi₀)))
                where
                c₀≤N : c₀ ≤ℕ N
                c₀≤N = ≤ℕ-trans (m≤n+m c₀ m) block
            from (inj₂ (e , bd)) =
              Junction.contradiction i₀ i₀≤s′ l l≤m Pi₀ bd (subst (_≤ℕ N) e (bound (s≤s i₀≤s′)))
                (subst (λ z → x z ≤ κ (p l)) e (qₜ≤κp (s≤s si₀≤s′) l≤m))
                (subst (λ z → ¬ p l ₋ ≤ κ (x z)) e λ h → maximal (suc i₀) (n<1+n i₀) si₀≤s′ (freeStar-qp si₀≤s′ l≤m h))
              where
              si₀≤s′ : suc i₀ ≤ℕ s′
              si₀≤s′ = cases (m≤n⇒m<n∨m≡n i₀≤s′)
                where
                cases : i₀ <ℕ s′ ⊎ i₀ ≡ s′ → suc i₀ ≤ℕ s′
                cases (inj₁ lt) = lt
                cases (inj₂ e′) = ⊥-elim (1+n≢n (suc-injective (trans (sym (subst (λ z → keep (suc z) ≡ suc (suc (keep z))) e′ e)) direct)))
```

The new chain and its B-type property.

```agda
        -- (B4) between the parts: p_{l*} ≰ κ(q_i) for i ≤ s′ and i + 1 < l + S.
        B4-mixed : ∀ {i} → i ≤ℕ s′ → ∀ {l} → l ≤ℕ m → suc i <ℕ l + S → ¬ p l ₋ ≤ κ (q i)
        B4-mixed {i} i≤s′ {l} l≤m si<l+S pl₋≤ = strong i≤s′ l≤m si<l+S (freeStar-qp i≤s′ l≤m pl₋≤)
          where
          strong : ∀ {i} → i ≤ℕ s′ → ∀ {l} → l ≤ℕ m → suc i <ℕ l + S → ¬ p l ≤ κ (q i)
          strong {i} i≤s′ {zero}   _    si<S pl≤ = B4 si<S ≤ℕ-refl (subst (_≤ κ (q i)) p₀≡u₋ pl≤)
          strong {i} i≤s′ {suc l′} sl′≤m _   pl≤ =
            let (i₀ , _ , i₀≤s′ , Pi₀ , maximal) = greatest-index (λ i′ → p (suc l′) ≤? κ (q i′)) s′ i i≤s′ pl≤
            in AtMax.contradiction i₀ i₀≤s′ (suc l′) sl′≤m (s≤s z≤n) Pi₀ maximal

        -- Positions in the new sequence: the kept part up to s′, and the block.
        data Pos (t′ : ℕ) : Type where
          inQ : t′ ≤ℕ s′ → Pos t′
          inP : ∀ l → l ≤ℕ m → t′ ≡ l + S → Pos t′

        pos : ∀ t′ → t′ ≤ℕ L′ → Pos t′
        pos t′ t′≤L′ = cases (t′ ≤ℕ? s′)
          where
          cases : Dec (t′ ≤ℕ s′) → Pos t′
          cases (yes h) = inQ h
          cases (no h)  = inP (t′ ∸ S) (subst (t′ ∸ S ≤ℕ_) (m+n∸n≡m m S) (∸-monoˡ-≤ S t′≤L′)) (sym (m∸n+n≡m (≰⇒> h)))

        -- A block index lies after every kept index.
        pq-absurd : ∀ {i j l} → i ≡ l + S → j ≤ℕ s′ → i <ℕ j → ⊥
        pq-absurd {i} {j} {l} e j≤s′ i<j = <ℕ-irrefl refl (<ℕ-≤-trans (<ℕ-≤-trans (≤ℕ-<-trans (subst (S ≤ℕ_) (sym e) (m≤n+m S l)) i<j) j≤s′) (n≤1+n s′))

        yq : ∀ {i} → i ≤ℕ s′ → y i ≡ q i
        yq = y-q

        yp : ∀ {i l} → i ≡ l + S → y i ≡ p l
        yp {i} {l} e = trans (cong y e) (y-p l)

        -- (B1) to (B4) for y.
        b1 : ∀ {i} → suc i ≤ℕ L′ → ¬ y i ₋ ≤ y (suc i)
        b1 {i} si≤L′ = go (pos i (<⇒≤ si≤L′))
          where
          go : Pos i → ¬ y i ₋ ≤ y (suc i)
          go (inQ i≤s′) = split (m≤n⇒m<n∨m≡n i≤s′)
            where
            split : i <ℕ s′ ⊎ i ≡ s′ → ¬ y i ₋ ≤ y (suc i)
            split (inj₁ i<s′) = subst₂ (λ a b → ¬ a ₋ ≤ b) (sym (yq (<⇒≤ i<s′))) (sym (yq i<s′)) (B1 (≤ℕ-trans i<s′ (n≤1+n s′)))
            split (inj₂ e)    = subst (λ z → ¬ y z ₋ ≤ y (suc z)) (sym e)
                                      (subst₂ (λ a b → ¬ a ₋ ≤ b) (sym (yq ≤ℕ-refl)) (sym y-p₀) λ h → B1 ≤ℕ-refl (≤-trans h (proj₁ p₀<u)))
          go (inP l l≤m e) = subst (λ z → ¬ y z ₋ ≤ y (suc z)) (sym e)
                                   (subst₂ (λ a b → ¬ a ₋ ≤ b) (sym (y-p l)) (sym (y-p (suc l))) (BP.B1 sl≤m))
            where
            sl≤m : suc l ≤ℕ m
            sl≤m = +-cancelʳ-≤ S (suc l) m (subst (λ z → suc z ≤ℕ L′) e si≤L′)

        b2 : ∀ {i j} → i <ℕ j → j ≤ℕ L′ → y i ≤ κ (y j)
        b2 {i} {j} i<j j≤L′ = go (pos i (<⇒≤ (<ℕ-≤-trans i<j j≤L′))) (pos j j≤L′)
          where
          go : Pos i → Pos j → y i ≤ κ (y j)
          go (inQ i≤s′)     (inQ j≤s′)      = subst₂ (λ a b → a ≤ κ b) (sym (yq i≤s′)) (sym (yq j≤s′)) (B2 i<j (≤ℕ-trans j≤s′ (n≤1+n s′)))
          go (inQ i≤s′)     (inP l l≤m e)   = subst₂ (λ a b → a ≤ κ b) (sym (yq i≤s′)) (sym (yp e)) (qₜ≤κp (s≤s i≤s′) l≤m)
          go (inP l l≤m e)  (inQ j≤s′)      = ⊥-elim (pq-absurd e j≤s′ i<j)
          go (inP l l≤m e)  (inP l′ l′≤m e′) =
            subst₂ (λ a b → a ≤ κ b) (sym (yp e)) (sym (yp e′))
                   (BP.B2 (+-cancelʳ-≤ S (suc l) l′ (subst₂ (λ a b → suc a ≤ℕ b) e e′ i<j)) l′≤m)

        b3 : ∀ {i} → suc i ≤ℕ L′ → y (suc i) ₋ ≤ κ (y i)
        b3 {i} si≤L′ = go (pos i (<⇒≤ si≤L′))
          where
          go : Pos i → y (suc i) ₋ ≤ κ (y i)
          go (inQ i≤s′) = split (m≤n⇒m<n∨m≡n i≤s′)
            where
            split : i <ℕ s′ ⊎ i ≡ s′ → y (suc i) ₋ ≤ κ (y i)
            split (inj₁ i<s′) = subst₂ (λ a b → a ₋ ≤ κ b) (sym (yq i<s′)) (sym (yq (<⇒≤ i<s′))) (B3 (≤ℕ-trans i<s′ (n≤1+n s′)))
            split (inj₂ e)    = subst (λ z → y (suc z) ₋ ≤ κ (y z)) (sym e)
                                      (subst₂ (λ a b → a ₋ ≤ κ b) (sym y-p₀) (sym (yq ≤ℕ-refl))
                                              (≤-trans (₋≤ p₀) (≤-trans (<→≤₋ p₀<u) u₋≤κqₛ′)))
          go (inP l l≤m e) = subst (λ z → y (suc z) ₋ ≤ κ (y z)) (sym e)
                                   (subst₂ (λ a b → a ₋ ≤ κ b) (sym (y-p (suc l))) (sym (y-p l)) (BP.B3 sl≤m))
            where
            sl≤m : suc l ≤ℕ m
            sl≤m = +-cancelʳ-≤ S (suc l) m (subst (λ z → suc z ≤ℕ L′) e si≤L′)

        b4 : ∀ {i j} → suc i <ℕ j → j ≤ℕ L′ → ¬ y j ₋ ≤ κ (y i)
        b4 {i} {j} si<j j≤L′ = go (pos i (<⇒≤ (<ℕ-≤-trans (<ℕ-trans (n<1+n i) si<j) j≤L′))) (pos j j≤L′)
          where
          go : Pos i → Pos j → ¬ y j ₋ ≤ κ (y i)
          go (inQ i≤s′)     (inQ j≤s′)      = subst₂ (λ a b → ¬ a ₋ ≤ κ b) (sym (yq j≤s′)) (sym (yq i≤s′)) (B4 si<j (≤ℕ-trans j≤s′ (n≤1+n s′)))
          go (inQ i≤s′)     (inP l l≤m e)   = subst₂ (λ a b → ¬ a ₋ ≤ κ b) (sym (yp e)) (sym (yq i≤s′)) (B4-mixed i≤s′ l≤m (subst (suc i <ℕ_) e si<j))
          go (inP l l≤m e)  (inQ j≤s′)      = ⊥-elim (pq-absurd e j≤s′ (<ℕ-trans (n<1+n i) si<j))
          go (inP l l≤m e)  (inP l′ l′≤m e′) =
            subst₂ (λ a b → ¬ a ₋ ≤ κ b) (sym (yp e′)) (sym (yp e))
                   (BP.B4 (+-cancelʳ-≤ S (suc (suc l)) l′ (subst₂ (λ a b → suc (suc a) ≤ℕ b) e e′ si<j)) l′≤m)

        bt′ : BType L′ y
        bt′ = record { B1 = b1 ; B2 = b2 ; B3 = b3 ; B4 = b4 }

        -- The chain structure of y: the old steps up to s′, the new junction at s′, and the block's B's.
        keep′0 : keep′ 0 ≡ 0
        keep′0 = trans (after-≤ keep s′ c₀ z≤n) keep0

        mono′ : ∀ {i j} → i <ℕ j → j ≤ℕ L′ → keep′ i <ℕ keep′ j
        mono′ i<j _ = after-mono keep s′ c₀ (λ i<j′ j≤s′ → mono i<j′ (≤ℕ-trans j≤s′ (n≤1+n s′))) (keep<c₀ ≤ℕ-refl) i<j

        bound′ : ∀ {i} → i ≤ℕ L′ → keep′ i ≤ℕ N
        bound′ = after-bound keep s′ c₀ (λ t≤s′ → bound (≤ℕ-trans t≤s′ (n≤1+n s′))) (subst (λ z → z + c₀ ≤ℕ N) (sym (m+n∸n≡m m S)) block)

        steps′ : ∀ i → i <ℕ L′ → (keep′ (suc i) ≡ suc (keep′ i) × y i B y (suc i))
                               ⊎ (keep′ (suc i) ≡ suc (suc (keep′ i)) × Boundary keep′ i)
        steps′ i i<L′ = go (pos i (<⇒≤ i<L′))
          where
          go : Pos i → (keep′ (suc i) ≡ suc (keep′ i) × y i B y (suc i)) ⊎ (keep′ (suc i) ≡ suc (suc (keep′ i)) × Boundary keep′ i)
          go (inQ i≤s′) = split (m≤n⇒m<n∨m≡n i≤s′)
            where
            split : i <ℕ s′ ⊎ i ≡ s′ → (keep′ (suc i) ≡ suc (keep′ i) × y i B y (suc i)) ⊎ (keep′ (suc i) ≡ suc (suc (keep′ i)) × Boundary keep′ i)
            split (inj₁ i<s′) = carry (steps i (≤ℕ-trans i<s′ (n≤1+n s′)))
              where
              agree : ∀ t′ → t′ ≤ℕ i → keep t′ ≡ keep′ t′
              agree t′ t′≤i = sym (after-≤ keep s′ c₀ (≤ℕ-trans t′≤i (<⇒≤ i<s′)))

              carry : (keep (suc i) ≡ suc (keep i) × x (keep i) B x (keep (suc i)))
                    ⊎ (keep (suc i) ≡ suc (suc (keep i)) × Boundary keep i)
                    → (keep′ (suc i) ≡ suc (keep′ i) × y i B y (suc i)) ⊎ (keep′ (suc i) ≡ suc (suc (keep′ i)) × Boundary keep′ i)
              carry (inj₁ (e , h))  = inj₁ (trans (after-≤ keep s′ c₀ i<s′) (trans e (cong suc (sym (after-≤ keep s′ c₀ (<⇒≤ i<s′)))))
                                           , subst₂ _B_ (sym (yq (<⇒≤ i<s′))) (sym (yq i<s′)) h)
              carry (inj₂ (e , bd)) = inj₂ (trans (after-≤ keep s′ c₀ i<s′) (trans e (cong (λ z → suc (suc z)) (sym (after-≤ keep s′ c₀ (<⇒≤ i<s′)))))
                                           , Boundary-resp agree bd)
            split (inj₂ e) = inj₂ (subst (λ z → keep′ (suc z) ≡ suc (suc (keep′ z))) (sym e) e₁
                                  , subst (Boundary keep′) (sym e) (Boundary-resp (λ t′ t′≤s′ → sym (after-≤ keep s′ c₀ t′≤s′)) last-boundary))
              where
              e₁ : keep′ S ≡ suc (suc (keep′ s′))
              e₁ = trans (after-suc keep s′ c₀) (trans (cong suc direct) (cong (λ z → suc (suc z)) (sym (after-≤ keep s′ c₀ ≤ℕ-refl))))
          go (inP l l≤m e) = inj₁ (subst (λ z → keep′ (suc z) ≡ suc (keep′ z)) (sym e) (trans (after-+ keep s′ c₀ (suc l)) (cong suc (sym (after-+ keep s′ c₀ l))))
                                  , subst (λ z → y z B y (suc z)) (sym e) (subst₂ _B_ (sym (y-p l)) (sym (y-p (suc l))) (Bs l l<m)))
            where
            l<m : l <ℕ m
            l<m = +-cancelʳ-≤ S (suc l) m (subst (λ z → suc z ≤ℕ L′) e i<L′)

        chain′ : Chain L′ keep′
        chain′ = record { keep0 = keep′0 ; mono = mono′ ; bound = bound′ ; bt = bt′ ; steps = steps′ }
```
