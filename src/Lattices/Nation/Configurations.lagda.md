---
layout: default
file: "src/Lattices/Nation/Configurations.lagda.md"
title: "Lattices.Nation.Configurations module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Three configurations that (W) excludes from a finite lattice

This is the [Lattices.Nation.Configurations][] module of the [agda-lattices][]
library.

Lemmas 5.38, 5.39 and 5.40 of [Freese, Ježek, and Nation (1995)][] (pp. 112
to 113; Nation's Lemmas 2.2, 2.3 and their duals) describe three configurations
of elements that a finite lattice satisfying Whitman's condition (W) cannot
contain.  The book's proofs build from each configuration a new one of the same
kind with a strictly smaller element, and conclude from the finiteness of the
lattice, which forbids an infinite descending chain.  Here each configuration
is a record, the construction is a function from the record to the record at the
smaller elements (`shrink₃₈`{.AgdaFunction}, `shrink₃₉`{.AgdaFunction}), and
the exclusion is a well-founded induction on the element that shrinks, along
the strict order of the finite lattice, which [Lattices.Bounded.Finite][]
proves well founded; no classical principle enters.  The lemmas need (W) and
finiteness only, so the module takes no semidistributive law.  It supplies the
following:

+  **No doubly reducible element** (`not-doubly`{.AgdaFunction},
   `meet-irr`{.AgdaFunction}), the form of FJN Corollary 1.9 the lemmas use: an
   element other than the least that is not join irreducible is the join of two
   smaller elements, so (W) forbids it to be the meet of two larger ones; and an
   element other than the least that is the meet of two larger elements is join
   irreducible.
+  **Lemma 5.38** (`Config₃₈`{.AgdaRecord}, `no-config₃₈`{.AgdaFunction}): no
   elements `a, a₀, a₁, b, b₀` with `b` join reducible and `a` join reducible or
   `a ≤ a₋ ∨ b`; `a ≤ a₁ ≺ a₀`; `b ≤ b₀`; `a ≰ b₀`; `b ≰ a₀`; `a₀ ≰ a₁ ∨ b₀`;
   `b₀ ≰ a₁ ∨ b`.  The construction replaces `a₀, a₁, b₀` by `a₁, a₁₋, b₀ ∧ (a₁ ∨ b)`.
+  **Lemma 5.39** (`Config₃₉`{.AgdaRecord}, `no-config₃₉`{.AgdaFunction}): no
   elements `a, b, c` with `b ∧ (c ∨ (a ∧ b)) ≰ a`, `a ∧ (c ∨ (a ∧ b)) ≰ b`,
   `a ∧ b ≰ c`, `a ≰ b ∨ c`, `b ≰ a ∨ c`.  The construction replaces `a, b` by
   `a ∧ (b ∨ c), b ∧ (a ∨ c)`; the configuration is symmetric in `a` and `b`
   (`swap₃₉`{.AgdaFunction}), which halves the verification, as the book's
   "fairly simple to show" intends.
+  **Lemma 5.40** (`Config₄₀`{.AgdaRecord}, `no-config₄₀`{.AgdaFunction}, in
   `ConfigurationsDual`{.AgdaModule}): no elements `a, a₀, b, b₀` with
   `a ≤ a₀`, `b ≤ b₀`, `a ≰ b₀`, `b ≰ a₀`, `a₀ ≰ a ∨ b`, `b₀ ≰ a ∨ b`,
   `a₀ ∧ b ≰ a`, `a ∧ b₀ ≰ b`.  With `c = a₀ ∧ b₀` the elements `a, b, c` form
   the configuration of Lemma 5.39 in the dual lattice, which is the instance of
   this module at the dual tables.

The book's proof of Lemma 5.38 is given in full and is followed step by step,
with one detail it leaves implicit made explicit: `a₁`, the meet of `a₀` and
`a₁ ∨ b₀`, is not the least element, since `a ≤ a₁` and `a ≰ b₀`.

The module checks in 0.4 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Configurations where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Relation.Unary.All           using ( All )
open import Data.Nat.Base                          using ( ℕ ; suc )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( decidable-stable )

import Data.List.Relation.Unary.All as All

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Finite    using ( module JoinDependency ; dual-laws )
open import Lattices.Nation.Order      using ( module Order )
open import Lattices.Semidistributive  using ( SatisfiesW ; W-irreducible )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

#### No doubly reducible element

```agda
module Configurations {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                      (laws : LatticeTableLaws _∧_ _∨_)
                      (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open JoinDependency laws
  open Order laws

  -- (W), with the table lattice's order.
  W : ∀ s₁ s₂ t₁ t₂ → s₁ ∧ s₂ ≤ t₁ ∨ t₂
    → (s₁ ≤ t₁ ∨ t₂ ⊎ s₂ ≤ t₁ ∨ t₂) ⊎ (s₁ ∧ s₂ ≤ t₁ ⊎ s₁ ∧ s₂ ≤ t₂)
  W = w

  -- An element that is not join irreducible and not the least is not a meet of two larger elements.
  not-doubly : ∀ {p} → ¬ HasOneLowerCover p → ⊥ᴸ ≢ p → ∀ {x y} → p < x → p < y → p ≢ x ∧ y
  not-doubly {p} ¬one ⊥≢p {x} {y} p<x p<y p≡x∧y =
    split (two-below (below p) ⊥ᴸ (All.tabulate ∈below⁻) (⊥ᴸ-least p , ⊥≢p) (¬one→₋≡ ¬one))
    where
    split : Σ (Fin (suc n)) (λ u → Σ (Fin (suc n)) λ v → u < p × v < p × u ∨ v ≡ p) → ⊥
    split (u , v , u<p , v<p , e) = cases (W-irreducible (tableLattice _∧_ _∨_ laws) w (sym e) p≡x∧y)
      where
      cases : (p ≡ x ⊎ p ≡ y) ⊎ (p ≡ u ⊎ p ≡ v) → ⊥
      cases (inj₁ (inj₁ p≡x))  = proj₂ p<x p≡x
      cases (inj₁ (inj₂ p≡y))  = proj₂ p<y p≡y
      cases (inj₂ (inj₁ p≡u))  = proj₂ u<p (sym p≡u)
      cases (inj₂ (inj₂ p≡v))  = proj₂ v<p (sym p≡v)

  -- A meet of two larger elements, other than the least, is join irreducible.
  meet-irr : ∀ {p x y} → ⊥ᴸ ≢ p → p < x → p < y → p ≡ x ∧ y → HasOneLowerCover p
  meet-irr {p} ⊥≢p p<x p<y e = decidable-stable (hasOneLowerCover? p) λ ¬one → not-doubly ¬one ⊥≢p p<x p<y e
```

#### Lemma 5.38

Suppose the configuration exists.  The element `a₁` is `a₀ ∧ (a₁ ∨ b₀)`: the
meet lies between `a₁` and `a₀`, and differs from `a₀` by condition (6), so the
cover forces it to be `a₁`.  It is not the least element (`a ≤ a₁`, `a ≰ b₀`),
and it is the meet of two larger elements (`a₀` by the cover, `a₁ ∨ b₀` by
condition (7)), hence join irreducible.  (W) applied to `a₀ ∧ (a₁ ∨ b₀) ≤ a₁₋ ∨ b`
fails in each disjunct, by (6), (7), the cover and (4), so `a₁ ≰ a₁₋ ∨ b`; this
gives `a ≠ a₁` in both cases of condition (1), hence `a ≤ a₁₋`.  With
`a₂ = a₁₋` and `b₁ = b₀ ∧ (a₁ ∨ b)`, the seven conditions hold for
`a, a₁, a₂, b, b₁`: (2) to (5) directly; (6) by (W) on `a₀ ∧ (a₁ ∨ b₀) ≤ a₂ ∨ b₁`,
whose disjuncts fail by (6), (7), the cover and (4); and (7) by (W) on
`b₀ ∧ (a₁ ∨ b) ≤ a₂ ∨ b`, whose disjuncts fail by (7), by `a₁ ≰ a₁₋ ∨ b`, by (5),
and finally because `b₁ ≤ b` would make `b` the meet of `b₀` and `a₁ ∨ b`, both
larger, while `b` is join reducible.

```agda
  -- The configuration of Lemma 5.38.
  record Config₃₈ (a a₀ a₁ b b₀ : Fin (suc n)) : Type where
    field
      b-red   : ¬ HasOneLowerCover b
      a-cond  : ¬ HasOneLowerCover a ⊎ (HasOneLowerCover a × a ≤ (a ₋) ∨ b)
      a≤a₁    : a ≤ a₁
      a₁⋖a₀   : a₁ ⋖ a₀
      b≤b₀    : b ≤ b₀
      a≰b₀    : ¬ a ≤ b₀
      b≰a₀    : ¬ b ≤ a₀
      a₀≰     : ¬ a₀ ≤ a₁ ∨ b₀
      b₀≰     : ¬ b₀ ≤ a₁ ∨ b

  module Shrink₃₈ {a a₀ a₁ b b₀ : Fin (suc n)} (cfg : Config₃₈ a a₀ a₁ b b₀) where
    open Config₃₈ cfg

    a₁<a₀ : a₁ < a₀
    a₁<a₀ = proj₁ a₁⋖a₀

    a₁≤a₀ : a₁ ≤ a₀
    a₁≤a₀ = proj₁ a₁<a₀

    -- a₁ is the meet of a₀ and a₁ ∨ b₀.
    m : Fin (suc n)
    m = a₀ ∧ (a₁ ∨ b₀)

    a₁≡m : a₁ ≡ m
    a₁≡m = decidable-stable (a₁ ≟ m) λ a₁≢m →
      proj₂ a₁⋖a₀ m (∧-greatest a₁≤a₀ ∨-upperˡ , a₁≢m) (∧-lowerˡ , λ m≡a₀ → a₀≰ (subst (_≤ a₁ ∨ b₀) m≡a₀ ∧-lowerʳ))

    -- a₁ is not the least element, and is the meet of two larger elements, hence join irreducible.
    ⊥≢a₁ : ⊥ᴸ ≢ a₁
    ⊥≢a₁ e = a≰b₀ (≤-trans a≤a₁ (subst (_≤ b₀) e (⊥ᴸ-least b₀)))

    a₁<a₁∨b₀ : a₁ < a₁ ∨ b₀
    a₁<a₁∨b₀ = ∨-upperˡ , λ e → b₀≰ (≤-trans (subst (b₀ ≤_) (sym e) ∨-upperʳ) ∨-upperˡ)

    a₁-irr : HasOneLowerCover a₁
    a₁-irr = meet-irr ⊥≢a₁ a₁<a₀ a₁<a₁∨b₀ a₁≡m

    -- a₁ ≰ a₁₋ ∨ b, by (W).
    a₁≰ : ¬ a₁ ≤ (a₁ ₋) ∨ b
    a₁≰ a₁≤ = cases (W a₀ (a₁ ∨ b₀) (a₁ ₋) b (subst (_≤ (a₁ ₋) ∨ b) a₁≡m a₁≤))
      where
      cases : (a₀ ≤ (a₁ ₋) ∨ b ⊎ a₁ ∨ b₀ ≤ (a₁ ₋) ∨ b) ⊎ (m ≤ a₁ ₋ ⊎ m ≤ b) → ⊥
      cases (inj₁ (inj₁ a₀≤))  = a₀≰ (≤-trans a₀≤ (∨-mono (₋≤ a₁) b≤b₀))
      cases (inj₁ (inj₂ s≤))   = b₀≰ (≤-trans ∨-upperʳ (≤-trans s≤ (∨-monoˡ (₋≤ a₁))))
      cases (inj₂ (inj₁ m≤))   = proj₂ a₁-irr (≤-antisym (₋≤ a₁) (subst (_≤ a₁ ₋) (sym a₁≡m) m≤))
      cases (inj₂ (inj₂ m≤b))  = a≰b₀ (≤-trans a≤a₁ (≤-trans (subst (_≤ b) (sym a₁≡m) m≤b) b≤b₀))

    -- a < a₁, in both cases of condition (1).
    a≢a₁ : a ≢ a₁
    a≢a₁ = cases a-cond
      where
      cases : ¬ HasOneLowerCover a ⊎ (HasOneLowerCover a × a ≤ (a ₋) ∨ b) → a ≢ a₁
      cases (inj₁ ¬one)      a≡a₁ = ¬one (subst HasOneLowerCover (sym a≡a₁) a₁-irr)
      cases (inj₂ (_ , a≤))  a≡a₁ = a₁≰ (subst (λ x → x ≤ (x ₋) ∨ b) a≡a₁ a≤)

    a≤a₁₋ : a ≤ a₁ ₋
    a≤a₁₋ = <→≤₋′ a≤a₁ a≢a₁

    -- The new b₀.
    b₁ : Fin (suc n)
    b₁ = b₀ ∧ (a₁ ∨ b)

    b≤b₁ : b ≤ b₁
    b≤b₁ = ∧-greatest b≤b₀ ∨-upperʳ

    -- b is not the least element and lies strictly below b₀ and a₁ ∨ b.
    ⊥≢b : ⊥ᴸ ≢ b
    ⊥≢b e = b≰a₀ (subst (_≤ a₀) e (⊥ᴸ-least a₀))

    b<b₀ : b < b₀
    b<b₀ = b≤b₀ , λ b≡b₀ → b₀≰ (subst (λ x → x ≤ a₁ ∨ b) b≡b₀ ∨-upperʳ)

    b<a₁∨b : b < a₁ ∨ b
    b<a₁∨b = ∨-upperʳ , λ e → a≰b₀ (≤-trans a≤a₁ (≤-trans (subst (a₁ ≤_) (sym e) ∨-upperˡ) b≤b₀))

    -- Condition (6) for the new elements, by (W).
    a₁≰′ : ¬ a₁ ≤ (a₁ ₋) ∨ b₁
    a₁≰′ a₁≤ = cases (W a₀ (a₁ ∨ b₀) (a₁ ₋) b₁ (subst (_≤ (a₁ ₋) ∨ b₁) a₁≡m a₁≤))
      where
      cases : (a₀ ≤ (a₁ ₋) ∨ b₁ ⊎ a₁ ∨ b₀ ≤ (a₁ ₋) ∨ b₁) ⊎ (m ≤ a₁ ₋ ⊎ m ≤ b₁) → ⊥
      cases (inj₁ (inj₁ a₀≤))   = a₀≰ (≤-trans a₀≤ (∨-mono (₋≤ a₁) ∧-lowerˡ))
      cases (inj₁ (inj₂ s≤))    = b₀≰ (≤-trans ∨-upperʳ (≤-trans s≤ (∨-least (≤∨ˡ (₋≤ a₁)) ∧-lowerʳ)))
      cases (inj₂ (inj₁ m≤))    = proj₂ a₁-irr (≤-antisym (₋≤ a₁) (subst (_≤ a₁ ₋) (sym a₁≡m) m≤))
      cases (inj₂ (inj₂ m≤b₁))  = a≰b₀ (≤-trans a≤a₁ (≤-trans (subst (_≤ b₁) (sym a₁≡m) m≤b₁) ∧-lowerˡ))

    -- Condition (7) for the new elements, by (W).
    b₁≰ : ¬ b₁ ≤ (a₁ ₋) ∨ b
    b₁≰ b₁≤ = cases (W b₀ (a₁ ∨ b) (a₁ ₋) b b₁≤)
      where
      cases : (b₀ ≤ (a₁ ₋) ∨ b ⊎ a₁ ∨ b ≤ (a₁ ₋) ∨ b) ⊎ (b₁ ≤ a₁ ₋ ⊎ b₁ ≤ b) → ⊥
      cases (inj₁ (inj₁ b₀≤))    = b₀≰ (≤-trans b₀≤ (∨-monoˡ (₋≤ a₁)))
      cases (inj₁ (inj₂ s≤))     = a₁≰ (≤-trans ∨-upperˡ s≤)
      cases (inj₂ (inj₁ b₁≤a₁₋)) = b≰a₀ (≤-trans b≤b₁ (≤-trans b₁≤a₁₋ (≤-trans (₋≤ a₁) a₁≤a₀)))
      cases (inj₂ (inj₂ b₁≤b))   = not-doubly b-red ⊥≢b b<b₀ b<a₁∨b (≤-antisym b≤b₁ b₁≤b)

    -- The configuration at a₁, a₁₋, b₁.
    shrink₃₈ : Config₃₈ a a₁ (a₁ ₋) b b₁
    shrink₃₈ = record
      { b-red = b-red ; a-cond = a-cond ; a≤a₁ = a≤a₁₋ ; a₁⋖a₀ = ₋⋖ a₁-irr ; b≤b₀ = b≤b₁
      ; a≰b₀ = λ a≤b₁ → a≰b₀ (≤-trans a≤b₁ ∧-lowerˡ)
      ; b≰a₀ = λ b≤a₁ → b≰a₀ (≤-trans b≤a₁ a₁≤a₀)
      ; a₀≰ = a₁≰′ ; b₀≰ = b₁≰ }

  -- Lemma 5.38: the configuration does not exist, by well-founded induction on a₀.
  no-config₃₈ : ∀ {a a₀ a₁ b b₀} → Config₃₈ a a₀ a₁ b b₀ → ⊥
  no-config₃₈ {a₀ = a₀} = go a₀ (<-acc a₀)
    where
    go : ∀ a₀ → Acc _<_ a₀ → ∀ {a a₁ b b₀} → Config₃₈ a a₀ a₁ b b₀ → ⊥
    go a₀ (acc smaller) cfg = go _ (smaller (Shrink₃₈.a₁<a₀ cfg)) (Shrink₃₈.shrink₃₈ cfg)
```

#### Lemma 5.39

The configuration is symmetric in `a` and `b`, up to the commutativity of the
meet `a ∧ b`.  With `a₁ = a ∧ (b ∨ c)` and `b₁ = b ∧ (a ∨ c)`, the meet
`a₁ ∧ b₁` is `a ∧ b`, which gives the new (3) at once; the new (4),
`a₁ ≰ b₁ ∨ c`, holds by (W) applied to `a ∧ (b ∨ c) ≤ b₁ ∨ c`, whose disjuncts
fail by (4), by (5) since `b₁ ∨ c ≤ a ∨ c`, by (2) since
`a ∧ (c ∨ (a ∧ b)) ≤ a₁ ≤ b₁ ≤ b`, and by (3); and the new (1),
`b₁ ∧ (c ∨ (a₁ ∧ b₁)) ≰ a₁`, holds since `b ∧ (c ∨ (a ∧ b))` lies below the
left side (it lies below `b₁`, as `c ∨ (a ∧ b) ≤ a ∨ c`) and not below `a`.
The new (2) and (5) are the new (1) and (4) of the configuration with `a` and
`b` exchanged.  The element `a₁` lies strictly below `a`, by (4).

```agda
  -- The configuration of Lemma 5.39.
  record Config₃₉ (a b c : Fin (suc n)) : Type where
    field
      c₁ : ¬ b ∧ (c ∨ (a ∧ b)) ≤ a
      c₂ : ¬ a ∧ (c ∨ (a ∧ b)) ≤ b
      c₃ : ¬ a ∧ b ≤ c
      c₄ : ¬ a ≤ b ∨ c
      c₅ : ¬ b ≤ a ∨ c

  -- The configuration is symmetric in a and b.
  swap₃₉ : ∀ {a b c} → Config₃₉ a b c → Config₃₉ b a c
  swap₃₉ {a} {b} {c} cfg = record
    { c₁ = λ h → c₂ (subst (λ x → a ∧ (c ∨ x) ≤ b) ∧-comm-law h)
    ; c₂ = λ h → c₁ (subst (λ x → b ∧ (c ∨ x) ≤ a) ∧-comm-law h)
    ; c₃ = λ h → c₃ (subst (_≤ c) ∧-comm-law h)
    ; c₄ = c₅ ; c₅ = c₄ }
    where open Config₃₉ cfg

  module _ {a b c : Fin (suc n)} (cfg : Config₃₉ a b c) where
    open Config₃₉ cfg

    private
      a₁ b₁ : Fin (suc n)
      a₁ = a ∧ (b ∨ c)
      b₁ = b ∧ (a ∨ c)

    a₁<a : a ∧ (b ∨ c) < a
    a₁<a = ∧-lowerˡ , λ e → c₄ (subst (_≤ b ∨ c) e ∧-lowerʳ)

    -- The meet of the new elements is the meet of the old ones.
    a₁∧b₁≡ : a₁ ∧ b₁ ≡ a ∧ b
    a₁∧b₁≡ = ≤-antisym (∧-mono ∧-lowerˡ ∧-lowerˡ)
                       (∧-greatest (∧-greatest ∧-lowerˡ (≤∨ˡ ∧-lowerʳ)) (∧-greatest ∧-lowerʳ (≤∨ˡ ∧-lowerˡ)))

    -- The new (3).
    shrink-c₃ : ¬ a₁ ∧ b₁ ≤ c
    shrink-c₃ h = c₃ (subst (_≤ c) a₁∧b₁≡ h)

    -- The new (4), by (W).
    shrink-c₄ : ¬ a₁ ≤ b₁ ∨ c
    shrink-c₄ h = cases (W a (b ∨ c) b₁ c h)
      where
      cases : (a ≤ b₁ ∨ c ⊎ b ∨ c ≤ b₁ ∨ c) ⊎ (a₁ ≤ b₁ ⊎ a₁ ≤ c) → ⊥
      cases (inj₁ (inj₁ a≤))    = c₄ (≤-trans a≤ (∨-monoˡ ∧-lowerˡ))
      cases (inj₁ (inj₂ s≤))    = c₅ (≤-trans ∨-upperˡ (≤-trans s≤ (∨-least ∧-lowerʳ ∨-upperʳ)))
      cases (inj₂ (inj₁ a₁≤b₁)) = c₂ (≤-trans (∧-monoʳ (∨-least ∨-upperʳ (≤∨ˡ ∧-lowerʳ))) (≤-trans a₁≤b₁ ∧-lowerˡ))
      cases (inj₂ (inj₂ a₁≤c))  = c₃ (≤-trans (∧-greatest ∧-lowerˡ (≤∨ˡ ∧-lowerʳ)) a₁≤c)

    -- The new (1): b ∧ (c ∨ (a ∧ b)) lies below the left side and not below a.
    shrink-c₁ : ¬ b₁ ∧ (c ∨ (a₁ ∧ b₁)) ≤ a₁
    shrink-c₁ h = c₁ (≤-trans lower (≤-trans h ∧-lowerˡ))
      where
      lower : b ∧ (c ∨ (a ∧ b)) ≤ b₁ ∧ (c ∨ (a₁ ∧ b₁))
      lower = ∧-greatest (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ (∨-least ∨-upperʳ (≤∨ˡ ∧-lowerˡ))))
                         (subst (λ x → b ∧ (c ∨ (a ∧ b)) ≤ c ∨ x) (sym a₁∧b₁≡) ∧-lowerʳ)

  -- The configuration at a ∧ (b ∨ c), b ∧ (a ∨ c).
  shrink₃₉ : ∀ {a b c} → Config₃₉ a b c → Config₃₉ (a ∧ (b ∨ c)) (b ∧ (a ∨ c)) c
  shrink₃₉ {a} {b} {c} cfg = record
    { c₁ = shrink-c₁ cfg
    ; c₂ = λ h → shrink-c₁ (swap₃₉ cfg) (subst (λ x → (a ∧ (b ∨ c)) ∧ (c ∨ x) ≤ b ∧ (a ∨ c)) ∧-comm-law h)
    ; c₃ = shrink-c₃ cfg
    ; c₄ = shrink-c₄ cfg
    ; c₅ = shrink-c₄ (swap₃₉ cfg) }

  -- Lemma 5.39: the configuration does not exist, by well-founded induction on a.
  no-config₃₉ : ∀ {a b c} → Config₃₉ a b c → ⊥
  no-config₃₉ {a} = go a (<-acc a)
    where
    go : ∀ a → Acc _<_ a → ∀ {b c} → Config₃₉ a b c → ⊥
    go a (acc smaller) cfg = go _ (smaller (a₁<a cfg)) (shrink₃₉ cfg)
```

#### Lemma 5.40

With `c = a₀ ∧ b₀`, the book checks the five conditions of the dual of Lemma
5.39 for `a, b, c`: `a ≰ b ∨ c` and `b ≰ a ∨ c` since `b ∨ c ≤ b₀` and
`a ∨ c ≤ a₀`; `c ≰ a ∨ b` by (W), whose disjuncts fail by (5), (6), (7) and (8);
and `b ∧ c ≰ a`, `a ∧ c ≰ b` by (7) and (8), since `b ∧ c = b ∧ a₀` and
`a ∧ c = a ∧ b₀`.  In the dual lattice, the lattice of the tables swapped, these
are the conditions of `Config₃₉ a b c`, each read through the converse order.

```agda
module ConfigurationsDual {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                          (laws : LatticeTableLaws _∧_ _∨_)
                          (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open JoinDependency laws
  open Order laws
  open Configurations laws w using ( W )
  module 𝒟 = Configurations (dual-laws laws) (W-dual w)

  -- The configuration of Lemma 5.40.
  record Config₄₀ (a a₀ b b₀ : Fin (suc n)) : Type where
    field
      a≤a₀   : a ≤ a₀
      b≤b₀   : b ≤ b₀
      a≰b₀   : ¬ a ≤ b₀
      b≰a₀   : ¬ b ≤ a₀
      a₀≰    : ¬ a₀ ≤ a ∨ b
      b₀≰    : ¬ b₀ ≤ a ∨ b
      a₀∧b≰  : ¬ a₀ ∧ b ≤ a
      a∧b₀≰  : ¬ a ∧ b₀ ≤ b

  -- Lemma 5.40: the configuration does not exist, through the dual of Lemma 5.39.
  no-config₄₀ : ∀ {a a₀ b b₀} → Config₄₀ a a₀ b b₀ → ⊥
  no-config₄₀ {a} {a₀} {b} {b₀} cfg = 𝒟.no-config₃₉ {a} {b} {c} (record
    { c₁ = λ h → a≰b∨c (≤-trans (≤ᵈ→ h) (∨-monoʳ ∧-lowerˡ))
    ; c₂ = λ h → b≰a∨c (≤-trans (≤ᵈ→ h) (∨-monoʳ ∧-lowerˡ))
    ; c₃ = λ h → c≰a∨b (≤ᵈ→ h)
    ; c₄ = λ h → a₀∧b≰ (≤-trans (∧-greatest ∧-lowerʳ (∧-greatest ∧-lowerˡ (∧ʳ≤ b≤b₀))) (≤ᵈ→ h))
    ; c₅ = λ h → a∧b₀≰ (≤-trans (∧-greatest ∧-lowerˡ (∧-greatest (∧ˡ≤ a≤a₀) ∧-lowerʳ)) (≤ᵈ→ h)) })
    where
    open Config₄₀ cfg

    c : Fin (suc n)
    c = a₀ ∧ b₀

    a≰b∨c : ¬ a ≤ b ∨ c
    a≰b∨c h = a≰b₀ (≤-trans h (∨-least b≤b₀ ∧-lowerʳ))

    b≰a∨c : ¬ b ≤ a ∨ c
    b≰a∨c h = b≰a₀ (≤-trans h (∨-least a≤a₀ ∧-lowerˡ))

    -- c ≰ a ∨ b, by (W).
    c≰a∨b : ¬ c ≤ a ∨ b
    c≰a∨b h = cases (W a₀ b₀ a b h)
      where
      cases : (a₀ ≤ a ∨ b ⊎ b₀ ≤ a ∨ b) ⊎ (c ≤ a ⊎ c ≤ b) → ⊥
      cases (inj₁ (inj₁ a₀≤))  = a₀≰ a₀≤
      cases (inj₁ (inj₂ b₀≤))  = b₀≰ b₀≤
      cases (inj₂ (inj₁ c≤a))  = a₀∧b≰ (≤-trans (∧-monoʳ b≤b₀) c≤a)
      cases (inj₂ (inj₂ c≤b))  = a∧b₀≰ (≤-trans (∧-monoˡ a≤a₀) c≤b)
```
