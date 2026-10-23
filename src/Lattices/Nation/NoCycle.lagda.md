---
layout: default
file: "src/Lattices/Nation/NoCycle.lagda.md"
title: "Lattices.Nation.NoCycle module"
date: "2026-10-22"
author: "the agda-algebras development team"
check-cost: heavy
---

### Lemma 5.54: an S-lattice contains no C-cycle

This is the [Lattices.Nation.NoCycle][] module of the [agda-lattices][]
library.

Lemma 5.54 of [Freese, Ježek, and Nation (1995)][] (pp. 125 and 126) closes
Section V.3: a finite lattice with both semidistributive laws and (W) has no
C-cycle.  A C-cycle yields a minimal one ([Lattices.Nation.Cycle][]), whose
steps are A's and B's; not all are A's, since an A descends, and not all are
B's, since κ ascends along a B (Lemma 2.63), so the cycle may be read from a
member that starts a run of B's, as `q₁₀ B … B q₁ₖ₁ A … A q₂₀ B … A q₁₀`.  The
main argument takes the largest block start `qᵢ₀` with `qᵢ₀₋₋ ≤ q₁₀₋₋` and
extends the kept chain of Lemma 5.51 block by block from it, Lemmas 5.44 to
5.46 and 5.36 showing at each block that its run of A's is a single A₂ and
that `qᵢ₀ ≤ κ` of the next block's start.  Read from every run of B's in
turn, this shows that every run of A's is a single A₂; read in the dual
lattice, where B's become A's, that every run of B's is a single B; and, with
Lemma 5.50, that no B is a B₂.  The cycle is then one Lemma 5.53 excludes.

The module is generic in the lattice, so the dual lattice's instance is a
reference to it at the swapped tables; the one fact the final argument needs
from the dual is its parameter (`Final`{.AgdaModule}), and
[Lattices.Nation.Lemma554][] supplies it.  Two of the book's steps are read
differently.  When the block start `qᵢ₀` is the base itself, the subsequences
to which the book applies Lemmas 5.44 and 5.45 at the last block end at the
base again and so repeat their first member; here the chain is read from its
second member, in the rotation of the cycle that starts there
(`AtEnd`{.AgdaModule}, `end-case`{.AgdaFunction}), and the conclusion
contradicts (B1) in place of the choice of `qᵢ₀`.  And where the book (p. 125)
has `p_{jm_j}` "either `q_{i+1,0}` or `q₁₀`", the member is `q_{j+1,0}` or
`q₁₀`.

The module checks in 32.0 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).  Its cost puts it under
the barrel policy: the front matter carries `check-cost: heavy`, and no barrel
imports it.  Most of the time is conversion between the copies of the same
relations that different modules' openings of `Kappa`{.AgdaModule} and
`Cycles`{.AgdaModule} create, which Agda unfolds before comparing.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.NoCycle where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.DivMod                        using ( _%_ ; n%n≡0 )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n ; m≤n⇒m<n∨m≡n ; ≰⇒> ; n≢0⇒n>0 ; +-suc ; +-comm
                                                         ; +-identityʳ ; m∸n+n≡m ; m+n∸n≡m ; m+[n∸m]≡n ; m≤m+n ; m≤n+m
                                                         ; +-∸-assoc ; +-assoc ; +-monoʳ-< ; +-monoʳ-≤ ; m∸n≤m
                                                         ; ∸-monoˡ-< ; ∸-monoˡ-≤ ; ∸-monoʳ-≤ ; ∸-monoʳ-< ; m<m+n ; m+n∸m≡n
                                                         ; m+n≤o⇒m≤o∸n ; 1+n≢n ; suc-injective )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-reflexive to ≤ℕ-reflexive
                                                            ; ≤-trans to ≤ℕ-trans ; <-trans to <ℕ-trans
                                                            ; <-≤-trans to <ℕ-≤-trans ; ≤-<-trans to ≤ℕ-<-trans
                                                            ; <-irrefl to <ℕ-irrefl ; _≤?_ to _≤ℕ?_ ; _≟_ to _≟ℕ_
                                                            ; ≤-antisym to ≤ℕ-antisym )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Unit.Base                         using ( ⊤ ; tt )
import Data.List.Relation.Unary.All as All
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; _×-dec_ ; decidable-stable )

-- Imports from this library ----------------------------------------------------
import Lattices.Nation.Alternating   as AlternatingModule
import Lattices.Nation.BType         as BTypeModule
import Lattices.Nation.Lemma551      as Lemma551Module
import Lattices.Nation.Subsequences  as SubsequencesModule
open import Lattices.Nation.Cycle           using ( module Cycles )
open import Lattices.Nation.Kappa           using ( module Kappa )
open import Lattices.Semidistributive       using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table                  using ( LatticeTableLaws ; tableLattice )
```

#### The steps of a minimal cycle

```agda
module NoCycle {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
               (laws : LatticeTableLaws _∧_ _∨_)
               (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
               (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open Cycles laws sd w
  module BT = BTypeModule.BType laws sd w
  open BT using ( B→κ< ; least-index ; greatest-index ; after ; after-≤ ; after-+ ; after-mono ; after-bound )
  module L551 = Lemma551Module.Lemma551 laws sd w
  module Subs = SubsequencesModule.Subsequences laws sd w

  -- A member is not both A- and B-related to another.
  A∧B : ∀ {a b} → a A b → a B b → ⊥
  A∧B aAb aBb = B→≱ aBb (proj₁ (A→< aAb))

  -- An A₁ is not an A₂.
  A₁∧A₂ : ∀ {a b} → a A₁ b → a A₂ b → ⊥
  A₁∧A₂ (_ , lt) (_ , e) = proj₂ lt (sym e)

  -- The lower cover is monotone: every element strictly below a is strictly below b ≥ a.
  ₋-mono : ∀ {a b} → a ≤ b → a ₋ ≤ b ₋
  ₋-mono {a} {b} a≤b = ∨*-least (All.tabulate λ c∈ → <→≤₋ (<-≤-trans (∈below⁻ c∈) a≤b)) (⊥ᴸ-least (b ₋))

  module Steps (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞 using ( at ; at-wrap ; step )

    kc : ℕ
    kc = MinimalCycle.k 𝒞

    -- The kind of each step.
    IsA IsB : ℕ → Type
    IsA t = at t A at (suc t)
    IsB t = at t B at (suc t)

    IsA₂ : ℕ → Type
    IsA₂ t = at t A₂ at (suc t)

    isA? : ∀ t → Dec (IsA t)
    isA? t = at t A? at (suc t)

    isB? : ∀ t → Dec (IsB t)
    isB? t = at t B? at (suc t)

    kind : ∀ t → t ≤ℕ kc → IsA t ⊎ IsB t
    kind t t≤k = step t t≤k

    ¬A→B : ∀ {t} → t ≤ℕ kc → ¬ IsA t → IsB t
    ¬A→B t≤k ¬a = from (kind _ t≤k)
      where
      from : IsA _ ⊎ IsB _ → IsB _
      from (inj₁ a) = ⊥-elim (¬a a)
      from (inj₂ b) = b

    ¬B→A : ∀ {t} → t ≤ℕ kc → ¬ IsB t → IsA t
    ¬B→A t≤k ¬b = from (kind _ t≤k)
      where
      from : IsA _ ⊎ IsB _ → IsA _
      from (inj₁ a) = a
      from (inj₂ b) = ⊥-elim (¬b b)

    -- Not every step is an A: an A descends, and the cycle returns to its base.
    all-A : (∀ t → t ≤ℕ kc → IsA t) → ⊥
    all-A As = <-irrefl (subst (_< at 0) at-wrap (descent kc ≤ℕ-refl))
      where
      descent : ∀ t → t ≤ℕ kc → at (suc t) < at 0
      descent zero     _    = A→< (As 0 z≤n)
      descent (suc t)  st≤k = <-≤-trans (A→< (As (suc t) st≤k)) (proj₁ (descent t (≤ℕ-trans (n≤1+n t) st≤k)))

    -- Nor is every step a B: κ ascends along a B (Lemma 2.63).
    all-B : (∀ t → t ≤ℕ kc → IsB t) → ⊥
    all-B Bs = <-irrefl (subst (λ z → κ (at 0) < κ z) at-wrap (ascent kc ≤ℕ-refl))
      where
      ascent : ∀ t → t ≤ℕ kc → κ (at 0) < κ (at (suc t))
      ascent zero     _    = B→κ< (Bs 0 z≤n)
      ascent (suc t)  st≤k = <-≤-trans (ascent t (≤ℕ-trans (n≤1+n t) st≤k)) (proj₁ (B→κ< (Bs (suc t) st≤k)))

    -- A bounded search: a step of either kind that does not hold everywhere exists.
    search : (P : ℕ → Type) (P? : ∀ t → Dec (P t)) → ∀ m → (∀ t → t ≤ℕ m → ¬ P t → ⊥ → ⊥)
           → ¬ (∀ t → t ≤ℕ m → ¬ P t) → Σ ℕ λ t → t ≤ℕ m × P t
    search P P? zero    _ ne = from (P? 0)
      where
      from : Dec (P 0) → Σ ℕ λ t → t ≤ℕ 0 × P t
      from (yes p) = 0 , z≤n , p
      from (no ¬p) = ⊥-elim (ne λ { zero _ → ¬p ; (suc t) () })
    search P P? (suc m) _ ne = from (P? (suc m))
      where
      from : Dec (P (suc m)) → Σ ℕ λ t → t ≤ℕ suc m × P t
      from (yes p) = suc m , ≤ℕ-refl , p
      from (no ¬p) = let (t , t≤m , pt) = search P P? m (λ _ _ _ x → x) λ none → ne (extend none)
                     in t , ≤ℕ-trans t≤m (n≤1+n m) , pt
        where
        extend : (∀ t → t ≤ℕ m → ¬ P t) → ∀ t → t ≤ℕ suc m → ¬ P t
        extend none t t≤sm pt = cases (m≤n⇒m<n∨m≡n t≤sm)
          where
          cases : t <ℕ suc m ⊎ t ≡ suc m → ⊥
          cases (inj₁ lt) = none t (s≤s⁻¹ lt) pt
          cases (inj₂ e)  = ¬p (subst P e pt)

    some-A : Σ ℕ λ t → t ≤ℕ kc × IsA t
    some-A = search IsA isA? kc (λ _ _ _ x → x) λ none → all-B λ t t≤k → ¬A→B t≤k (none t t≤k)

    some-B : Σ ℕ λ t → t ≤ℕ kc × IsB t
    some-B = search IsB isB? kc (λ _ _ _ x → x) λ none → all-A λ t t≤k → ¬B→A t≤k (none t t≤k)

    -- The least B step from the base, given one: every earlier step is an A.
    first-B : Σ ℕ λ s → s ≤ℕ kc × IsB s × (∀ t → t <ℕ s → IsA t)
    first-B = let (b , b≤k , Bb) = some-B
                  (s , s≤b , Bs , least) = least-index isB? b Bb
              in s , ≤ℕ-trans s≤b b≤k , Bs , λ t t<s → ¬B→A (≤ℕ-trans (<⇒≤ (<ℕ-≤-trans t<s s≤b)) b≤k) (least t t<s)
```

The conclusions of the main argument below, for a cycle whose first step is
a B and whose last step is an A: the last step is an A₂ preceded by a B, which
is not a B₂ when an A precedes it.

```agda
  record Result (𝒞 : MinimalCycle) : Type where
    field
      k′   : ℕ
      k≡   : MinimalCycle.k 𝒞 ≡ suc k′
      A₂k  : Steps.IsA₂ 𝒞 (MinimalCycle.k 𝒞)
      Bk′  : Steps.IsB 𝒞 k′
      noB₂ : ∀ {k″} → k′ ≡ suc k″ → Steps.IsA 𝒞 k″
           → ¬ (MinimalCycleProperties.at 𝒞 k′ B₂ MinimalCycleProperties.at 𝒞 (suc k′))
```

A step of a cycle may be read through equations of its two members
(`→IsA`{.AgdaFunction}, `IsB→`{.AgdaFunction}); [Lattices.Nation.Lemma554][]
uses them to pass between a cycle and its dual.

```agda
  →IsA : (𝒞 : MinimalCycle) → ∀ i {x y} → MinimalCycleProperties.at 𝒞 i ≡ x → MinimalCycleProperties.at 𝒞 (suc i) ≡ y
       → x A y → Steps.IsA 𝒞 i
  →IsA 𝒞 i refl refl h = h

  IsB→ : (𝒞 : MinimalCycle) → ∀ i {x y} → MinimalCycleProperties.at 𝒞 i ≡ x → MinimalCycleProperties.at 𝒞 (suc i) ≡ y
       → Steps.IsB 𝒞 i → x B y
  IsB→ 𝒞 i refl refl h = h
```

#### A base that starts a run of B's

From a cycle whose first step is an A, rotating to its first B gives a cycle
whose first step is a B and whose last step is an A; the A's before the first
B become the last steps of the rotation.

```agda
  module ToBase (𝒞₁ : MinimalCycle) (A0 : Steps.IsA 𝒞₁ 0) where
    open Steps 𝒞₁ using ( kc ; IsA ; IsB ; first-B )
    module 𝒫₁ = MinimalCycleProperties 𝒞₁
    open Rotation 𝒞₁ using ( at-rotate-≤ ; at-rotate-≤′ ; at-rotate-wrap )

    s : ℕ
    s = proj₁ first-B

    s≤k : s ≤ℕ kc
    s≤k = proj₁ (proj₂ first-B)

    Bs : IsB s
    Bs = proj₁ (proj₂ (proj₂ first-B))

    As : ∀ t → t <ℕ s → IsA t
    As = proj₂ (proj₂ (proj₂ first-B))

    -- s ≥ 1, as the first step is an A and not a B.
    1≤s : 1 ≤ℕ s
    1≤s = from (m≤n⇒m<n∨m≡n (z≤n {s}))
      where
      from : 0 <ℕ s ⊎ 0 ≡ s → 1 ≤ℕ s
      from (inj₁ lt) = lt
      from (inj₂ e)  = ⊥-elim (A∧B A0 (subst IsB (sym e) Bs))

    s′ : ℕ
    s′ = s ∸ 1

    s≡ : s ≡ suc s′
    s≡ = sym (trans (sym (+-comm s′ 1)) (m∸n+n≡m 1≤s))

    𝒞₂ : MinimalCycle
    𝒞₂ = rotate 𝒞₁ s

    module 𝒫₂ = MinimalCycleProperties 𝒞₂

    -- The members of the rotation: at₂ i is at₁ (s + i) up to the base, and at₁ (s ∸ 1) at the end.
    at₂-0 : 𝒫₂.at 0 ≡ 𝒫₁.at s
    at₂-0 = trans (at-rotate-≤ s (subst (_≤ℕ kc) (sym (+-identityʳ s)) s≤k)) (cong 𝒫₁.at (+-identityʳ s))

    at₂-1 : 𝒫₂.at 1 ≡ 𝒫₁.at (suc s)
    at₂-1 = trans (at-rotate-≤′ s (≤ℕ-trans 1≤s s≤k) (subst (_≤ℕ suc kc) (sym (+-comm s 1)) (s≤s s≤k))) (cong 𝒫₁.at (+-comm s 1))

    at₂-k : 𝒫₂.at kc ≡ 𝒫₁.at s′
    at₂-k = at-rotate-wrap s s′ ≤ℕ-refl (trans (cong (_+ kc) s≡) (sym (+-suc s′ kc))) (≤ℕ-trans (n≤1+n s′) (subst (_≤ℕ kc) s≡ s≤k))

    at₂-sk : 𝒫₂.at (suc kc) ≡ 𝒫₁.at s
    at₂-sk = trans 𝒫₂.at-wrap at₂-0

    -- The first step of the rotation is the B, and its last step the A before it.
    B0 : 𝒫₂.at 0 B 𝒫₂.at 1
    B0 = subst₂ _B_ (sym at₂-0) (sym at₂-1) Bs

    Ak : 𝒫₂.at kc A 𝒫₂.at (suc kc)
    Ak = subst₂ _A_ (sym at₂-k) (sym at₂-sk) (subst (λ z → 𝒫₁.at s′ A 𝒫₁.at z) (sym s≡) (As s′ (≤ℕ-reflexive (sym s≡))))

    -- When two A's precede the B, the step before the last is an A too.
    module TwoBefore (s″ : ℕ) (s′≡ : s′ ≡ suc s″) where
      kc′ : ℕ
      kc′ = kc ∸ 1

      kc≡ : kc ≡ suc kc′
      kc≡ = sym (trans (sym (+-comm kc′ 1)) (m∸n+n≡m (≤ℕ-trans 1≤s s≤k)))

      at₂-k′ : 𝒫₂.at kc′ ≡ 𝒫₁.at s″
      at₂-k′ = at-rotate-wrap s s″ (≤ℕ-trans (n≤1+n kc′) (≤ℕ-reflexive (sym kc≡))) eq
                              (≤ℕ-trans (n≤1+n s″) (≤ℕ-trans (≤ℕ-reflexive (sym s′≡)) (≤ℕ-trans (n≤1+n s′) (subst (_≤ℕ kc) s≡ s≤k))))
        where
        eq : s + kc′ ≡ s″ + suc kc
        eq = trans (cong (_+ kc′) (trans s≡ (cong suc s′≡)))
                   (sym (trans (cong (s″ +_) (cong suc kc≡)) (trans (+-suc s″ (suc kc′)) (cong suc (+-suc s″ kc′)))))

      Ak′ : 𝒫₂.at kc′ A 𝒫₂.at (suc kc′)
      Ak′ = subst₂ _A_ (sym at₂-k′) (sym (trans (cong 𝒫₂.at (sym kc≡)) (trans at₂-k (cong 𝒫₁.at s′≡))))
                       (As s″ (subst (suc s″ ≤ℕ_) (sym (trans s≡ (cong suc s′≡))) (n≤1+n (suc s″))))
```

#### The main argument

Fix a minimal cycle whose first step is a B and whose last step is an A.  A
*block start* is the base or a B preceded by an A; the block start `s₀` is the
largest with `at s₀ ₋₋ ≤ at 0 ₋₋`, so that no later block start `t` has
`at t ₋₋ ≤ at 0 ₋₋`.  The members from `s₀` on are the flat family `x`, and
the kept chain of Lemma 5.51 grows from the run of B's at `s₀` block by
block.

```agda
  module Main (𝒞 : MinimalCycle) (B0 : Steps.IsB 𝒞 0) (Ak : Steps.IsA 𝒞 (Steps.kc 𝒞)) where
    open Steps 𝒞
    open MinimalCycleProperties 𝒞 hiding ( k )
    open BT.InCycle 𝒞 using ( BType ; BType-shift ; BType-cong ; lemma-5-36 )
    module L551C = L551.InCycle 𝒞
    module SubsC = Subs.InCycle 𝒞

    -- A block start: the base, or a B preceded by an A.
    IsStart : ℕ → Type
    IsStart zero     = ⊤
    IsStart (suc t)  = IsA t × IsB (suc t)

    isStart? : ∀ t → Dec (IsStart t)
    isStart? zero     = yes tt
    isStart? (suc t)  = isA? t ×-dec isB? (suc t)

    -- The largest block start s₀ with at s₀ ₋₋ ≤ at 0 ₋₋.
    P : ℕ → Type
    P t = IsStart t × ((at t ₋) ₋ ≤ (at 0 ₋) ₋)

    P? : ∀ t → Dec (P t)
    P? t = isStart? t ×-dec (_ ≤? _)

    private
      found : Σ ℕ λ j → 0 ≤ℕ j × j ≤ℕ kc × P j × (∀ t → j <ℕ t → t ≤ℕ kc → ¬ P t)
      found = greatest-index P? kc 0 z≤n (tt , ≤-refl)

    s₀ : ℕ
    s₀ = proj₁ found

    s₀≤k : s₀ ≤ℕ kc
    s₀≤k = proj₁ (proj₂ (proj₂ found))

    s₀-start : IsStart s₀
    s₀-start = proj₁ (proj₁ (proj₂ (proj₂ (proj₂ found))))

    s₀₋₋≤ : (at s₀ ₋) ₋ ≤ (at 0 ₋) ₋
    s₀₋₋≤ = proj₂ (proj₁ (proj₂ (proj₂ (proj₂ found))))

    maximal : ∀ t → s₀ <ℕ t → t ≤ℕ kc → IsStart t → ¬ (at t ₋) ₋ ≤ (at 0 ₋) ₋
    maximal t s₀<t t≤k st le = proj₂ (proj₂ (proj₂ (proj₂ found))) t s₀<t t≤k (st , le)

    -- The members from s₀ on, read at the indices up to N = kc ∸ s₀.
    N : ℕ
    N = kc ∸ s₀

    x : ℕ → Fin (suc n)
    x t = at (s₀ + t)

    pos≤k : ∀ {i} → i ≤ℕ N → s₀ + i ≤ℕ kc
    pos≤k i≤N = subst (s₀ + _ ≤ℕ_) (m+[n∸m]≡n s₀≤k) (+-monoʳ-≤ s₀ i≤N)

    sub : Sub N x
    sub = Sub-restrict whole (s₀ +_) (λ i<j _ → +-monoʳ-< s₀ i<j) pos≤k

    module F = L551C.Flat sub

    -- A step of x, as a step of the cycle.
    xB : ∀ {t} → IsB (s₀ + t) → x t B x (suc t)
    xB {t} b = subst (λ z → x t B at z) (sym (+-suc s₀ t)) b

    xA : ∀ {t} → IsA (s₀ + t) → x t A x (suc t)
    xA {t} a = subst (λ z → x t A at z) (sym (+-suc s₀ t)) a

    -- The end of the run of B's from a B at s: the least u > s with an A, every step between a B.
    run-end : ∀ s → s ≤ℕ kc → IsB s → Σ ℕ λ d → 0 <ℕ d × s + d ≤ℕ kc × IsA (s + d) × (∀ i → i <ℕ d → IsB (s + i))
    run-end s s≤k Bs =
      let (d , d≤ , Ad , least) = least-index (λ i → isA? (s + i)) (kc ∸ s) (subst IsA (sym (m+[n∸m]≡n s≤k)) Ak)
      in d , positive d Ad , subst (s + d ≤ℕ_) (m+[n∸m]≡n s≤k) (+-monoʳ-≤ s d≤) , Ad
         , λ i i<d → ¬A→B (≤ℕ-trans (+-monoʳ-≤ s (<⇒≤ (<ℕ-≤-trans i<d d≤))) (≤ℕ-reflexive (m+[n∸m]≡n s≤k))) (least i i<d)
      where
      positive : ∀ d → IsA (s + d) → 0 <ℕ d
      positive zero    A0 = ⊥-elim (A∧B (subst IsA (+-identityʳ s) A0) Bs)
      positive (suc d) _  = s≤s z≤n
```

The runs of A's at the end of the cycle lead back to the base, which the kept
chain cannot include as a further member: the lemmas that read the chain
with the members after its last are applied in the rotation of the cycle to
`s₀`, or, when `s₀` is the base itself, to the member after it, the chain
then read from its second member (`AtEnd`{.AgdaModule}).

```agda
    -- The chain's first member, in the two readings, against a conclusion p₋ < q₀₋ with p the base.
    module EndContra {s′ : ℕ} {keep : ℕ → ℕ} (ch : F.Chain (suc s′) keep) where
      open F.Chain ch

      -- s₀ ≥ 1, q₀ = at s₀: at 0 ₋ < at s₀ ₋ puts at 0 ₋ below at s₀ ₋₋ ≤ at 0 ₋₋.
      contra-pos : at 0 ₋ < x (keep 0) ₋ → ⊥
      contra-pos lt = proj₂ (at-₋irr 𝒞 0 z≤n) (≤-antisym (₋≤ (at 0 ₋)) (≤-trans (<→≤₋ lt′) s₀₋₋≤))
        where
        lt′ : at 0 ₋ < at s₀ ₋
        lt′ = subst (λ z → at 0 ₋ < at z ₋) (trans (cong (s₀ +_) keep0) (+-identityʳ s₀)) lt

      -- s₀ = 0, the chain read from its second member: at 0 ₋ < x (keep 1) ₋ contradicts (B1).
      contra-zero : s₀ ≡ 0 → at 0 ₋ < x (keep 1) ₋ → ⊥
      contra-zero e lt = B1 (s≤s z≤n) (≤-trans (≤-reflexive′ (cong (λ z → at z ₋) x0≡)) (≤-trans (proj₁ lt) (₋≤ (x (keep 1)))))
        where
        open BType bt
        x0≡ : s₀ + keep 0 ≡ 0
        x0≡ = trans (cong₂ _+_ e keep0) refl

    -- The chain read in the rotation by r = s₀ + d, from its member d, with e′ + 1 members after its
    -- last, u, the last of them the base again (u + e′ = kc).
    module AtEnd {s′ : ℕ} {keep : ℕ → ℕ} (ch : F.Chain (suc s′) keep) (u : ℕ) (last : s₀ + keep (suc s′) ≡ u)
                 (r d : ℕ) (r≡ : r ≡ s₀ + d) (1≤r : 1 ≤ℕ r) (d≤ss′ : d ≤ℕ suc s′)
                 (e′ : ℕ) (end : e′ + u ≡ kc) where
      open F.Chain ch
      open Rotation 𝒞 using ( at-rotate-≤ ; at-rotate-≤′ )

      𝒞′ : MinimalCycle
      𝒞′ = rotate 𝒞 r

      module 𝒫′ = MinimalCycleProperties 𝒞′

      L : ℕ
      L = suc s′ ∸ d

      d+L≡ : d + L ≡ suc s′
      d+L≡ = m+[n∸m]≡n d≤ss′

      -- Indices grow at least as fast as the reindexing.
      keep≥ : ∀ t → t ≤ℕ suc s′ → t ≤ℕ keep t
      keep≥ zero     _     = z≤n
      keep≥ (suc t)  st≤ss′ = ≤ℕ-trans (s≤s (keep≥ t (≤ℕ-trans (n≤1+n t) st≤ss′))) (mono (n<1+n t) st≤ss′)

      keepʳ : ℕ → ℕ
      keepʳ t = (s₀ + keep (d + t)) ∸ r

      c : ℕ
      c = suc u ∸ r

      y : ℕ → Fin (suc n)
      y t = 𝒫′.at (after keepʳ L c t)

      d+t≤ : ∀ {t} → t ≤ℕ L → d + t ≤ℕ suc s′
      d+t≤ {t} t≤L = subst (d + t ≤ℕ_) d+L≡ (+-monoʳ-≤ d t≤L)

      r≤pos : ∀ t → t ≤ℕ L → r ≤ℕ s₀ + keep (d + t)
      r≤pos t t≤L = subst (_≤ℕ s₀ + keep (d + t)) (sym r≡) (+-monoʳ-≤ s₀ (≤ℕ-trans (m≤m+n d t) (keep≥ (d + t) (d+t≤ t≤L))))

      pos≤kc : ∀ t → t ≤ℕ L → s₀ + keep (d + t) ≤ℕ kc
      pos≤kc t t≤L = pos≤k (bound (d+t≤ t≤L))

      u≤kc : u ≤ℕ kc
      u≤kc = subst (_≤ℕ kc) last (pos≤k (bound ≤ℕ-refl))

      r≤su : r ≤ℕ suc u
      r≤su = ≤ℕ-trans (r≤pos 0 z≤n) (≤ℕ-trans (+-monoʳ-≤ s₀ (keep-mono-≤ (d+t≤ z≤n))) (≤ℕ-trans (≤ℕ-reflexive last) (n≤1+n u)))
        where
        keep-mono-≤ : ∀ {t} → t ≤ℕ suc s′ → keep t ≤ℕ keep (suc s′)
        keep-mono-≤ {t} t≤ = from (m≤n⇒m<n∨m≡n t≤)
          where
          from : t <ℕ suc s′ ⊎ t ≡ suc s′ → keep t ≤ℕ keep (suc s′)
          from (inj₁ lt) = <⇒≤ (mono lt ≤ℕ-refl)
          from (inj₂ e)  = ≤ℕ-reflexive (cong keep e)

      -- Reading the chain's members.
      y-keep : ∀ t → t ≤ℕ L → y t ≡ x (keep (d + t))
      y-keep t t≤L = trans (cong 𝒫′.at (after-≤ keepʳ L c t≤L))
                           (trans (at-rotate-≤ r (subst (_≤ℕ kc) (sym (m+[n∸m]≡n (r≤pos t t≤L))) (pos≤kc t t≤L)))
                                  (cong at (m+[n∸m]≡n (r≤pos t t≤L))))

      y-0 : y 0 ≡ x (keep d)
      y-0 = trans (y-keep 0 z≤n) (cong (λ z → x (keep z)) (+-identityʳ d))

      y-L : y L ≡ at u
      y-L = trans (y-keep L ≤ℕ-refl) (trans (cong (λ z → x (keep z)) d+L≡) (cong at last))

      -- Reading the members after it: the l-th is at (l + suc u), the base again at l = e′.
      l+su≤ : ∀ {l} → l ≤ℕ e′ → l + suc u ≤ℕ suc kc
      l+su≤ {l} l≤e′ = subst (l + suc u ≤ℕ_) (trans (+-suc e′ u) (cong suc end)) (+-monoˡ-≤′ l≤e′)
        where
        +-monoˡ-≤′ : l ≤ℕ e′ → l + suc u ≤ℕ e′ + suc u
        +-monoˡ-≤′ h = subst₂ _≤ℕ_ (+-comm (suc u) l) (+-comm (suc u) e′) (+-monoʳ-≤ (suc u) h)

      l+c≤ : ∀ {l} → l ≤ℕ e′ → l + c ≤ℕ kc
      l+c≤ {l} l≤e′ = ≤ℕ-trans (≤ℕ-reflexive (sym (+-∸-assoc l r≤su)))
                               (≤ℕ-trans (∸-monoˡ-≤ r (l+su≤ l≤e′)) (∸-monoʳ-≤ (suc kc) 1≤r))

      y-extra : ∀ l → l ≤ℕ e′ → y (l + suc L) ≡ at (l + suc u)
      y-extra l l≤e′ = trans (cong 𝒫′.at (after-+ keepʳ L c l))
                             (trans (at-rotate-≤′ r (l+c≤ l≤e′) (subst (_≤ℕ suc kc) (sym eq) (l+su≤ l≤e′))) (cong at eq))
        where
        eq : r + (l + c) ≡ l + suc u
        eq = trans (sym (+-assoc r l c)) (trans (cong (_+ c) (+-comm r l)) (trans (+-assoc l r c) (cong (l +_) (m+[n∸m]≡n r≤su))))

      -- The family as a subsequence of the rotation.
      sub-y : 𝒫′.Sub (e′ + suc L) y
      sub-y = 𝒫′.Sub-restrict 𝒫′.whole (after keepʳ L c) (λ i<j _ → after-mono keepʳ L c monoʳ L<c i<j)
                                          (after-bound keepʳ L c boundʳ (subst (λ z → z + c ≤ℕ kc) (sym (m+n∸n≡m e′ (suc L))) (l+c≤ ≤ℕ-refl)))
        where
        monoʳ : ∀ {i j} → i <ℕ j → j ≤ℕ L → keepʳ i <ℕ keepʳ j
        monoʳ {i} {j} i<j j≤L = ∸-monoˡ-< (+-monoʳ-< s₀ (mono (+-monoʳ-< d i<j) (d+t≤ j≤L))) (r≤pos i (≤ℕ-trans (<⇒≤ i<j) j≤L))

        L<c : keepʳ L <ℕ c
        L<c = ∸-monoˡ-< (subst (_<ℕ suc u) (sym (trans (cong (λ z → s₀ + keep z) d+L≡) last)) (n<1+n u)) (r≤pos L ≤ℕ-refl)

        boundʳ : ∀ {i} → i ≤ℕ L → keepʳ i ≤ℕ kc
        boundʳ {i} i≤L = ≤ℕ-trans (m∸n≤m _ r) (pos≤kc i i≤L)

      -- The chain from its member d is a B-type sequence.
      bt-y : BType L y
      bt-y = BType-cong ≤ℕ-refl (λ t t≤L → y-keep t t≤L) (BType-shift d L (≤ℕ-reflexive d+L≡) bt)

      -- The same record for the rotation: B-type sequences do not depend on the cycle.
      module BT′ = BT.InCycle 𝒞′

      bt-y′ : BT′.BType L y
      bt-y′ = record { B1 = B1 ; B2 = B2 ; B3 = B3 ; B4 = B4 } where open BType bt-y
```

The loop over the blocks after `s₀`.  Its state at the end `u` of a block's
run of B's is the kept chain up to that block, with the A at `u`, and the
start of that block, whose first B is not a B₂ unless the block is the first;
the loop excludes an A₁ at `u` by Lemma 5.44 and a second A after it by Lemma
5.45 or 5.36, and otherwise extends the chain by the next block, whose start
lies below κ of `s₀`'s member by Lemma 5.46 and the choice of `s₀`.

```agda
    -- The state at the end u of a block's run of B's.
    record State (u : ℕ) : Type where
      field
        s′     : ℕ
        keep   : ℕ → ℕ
        chain  : F.Chain (suc s′) keep
        direct : keep (suc s′) ≡ suc (keep s′)
        last   : s₀ + keep (suc s′) ≡ u
        uA     : IsA u
        bstart : ℕ
        s₀≤b   : s₀ ≤ℕ bstart
        b<u    : bstart <ℕ u
        bB     : ∀ t → bstart ≤ℕ t → t <ℕ u → IsB t
        b-ok   : bstart ≡ s₀ ⊎ ¬ (at bstart B₂ at (suc bstart))

    1≤kc : 1 ≤ℕ kc
    1≤kc = from (m≤n⇒m<n∨m≡n (z≤n {kc}))
      where
      from : 0 <ℕ kc ⊎ 0 ≡ kc → 1 ≤ℕ kc
      from (inj₁ lt) = lt
      from (inj₂ e)  = ⊥-elim (A∧B (subst IsA (sym e) Ak) B0)

    -- The end of the run of A's from u: the next B, or the base when the run reaches it.
    arun-end : ∀ u → u ≤ℕ kc → IsA u → Σ ℕ λ v → u <ℕ v × v ≤ℕ suc kc × (∀ t → u ≤ℕ t → t <ℕ v → IsA t) × (v ≤ℕ kc → IsB v)
    arun-end u u≤k Au = go (kc ∸ u) u u≤k Au (m+[n∸m]≡n u≤k)
      where
      go : ∀ f t → t ≤ℕ kc → IsA t → t + f ≡ kc → Σ ℕ λ v → t <ℕ v × v ≤ℕ suc kc × (∀ t′ → t ≤ℕ t′ → t′ <ℕ v → IsA t′) × (v ≤ℕ kc → IsB v)
      go zero    t t≤k At e = suc t , n<1+n t , subst (suc t ≤ℕ_) (trans (sym (cong suc (+-identityʳ t))) (cong suc e)) ≤ℕ-refl
                            , (λ t′ t≤t′ t′<st → subst IsA (≤-antisym′ t≤t′ (s≤s⁻¹ t′<st)) At)
                            , λ st≤k → ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans st≤k (≤ℕ-reflexive (trans (sym e) (+-identityʳ t)))))
        where
        ≤-antisym′ : ∀ {a b} → a ≤ℕ b → b ≤ℕ a → a ≡ b
        ≤-antisym′ z≤n z≤n = refl
        ≤-antisym′ (s≤s p) (s≤s q) = cong suc (≤-antisym′ p q)
      go (suc f) t t≤k At e = decide (isB? (suc t))
        where
        st≤k : suc t ≤ℕ kc
        st≤k = subst (suc t ≤ℕ_) (trans (sym (+-suc t f)) e) (s≤s (m≤m+n t f))

        decide : Dec (IsB (suc t)) → Σ ℕ λ v → t <ℕ v × v ≤ℕ suc kc × (∀ t′ → t ≤ℕ t′ → t′ <ℕ v → IsA t′) × (v ≤ℕ kc → IsB v)
        decide (yes b) = suc t , n<1+n t , ≤ℕ-trans st≤k (n≤1+n kc)
                       , (λ t′ t≤t′ t′<st → subst IsA (≤-antisym′ t≤t′ (s≤s⁻¹ t′<st)) At) , λ _ → b
          where
          ≤-antisym′ : ∀ {a b} → a ≤ℕ b → b ≤ℕ a → a ≡ b
          ≤-antisym′ z≤n z≤n = refl
          ≤-antisym′ (s≤s p) (s≤s q) = cong suc (≤-antisym′ p q)
        decide (no ¬b) = let (v , st<v , v≤sk , all , next) = go f (suc t) st≤k (¬B→A st≤k ¬b) (trans (sym (+-suc t f)) e)
                         in v , <ℕ-trans (n<1+n t) st<v , v≤sk , (λ t′ t≤t′ t′<v → cases t′ t≤t′ t′<v all) , next
          where
          cases : ∀ t′ → t ≤ℕ t′ → t′ <ℕ _ → (∀ t″ → suc t ≤ℕ t″ → t″ <ℕ _ → IsA t″) → IsA t′
          cases t′ t≤t′ t′<v all = from (m≤n⇒m<n∨m≡n t≤t′)
            where
            from : t <ℕ t′ ⊎ t ≡ t′ → IsA t′
            from (inj₁ lt) = all t′ lt t′<v
            from (inj₂ eq) = subst IsA eq At

    -- Along a run of A's the members descend.
    arun-descent : ∀ u v → u ≤ℕ v → v ≤ℕ suc kc → (∀ t → u ≤ℕ t → t <ℕ v → IsA t) → at v ≤ at u
    arun-descent u v u≤v v≤sk As = go (v ∸ u) v u≤v (m+[n∸m]≡n u≤v) ≤ℕ-refl
      where
      go : ∀ f v′ → u ≤ℕ v′ → u + f ≡ v′ → (v′ ≤ℕ v) → at v′ ≤ at u
      go zero     v′ _ e _ = ≤-reflexive′ (cong at (trans (sym e) (+-identityʳ u)))
      go (suc f) v′ u≤v′ e v′≤v =
        ≤-trans (≤-reflexive′ (cong at e′))
                (≤-trans (proj₁ (A→< (As (u + f) (m≤m+n u f) uf<v))) (go f (u + f) (m≤m+n u f) refl (<⇒≤ uf<v)))
        where
        e′ : v′ ≡ suc (u + f)
        e′ = trans (sym e) (+-suc u f)

        uf<v : u + f <ℕ v
        uf<v = <ℕ-≤-trans (subst (u + f <ℕ_) (sym e′) (n<1+n (u + f))) v′≤v
```

The pieces of the loop body: readings of a chain with the members after it,
before the base (`FlatExt`{.AgdaModule}) or up to it (`AtEnd`{.AgdaModule}),
and the lemmas of Section V.3 applied to them.

```agda
    -- Indices of a kept chain grow at least as fast as its own.
    chain-keep≥ : ∀ {s′ keep} → F.Chain (suc s′) keep → ∀ t → t ≤ℕ suc s′ → t ≤ℕ keep t
    chain-keep≥ ch zero     _      = z≤n
    chain-keep≥ ch (suc t)  st≤ss′ =
      ≤ℕ-trans (s≤s (chain-keep≥ ch t (≤ℕ-trans (n≤1+n t) st≤ss′))) (F.Chain.mono ch (n<1+n t) st≤ss′)

    -- A block start is a B.
    start-B : ∀ t → IsStart t → IsB t
    start-B zero     _       = B0
    start-B (suc t)  (_ , b) = b

    -- A later block start whose lower cover's lower cover lies below at s₀ ₋₋ contradicts the choice of s₀.
    start-contra : ∀ t → s₀ <ℕ t → t ≤ℕ kc → IsStart t → (at t ₋) ₋ ≤ (at s₀ ₋) ₋ → ⊥
    start-contra t s₀<t t≤k st le = maximal t s₀<t t≤k st (≤-trans le s₀₋₋≤)

    -- A conclusion p₋ < q₀₋ for a member p of the run of A's from u contradicts the choice of s₀: the run
    -- descends, so its end, a later block start or the base, has its double lower cover below at s₀ ₋₋.
    run-contra : ∀ u → s₀ <ℕ u → ∀ v → u <ℕ v → v ≤ℕ suc kc → (∀ t → u ≤ℕ t → t <ℕ v → IsA t) → (v ≤ℕ kc → IsB v)
               → ∀ w → u ≤ℕ w → w ≤ℕ v → w ≤ℕ kc → at w ₋ < at s₀ ₋ → ⊥
    run-contra u s₀<u zero     ()
    run-contra u s₀<u (suc v′) u<v v≤sk runA nextB w u≤w w≤v w≤k lt = cases (m≤n⇒m<n∨m≡n v≤sk)
      where
      w₋₋< : (at w ₋) ₋ < (at s₀ ₋) ₋
      w₋₋< = <-≤-trans (at-₋irr 𝒞 w w≤k) (<→≤₋ lt)

      v≤w : at (suc v′) ≤ at w
      v≤w = arun-descent w (suc v′) w≤v v≤sk (λ t w≤t t<v → runA t (≤ℕ-trans u≤w w≤t) t<v)

      v₋₋< : (at (suc v′) ₋) ₋ < (at s₀ ₋) ₋
      v₋₋< = ≤-<-trans (₋-mono (₋-mono v≤w)) w₋₋<

      cases : suc v′ <ℕ suc kc ⊎ suc v′ ≡ suc kc → ⊥
      cases (inj₁ v<sk) = start-contra (suc v′) (<ℕ-≤-trans s₀<u (<⇒≤ u<v)) (s≤s⁻¹ v<sk)
                                       (runA v′ (s≤s⁻¹ u<v) (n<1+n v′) , nextB (s≤s⁻¹ v<sk)) (proj₁ v₋₋<)
      cases (inj₂ e)    = <-irrefl (<-≤-trans (subst (λ z → (z ₋) ₋ < (at s₀ ₋) ₋) (trans (cong at e) at-wrap) v₋₋<) s₀₋₋≤)

    -- Lemma 5.36 for three consecutive members, read in the rotation of the cycle to the first.
    three : ∀ t → suc (suc t) ≤ℕ suc kc → 2 ≤ℕ kc → IsA₂ t → IsA (suc t) → IsA₂ (suc t)
    three t sst≤ 2≤k A₂t At′ = subst₂ _A₂_ e₁ e₂ (proj₂ (BT′.lemma-5-36 sub3 A₂′ A′))
      where
      𝒞′ : MinimalCycle
      𝒞′ = rotate 𝒞 t

      module 𝒫′ = MinimalCycleProperties 𝒞′
      module BT′ = BT.InCycle 𝒞′
      open Rotation 𝒞 using ( at-rotate-≤′ )

      t+2 : t + 2 ≡ suc (suc t)
      t+2 = +-comm t 2

      rd : ∀ i → i ≤ℕ 2 → 𝒫′.at i ≡ at (t + i)
      rd i i≤2 = at-rotate-≤′ t (≤ℕ-trans i≤2 2≤k) (≤ℕ-trans (+-monoʳ-≤ t i≤2) (subst (_≤ℕ suc kc) (sym t+2) sst≤))

      e₀ : 𝒫′.at 0 ≡ at t
      e₀ = trans (rd 0 z≤n) (cong at (+-identityʳ t))

      e₁ : 𝒫′.at 1 ≡ at (suc t)
      e₁ = trans (rd 1 (s≤s z≤n)) (cong at (+-comm t 1))

      e₂ : 𝒫′.at 2 ≡ at (suc (suc t))
      e₂ = trans (rd 2 (s≤s (s≤s z≤n))) (cong at t+2)

      sub3 : 𝒫′.Sub 2 𝒫′.at
      sub3 = 𝒫′.Sub-prefix 𝒫′.whole 2≤k

      A₂′ : 𝒫′.at 0 A₂ 𝒫′.at 1
      A₂′ = subst₂ _A₂_ (sym e₀) (sym e₁) A₂t

      A′ : 𝒫′.at 1 A 𝒫′.at 2
      A′ = subst₂ _A_ (sym e₁) (sym e₂) At′

    -- The flat reading of a chain at u with e + 1 members after its last, all before the base.
    module FlatExt {s′ : ℕ} {keep : ℕ → ℕ} (ch : F.Chain (suc s′) keep) (u : ℕ) (last : s₀ + keep (suc s′) ≡ u)
                   (e : ℕ) (bnd : suc (e + u) ≤ℕ kc) where
      open F.Chain ch

      S c : ℕ
      S = suc s′
      c = suc (keep S)

      ext : ℕ → ℕ
      ext = after keep S c

      z : ℕ → Fin (suc n)
      z t = x (ext t)

      s₀+c : s₀ + c ≡ suc u
      s₀+c = trans (+-suc s₀ (keep S)) (cong suc last)

      e+c≤N : e + c ≤ℕ N
      e+c≤N = m+n≤o⇒m≤o∸n (e + c) (subst (_≤ℕ kc) eq bnd)
        where
        eq : suc (e + u) ≡ (e + c) + s₀
        eq = sym (trans (+-assoc e c s₀) (trans (cong (e +_) (trans (+-comm c s₀) s₀+c)) (+-suc e u)))

      sub-z : Sub (e + suc S) z
      sub-z = Sub-restrict sub ext (λ i<j _ → after-mono keep S c mono (n<1+n (keep S)) i<j)
                                   (after-bound keep S c bound (subst (λ t → t + c ≤ℕ N) (sym (m+n∸n≡m e (suc S))) e+c≤N))

      z-q : ∀ {t} → t ≤ℕ S → z t ≡ x (keep t)
      z-q t≤S = cong x (after-≤ keep S c t≤S)

      bt-z : BType S z
      bt-z = BType-cong {k = S} {j = S} {q = λ t → x (keep t)} {q′ = z} ≤ℕ-refl (λ t t≤S → z-q t≤S) bt

      z-0 : z 0 ≡ at s₀
      z-0 = trans (z-q z≤n) (cong at (trans (cong (s₀ +_) keep0) (+-identityʳ s₀)))

      z-S : z S ≡ at u
      z-S = trans (z-q ≤ℕ-refl) (cong at last)

      z-extra : ∀ l → z (l + suc S) ≡ at (suc (l + u))
      z-extra l = trans (cong x (after-+ keep S c l)) (cong at eq)
        where
        eq : s₀ + (l + c) ≡ suc (l + u)
        eq = trans (sym (+-assoc s₀ l c))
                   (trans (cong (_+ c) (+-comm s₀ l)) (trans (+-assoc l s₀ c) (trans (cong (l +_) s₀+c) (+-suc l u))))

    -- Lemma 5.44 in the flat reading: with an A₁ at u, at (u + 1) ₋ < at s₀ ₋.
    flat-5-44 : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) u (last : s₀ + keep (suc s′) ≡ u) → suc u ≤ℕ kc
              → at u A₁ at (suc u) → at (suc u) ₋ < at s₀ ₋
    flat-5-44 ch u last su≤k h = subst₂ (λ a b → a ₋ < b ₋) (FE.z-extra 0) FE.z-0 (SubsC.lemma-5-44 FE.sub-z FE.bt-z h′)
      where
      module FE = FlatExt ch u last 0 su≤k

      h′ : FE.z FE.S A₁ FE.z (suc FE.S)
      h′ = subst₂ _A₁_ (sym FE.z-S) (sym (FE.z-extra 0)) h

    -- Lemma 5.45 in the flat reading: with A₂'s at u and u + 1, at (u + 2) ₋ < at s₀ ₋.
    flat-5-45 : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) u (last : s₀ + keep (suc s′) ≡ u) → suc (suc u) ≤ℕ kc
              → at u A₂ at (suc u) → at (suc u) A₂ at (suc (suc u)) → at (suc (suc u)) ₋ < at s₀ ₋
    flat-5-45 ch u last ssu≤k h₁ h₂ =
      subst₂ (λ a b → a ₋ < b ₋) (FE.z-extra 1) FE.z-0 (SubsC.lemma-5-45 FE.S FE.sub-z FE.bt-z h₁′ h₂′)
      where
      module FE = FlatExt ch u last 1 ssu≤k

      h₁′ : FE.z FE.S A₂ FE.z (suc FE.S)
      h₁′ = subst₂ _A₂_ (sym FE.z-S) (sym (FE.z-extra 0)) h₁

      h₂′ : FE.z (suc FE.S) A₂ FE.z (suc (suc FE.S))
      h₂′ = subst₂ _A₂_ (sym (FE.z-extra 0)) (sym (FE.z-extra 1)) h₂

    -- Lemma 5.46 in the flat reading: with an A₂ at u, at (u + 1) B at s₀ failing and at s₀ ≰ κ(at (u + 1)),
    -- at (u + 1) ₋₋ < at s₀ ₋.
    flat-5-46 : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) u (last : s₀ + keep (suc s′) ≡ u) → suc u ≤ℕ kc
              → at u A₂ at (suc u) → ¬ (at (suc u) B at s₀) → ¬ at s₀ ≤ κ (at (suc u)) → (at (suc u) ₋) ₋ < at s₀ ₋
    flat-5-46 ch u last su≤k h ¬B ¬≤ =
      subst₂ (λ a b → (a ₋) ₋ < b ₋) (FE.z-extra 0) FE.z-0 (SubsC.lemma-5-46 FE.sub-z FE.bt-z h′ ¬B′ ¬≤′)
      where
      module FE = FlatExt ch u last 0 su≤k

      h′ : FE.z FE.S A₂ FE.z (suc FE.S)
      h′ = subst₂ _A₂_ (sym FE.z-S) (sym (FE.z-extra 0)) h

      ¬B′ : ¬ (FE.z (suc FE.S) B FE.z 0)
      ¬B′ = subst₂ (λ a b → ¬ (a B b)) (sym (FE.z-extra 0)) (sym FE.z-0) ¬B

      ¬≤′ : ¬ FE.z 0 ≤ κ (FE.z (suc FE.S))
      ¬≤′ = subst₂ (λ a b → ¬ a ≤ κ b) (sym FE.z-0) (sym (FE.z-extra 0)) ¬≤

    -- At the end, a conclusion at 0 ₋ < x (keep d) ₋ for the reading from member d (0 when s₀ ≥ 1, 1 when
    -- s₀ = 0) is a contradiction.
    end-case : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) → (∀ d → d ≤ℕ 1 → 1 ≤ℕ s₀ + d → at 0 ₋ < x (keep d) ₋) → ⊥
    end-case ch f = decide (s₀ ≟ℕ 0)
      where
      decide : Dec (s₀ ≡ 0) → ⊥
      decide (yes e) = EndContra.contra-zero ch e (f 1 ≤ℕ-refl (m≤n+m 1 s₀))
      decide (no ne) = EndContra.contra-pos ch (f 0 z≤n (subst (1 ≤ℕ_) (sym (+-identityʳ s₀)) (n≢0⇒n>0 ne)))

    -- Lemma 5.44 at the end: an A₁ at u = kc, to the base.
    end-5-44 : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) u (last : s₀ + keep (suc s′) ≡ u) → u ≡ kc
             → at u A₁ at (suc u) → ⊥
    end-5-44 {s′} {keep} ch u last u≡k h = end-case ch conclusion
      where
      conclusion : ∀ d → d ≤ℕ 1 → 1 ≤ℕ s₀ + d → at 0 ₋ < x (keep d) ₋
      conclusion d d≤1 1≤r = subst₂ (λ a b → a ₋ < b ₋) eP AE.y-0 (S′.lemma-5-44 AE.sub-y AE.bt-y′ h′)
        where
        module AE = AtEnd ch u last (s₀ + d) d refl 1≤r (≤ℕ-trans d≤1 (s≤s z≤n)) 0 u≡k
        module S′ = Subs.InCycle AE.𝒞′

        h′ : AE.y AE.L A₁ AE.y (suc AE.L)
        h′ = subst₂ _A₁_ (sym AE.y-L) (sym (AE.y-extra 0 z≤n)) h

        eP : AE.y (suc AE.L) ≡ at 0
        eP = trans (AE.y-extra 0 z≤n) (trans (cong (λ z → at (suc z)) u≡k) at-wrap)

    -- Lemma 5.45 at the end: A₂'s at u and u + 1 = kc, the second to the base.
    end-5-45 : ∀ {s′ keep} (ch : F.Chain (suc s′) keep) u (last : s₀ + keep (suc s′) ≡ u) → suc u ≡ kc
             → at u A₂ at (suc u) → at (suc u) A₂ at (suc (suc u)) → ⊥
    end-5-45 {s′} {keep} ch u last su≡k h₁ h₂ = end-case ch conclusion
      where
      conclusion : ∀ d → d ≤ℕ 1 → 1 ≤ℕ s₀ + d → at 0 ₋ < x (keep d) ₋
      conclusion d d≤1 1≤r = subst₂ (λ a b → a ₋ < b ₋) eP AE.y-0 (S′.lemma-5-45 AE.L AE.sub-y AE.bt-y′ h₁′ h₂′)
        where
        module AE = AtEnd ch u last (s₀ + d) d refl 1≤r (≤ℕ-trans d≤1 (s≤s z≤n)) 1 su≡k
        module S′ = Subs.InCycle AE.𝒞′

        h₁′ : AE.y AE.L A₂ AE.y (suc AE.L)
        h₁′ = subst₂ _A₂_ (sym AE.y-L) (sym (AE.y-extra 0 z≤n)) h₁

        h₂′ : AE.y (suc AE.L) A₂ AE.y (suc (suc AE.L))
        h₂′ = subst₂ _A₂_ (sym (AE.y-extra 0 z≤n)) (sym (AE.y-extra 1 ≤ℕ-refl)) h₂

        eP : AE.y (suc (suc AE.L)) ≡ at 0
        eP = trans (AE.y-extra 1 ≤ℕ-refl) (trans (cong (λ z → at (suc z)) su≡k) at-wrap)
```

The loop body at a state `u`: the run of A's from `u` is a single A₂, by
Lemmas 5.44, 5.45 and 5.36; it reaches the base, which ends the loop with the
result, or a later block, which the extension step of Lemma 5.51 adds to the
chain.

```agda
    module Body {u : ℕ} (u≤k : u ≤ℕ kc) (st : State u) where
      open State st

      private
        ar : Σ ℕ λ v → u <ℕ v × v ≤ℕ suc kc × (∀ t → u ≤ℕ t → t <ℕ v → IsA t) × (v ≤ℕ kc → IsB v)
        ar = arun-end u u≤k uA

      v : ℕ
      v = proj₁ ar

      u<v : u <ℕ v
      u<v = proj₁ (proj₂ ar)

      v≤sk : v ≤ℕ suc kc
      v≤sk = proj₁ (proj₂ (proj₂ ar))

      runA : ∀ t → u ≤ℕ t → t <ℕ v → IsA t
      runA = proj₁ (proj₂ (proj₂ (proj₂ ar)))

      nextB : v ≤ℕ kc → IsB v
      nextB = proj₂ (proj₂ (proj₂ (proj₂ ar)))

      s₀<u : s₀ <ℕ u
      s₀<u = ≤ℕ-<-trans s₀≤b b<u

      contra : ∀ w → u ≤ℕ w → w ≤ℕ v → w ≤ℕ kc → at w ₋ < at s₀ ₋ → ⊥
      contra = run-contra u s₀<u v u<v v≤sk runA nextB

      -- The step at u is not an A₁ (Lemma 5.44).
      A₁-case : at u A₁ at (suc u) → ⊥
      A₁-case h = split (m≤n⇒m<n∨m≡n u≤k)
        where
        split : u <ℕ kc ⊎ u ≡ kc → ⊥
        split (inj₁ u<k) = contra (suc u) (n≤1+n u) u<v u<k (flat-5-44 chain u last u<k h)
        split (inj₂ u≡k) = end-5-44 chain u last u≡k h

      A₂u : IsA₂ u
      A₂u = from (A→A₁⊎A₂ uA)
        where
        from : at u A₁ at (suc u) ⊎ at u A₂ at (suc u) → IsA₂ u
        from (inj₁ h) = ⊥-elim (A₁-case h)
        from (inj₂ h) = h

      -- The step after u is not an A (Lemmas 5.36 and 5.45).
      two-A : suc u <ℕ v → ⊥
      two-A su<v = from (A→A₁⊎A₂ Asu)
        where
        Asu : IsA (suc u)
        Asu = runA (suc u) (n≤1+n u) su<v

        su≤k : suc u ≤ℕ kc
        su≤k = s≤s⁻¹ (<ℕ-≤-trans su<v v≤sk)

        2≤k : 2 ≤ℕ kc
        2≤k = ≤ℕ-trans (s≤s (≤ℕ-trans (s≤s z≤n) s₀<u)) su≤k

        from : at (suc u) A₁ at (suc (suc u)) ⊎ IsA₂ (suc u) → ⊥
        from (inj₁ h) = A₁∧A₂ h (three u (s≤s su≤k) 2≤k A₂u Asu)
        from (inj₂ h) = split (m≤n⇒m<n∨m≡n su≤k)
          where
          split : suc u <ℕ kc ⊎ suc u ≡ kc → ⊥
          split (inj₁ su<k) = contra (suc (suc u)) (≤ℕ-trans (n≤1+n u) (n≤1+n (suc u))) su<v su<k
                                     (flat-5-45 chain u last su<k A₂u h)
          split (inj₂ su≡k) = end-5-45 chain u last su≡k A₂u h

      single : v ≡ suc u
      single = from (m≤n⇒m<n∨m≡n u<v)
        where
        from : suc u <ℕ v ⊎ suc u ≡ v → v ≡ suc u
        from (inj₁ su<v) = ⊥-elim (two-A su<v)
        from (inj₂ e)    = sym e

      -- The chain's last step, a B from k′ to u.
      k′ : ℕ
      k′ = s₀ + keep s′

      su≡ : suc k′ ≡ u
      su≡ = trans (sym (+-suc s₀ (keep s′))) (trans (cong (s₀ +_) (sym direct)) last)

      Bk′ : IsB k′
      Bk′ = from (F.Chain.steps chain s′ (n<1+n s′))
        where
        from : (keep (suc s′) ≡ suc (keep s′) × x (keep s′) B x (keep (suc s′)))
             ⊎ (keep (suc s′) ≡ suc (suc (keep s′)) × F.Boundary keep s′) → IsB k′
        from (inj₁ (_ , h)) = subst (λ z → at k′ B at z) (trans (cong (s₀ +_) direct) (+-suc s₀ (keep s′))) h
        from (inj₂ (e , _)) = ⊥-elim (1+n≢n (trans (sym e) direct))

      -- The end: u = kc, and the run of A's is the single A₂ from kc to the base.
      final : u ≡ kc → Result 𝒞
      final u≡k = record
        { k′ = k′ ; k≡ = sym (trans su≡ u≡k) ; A₂k = subst IsA₂ u≡k A₂u ; Bk′ = Bk′ ; noB₂ = noB₂′ }
        where
        -- When the block is the first, at s₀ = at k′: the A₂ from kc to the base puts at 0 ₋₋ below at kc ₋₋,
        -- while a B₂ would put at kc ₋₋ below at s₀ ₋₋ ≤ at 0 ₋₋.
        last-block : s₀ ≡ k′ → ¬ (at k′ B₂ at (suc k′))
        last-block s₀≡k′ (_ , lt) = <-irrefl (<-≤-trans 0₋₋<k₋₋ k₋₋≤0₋₋)
          where
          0<k : at 0 < at kc
          0<k = subst (_< at kc) at-wrap (A→< Ak)

          0₋₋<k₋₋ : (at 0 ₋) ₋ < (at kc ₋) ₋
          0₋₋<k₋₋ = <-≤-trans (at-₋irr 𝒞 0 z≤n) (₋-mono (<→≤₋ 0<k))

          lt′ : at kc ₋ < at k′
          lt′ = subst (λ z → at z ₋ < at k′) (trans su≡ u≡k) lt

          k₋₋≤0₋₋ : (at kc ₋) ₋ ≤ (at 0 ₋) ₋
          k₋₋≤0₋₋ = ≤-trans (₋-mono (<→≤₋ lt′)) (≤-trans (≤-reflexive′ (cong (λ z → (at z ₋) ₋) (sym s₀≡k′))) s₀₋₋≤)

        noB₂′ : ∀ {k″} → k′ ≡ suc k″ → IsA k″ → ¬ (at k′ B₂ at (suc k′))
        noB₂′ {k″} e Ak″ = decide (bstart ≤ℕ? k″)
          where
          k″<u : k″ <ℕ u
          k″<u = subst (k″ <ℕ_) (trans (cong suc (sym e)) su≡) (n≤1+n (suc k″))

          decide : Dec (bstart ≤ℕ k″) → ¬ (at k′ B₂ at (suc k′))
          decide (yes b≤k″) = ⊥-elim (A∧B Ak″ (bB k″ b≤k″ k″<u))
          decide (no b≰k″)  = from b-ok
            where
            b≡k′ : bstart ≡ k′
            b≡k′ = ≤ℕ-antisym (s≤s⁻¹ (subst (bstart <ℕ_) (sym su≡) b<u)) (subst (_≤ℕ bstart) (sym e) (≰⇒> b≰k″))

            from : bstart ≡ s₀ ⊎ ¬ (at bstart B₂ at (suc bstart)) → ¬ (at k′ B₂ at (suc k′))
            from (inj₁ b≡s₀) = last-block (trans (sym b≡s₀) b≡k′)
            from (inj₂ h)    = subst (λ z → ¬ (at z B₂ at (suc z))) b≡k′ h

      -- A later block: the single A₂ at u reaches the block start u + 1 ≤ kc, and the block joins the chain.
      transition : u <ℕ kc → Σ ℕ λ u′ → u <ℕ u′ × u′ ≤ℕ kc × State u′
      transition u<k = go (run-end (suc u) u<k Bv)
        where
        Bv : IsB (suc u)
        Bv = subst IsB single (nextB (subst (_≤ℕ kc) (sym single) u<k))

        s₀<su : s₀ <ℕ suc u
        s₀<su = <ℕ-trans s₀<u (n<1+n u)

        start : IsStart (suc u)
        start = uA , Bv

        -- at (u + 1) B at s₀ fails: C relates a member only to its successor, and at kc A at 0.
        ¬vBq₀ : ¬ (at (suc u) B at s₀)
        ¬vBq₀ h = from (inorder u<k s₀≤k (inj₂ h))
          where
          from : s₀ ≡ suc (suc u) ⊎ (suc u ≡ kc × s₀ ≡ 0) → ⊥
          from (inj₁ e)        = <ℕ-irrefl e (<ℕ-trans s₀<su (n<1+n (suc u)))
          from (inj₂ (e , e₀)) = A∧B Ak (subst₂ _B_ (cong at e) (trans (cong at e₀) (sym at-wrap)) h)

        -- Lemma 5.46 and the choice of s₀: at s₀ ≤ κ(at (u + 1)), and at (u + 1) ₋ ≮ at s₀ ₋.
        q₀≤κv : at s₀ ≤ κ (at (suc u))
        q₀≤κv = decidable-stable (_ ≤? _) λ q₀≰ →
          start-contra (suc u) s₀<su u<k start (<→≤₋ (flat-5-46 chain u last u<k A₂u ¬vBq₀ q₀≰))

        ¬v₋<q₀₋ : ¬ (at (suc u) ₋ < at s₀ ₋)
        ¬v₋<q₀₋ lt = start-contra (suc u) s₀<su u<k start (≤-trans (₋≤ (at (suc u) ₋)) (<→≤₋ lt))

        c₀ : ℕ
        c₀ = suc (keep (suc s′))

        s₀+c₀ : s₀ + c₀ ≡ suc u
        s₀+c₀ = trans (+-suc s₀ (keep (suc s′))) (cong suc last)

        eqₗ : ∀ l → s₀ + (l + c₀) ≡ suc u + l
        eqₗ l = trans (sym (+-assoc s₀ l c₀))
                      (trans (cong (_+ c₀) (+-comm s₀ l)) (trans (+-assoc l s₀ c₀) (trans (cong (l +_) s₀+c₀) (+-comm l (suc u)))))

        go : (Σ ℕ λ d → 0 <ℕ d × suc u + d ≤ℕ kc × IsA (suc u + d) × (∀ i → i <ℕ d → IsB (suc u + i)))
           → Σ ℕ λ u′ → u <ℕ u′ × u′ ≤ℕ kc × State u′
        go (zero , () , _)
        go (suc m′ , _ , end≤ , Aend , Bs) = suc u + suc m′ , m≤m+n (suc u) (suc m′) , end≤ , new
          where
          block : suc m′ + c₀ ≤ℕ N
          block = m+n≤o⇒m≤o∸n (suc m′ + c₀) (subst (_≤ℕ kc) eq end≤)
            where
            eq : suc u + suc m′ ≡ (suc m′ + c₀) + s₀
            eq = sym (trans (+-assoc (suc m′) c₀ s₀)
                            (trans (cong (suc m′ +_) (trans (+-comm c₀ s₀) s₀+c₀)) (+-comm (suc m′) (suc u))))

          hA₂x : x (keep (suc s′)) A₂ x c₀
          hA₂x = subst₂ _A₂_ (sym (cong at last)) (sym (cong at s₀+c₀)) A₂u

          Bsx : ∀ l → l <ℕ suc m′ → x (l + c₀) B x (suc l + c₀)
          Bsx l l<d = subst₂ _B_ (sym (cong at (eqₗ l))) (sym (cong at (trans (+-suc s₀ (l + c₀)) (cong suc (eqₗ l))))) (Bs l l<d)

          q₀≤κx : x 0 ≤ κ (x c₀)
          q₀≤κx = subst₂ (λ a b → a ≤ κ b) (cong at (sym (+-identityʳ s₀))) (cong at (sym s₀+c₀)) q₀≤κv

          ¬x : ¬ (x c₀ ₋ < x 0 ₋)
          ¬x = subst₂ (λ a b → ¬ (a ₋ < b ₋)) (cong at (sym s₀+c₀)) (cong at (sym (+-identityʳ s₀))) ¬v₋<q₀₋

          module E = F.Extend chain direct (suc m′) (s≤s z≤n) block hA₂x Bsx q₀≤κx ¬x

          new : State (suc u + suc m′)
          new = record
            { s′     = m′ + suc s′
            ; keep   = E.keep′
            ; chain  = E.chain′
            ; direct = trans (after-+ keep s′ c₀ (suc m′)) (cong suc (sym (after-+ keep s′ c₀ m′)))
            ; last   = trans (cong (s₀ +_) (after-+ keep s′ c₀ (suc m′))) (eqₗ (suc m′))
            ; uA     = Aend
            ; bstart = suc u
            ; s₀≤b   = <⇒≤ s₀<su
            ; b<u    = m<m+n (suc u) (s≤s z≤n)
            ; bB     = λ t su≤t t<end → subst IsB (m+[n∸m]≡n su≤t)
                         (Bs (t ∸ suc u) (subst (t ∸ suc u <ℕ_) (m+n∸m≡n (suc u) (suc m′)) (∸-monoˡ-< t<end su≤t)))
            ; b-ok   = inj₂ λ h → E.noB₂ (subst₂ _B₂_ (cong at (sym s₀+c₀))
                                                     (cong at (sym (trans (+-suc s₀ c₀) (cong suc s₀+c₀)))) h) }

      result-or-next : Result 𝒞 ⊎ (Σ ℕ λ u′ → u <ℕ u′ × u′ ≤ℕ kc × State u′)
      result-or-next = split (m≤n⇒m<n∨m≡n u≤k)
        where
        split : u <ℕ kc ⊎ u ≡ kc → Result 𝒞 ⊎ (Σ ℕ λ u′ → u <ℕ u′ × u′ ≤ℕ kc × State u′)
        split (inj₁ u<k) = inj₂ (transition u<k)
        split (inj₂ u≡k) = inj₁ (final u≡k)

    -- The loop, by recursion on a bound for kc ∸ u.
    not<0 : ∀ {a} → ¬ a <ℕ 0
    not<0 ()

    loop : ∀ fuel {u} → u ≤ℕ kc → kc ∸ u ≤ℕ fuel → State u → Result 𝒞
    loop fuel {u} u≤k b st = from fuel b (Body.result-or-next u≤k st)
      where
      from : ∀ f → kc ∸ u ≤ℕ f → Result 𝒞 ⊎ (Σ ℕ λ u′ → u <ℕ u′ × u′ ≤ℕ kc × State u′) → Result 𝒞
      from _       _  (inj₁ r)                        = r
      from zero    b′ (inj₂ (u′ , u<u′ , u′≤k , _))   = ⊥-elim (not<0 (<ℕ-≤-trans (∸-monoʳ-< u<u′ u′≤k) b′))
      from (suc f) b′ (inj₂ (u′ , u<u′ , u′≤k , st′)) = loop f u′≤k (s≤s⁻¹ (<ℕ-≤-trans (∸-monoʳ-< u<u′ u′≤k) b′)) st′

    -- The initial state: the run of B's at s₀, a chain with the identity reindexing.
    initial : Σ ℕ λ u → u ≤ℕ kc × State u
    initial = go (run-end s₀ s₀≤k (start-B s₀ s₀-start))
      where
      go : (Σ ℕ λ d → 0 <ℕ d × s₀ + d ≤ℕ kc × IsA (s₀ + d) × (∀ i → i <ℕ d → IsB (s₀ + i)))
         → Σ ℕ λ u → u ≤ℕ kc × State u
      go (zero , () , _)
      go (suc m₀ , _ , d≤ , Aend , Bs) = s₀ + suc m₀ , d≤ , record
        { s′     = m₀
        ; keep   = λ t → t
        ; chain  = F.chain-of-Bs (suc m₀) d≤N (λ i i<d → xB (Bs i i<d))
        ; direct = refl
        ; last   = refl
        ; uA     = Aend
        ; bstart = s₀
        ; s₀≤b   = ≤ℕ-refl
        ; b<u    = m<m+n s₀ (s≤s z≤n)
        ; bB     = λ t s₀≤t t<end → subst IsB (m+[n∸m]≡n s₀≤t)
                     (Bs (t ∸ s₀) (subst (t ∸ s₀ <ℕ_) (m+n∸m≡n s₀ (suc m₀)) (∸-monoˡ-< t<end s₀≤t)))
        ; b-ok   = inj₁ refl }
        where
        d≤N : suc m₀ ≤ℕ N
        d≤N = m+n≤o⇒m≤o∸n (suc m₀) (subst (_≤ℕ kc) (+-comm s₀ (suc m₀)) d≤)

    -- The result of the main argument.
    result : Result 𝒞
    result = loop kc (proj₁ (proj₂ initial)) (m∸n≤m kc (proj₁ initial)) (proj₂ (proj₂ initial))
```

```agda
  -- The main argument as a function of the cycle.
  main : (𝒞 : MinimalCycle) → Steps.IsB 𝒞 0 → Steps.IsA 𝒞 (Steps.kc 𝒞) → Result 𝒞
  main 𝒞 B0 Ak = Main.result 𝒞 B0 Ak
```

#### The cyclic reading of the steps, and the A's of any cycle

A cycle's members read at any natural number, modulo the length
(`atᶜ`{.AgdaFunction} of [Lattices.Nation.Cycle][]), give its steps at every
position, and the steps of a rotation are the cyclic steps shifted
(`Rot`{.AgdaModule}).  The main argument, applied to the rotation of a cycle
to the first B after a given A (`ToBase`{.AgdaModule}), shows that the A is a
single A₂ between two B's (`factA0`{.AgdaFunction} for the first step,
`factA`{.AgdaFunction} for every position).

```agda
  module Cyclic (𝒞 : MinimalCycle) where
    open Steps 𝒞 using ( kc )
    open MinimalCycleProperties 𝒞 using ( at ; at-wrap ; at-irr )
    open Rotation 𝒞 using ( atᶜ ; atᶜ-≤ ; at-rotate-all ; atᶜ-cong ; %-suc ; %-≤ )

    -- The relation R between the members at positions a and a + 1, read cyclically.
    _ᶜ_ : (Fin (suc n) → Fin (suc n) → Type) → ℕ → Type
    R ᶜ a = R (atᶜ a) (atᶜ (suc a))

    ᶜ-cong : ∀ R a b → a % suc kc ≡ b % suc kc → R ᶜ a → R ᶜ b
    ᶜ-cong R a b e h = subst₂ R (atᶜ-cong a b e) (atᶜ-cong (suc a) (suc b) (%-suc a b e)) h

    -- Every member is join irreducible.
    irrᶜ : ∀ a → HasOneLowerCover (atᶜ a)
    irrᶜ a = at-irr (a % suc kc) (%-≤ a)

    -- At a position up to the length, the cyclic step is the cycle's own.
    atᶜ-suc : ∀ {t} → t ≤ℕ kc → atᶜ (suc t) ≡ at (suc t)
    atᶜ-suc {t} t≤k = from (m≤n⇒m<n∨m≡n t≤k)
      where
      from : t <ℕ kc ⊎ t ≡ kc → atᶜ (suc t) ≡ at (suc t)
      from (inj₁ lt)   = atᶜ-≤ lt
      from (inj₂ refl) = trans (cong at (n%n≡0 (suc kc))) (sym at-wrap)

    ᶜ→ : ∀ R {t} → t ≤ℕ kc → R ᶜ t → R (at t) (at (suc t))
    ᶜ→ R t≤k h = subst₂ R (atᶜ-≤ t≤k) (atᶜ-suc t≤k) h

    →ᶜ : ∀ R {t} → t ≤ℕ kc → R (at t) (at (suc t)) → R ᶜ t
    →ᶜ R t≤k h = subst₂ R (sym (atᶜ-≤ t≤k)) (sym (atᶜ-suc t≤k)) h

    -- In the rotation by r, the step at i ≤ kc is the cyclic step at r + i.
    module Rot (r : ℕ) where
      𝒞′ : MinimalCycle
      𝒞′ = rotate 𝒞 r

      module 𝒫′ = MinimalCycleProperties 𝒞′

      rd : ∀ i → i ≤ℕ kc → 𝒫′.at i ≡ atᶜ (r + i)
      rd i i≤k = at-rotate-all r i (≤ℕ-trans i≤k (n≤1+n kc))

      rd-suc : ∀ i → i ≤ℕ kc → 𝒫′.at (suc i) ≡ atᶜ (suc (r + i))
      rd-suc i i≤k = trans (at-rotate-all r (suc i) (s≤s i≤k)) (cong atᶜ (+-suc r i))

      rot→ᶜ : ∀ R i → i ≤ℕ kc → R (𝒫′.at i) (𝒫′.at (suc i)) → R ᶜ (r + i)
      rot→ᶜ R i i≤k h = subst₂ R (rd i i≤k) (rd-suc i i≤k) h

      ᶜ→rot : ∀ R i → i ≤ℕ kc → R ᶜ (r + i) → R (𝒫′.at i) (𝒫′.at (suc i))
      ᶜ→rot R i i≤k h = subst₂ R (sym (rd i i≤k)) (sym (rd-suc i i≤k)) h

  -- The first step of a cycle, if an A, is an A₂ between two B's: the main argument for the rotation of the
  -- cycle to the first B after it, in which the A's before that B are the last steps.
  factA0 : (𝒞₁ : MinimalCycle) → Steps.IsA 𝒞₁ 0
         → Steps.IsA₂ 𝒞₁ 0 × Steps.IsB 𝒞₁ 1 × Steps.IsB 𝒞₁ (Steps.kc 𝒞₁)
  factA0 𝒞₁ A0 = cases T.s′ refl
    where
    module T = ToBase 𝒞₁ A0
    module R = Result (main T.𝒞₂ T.B0 T.Ak)
    open Steps 𝒞₁ using ( kc ; IsA ; IsB ; IsA₂ )
    module 𝒫₁ = MinimalCycleProperties 𝒞₁
    module 𝒫₂ = MinimalCycleProperties T.𝒞₂
    open Rotation 𝒞₁ using ( at-rotate-≤′ )

    cases : ∀ t → T.s′ ≡ t → IsA₂ 0 × IsB 1 × IsB kc
    cases (suc s″) e = ⊥-elim (A∧B (T.TwoBefore.Ak′ s″ e) (subst (λ z → 𝒫₂.at z B 𝒫₂.at (suc z)) k′≡ R.Bk′))
      where
      k′≡ : R.k′ ≡ T.TwoBefore.kc′ s″ e
      k′≡ = suc-injective (trans (sym R.k≡) (T.TwoBefore.kc≡ s″ e))
    cases zero e = A₂0 , B1 , Bk
      where
      s≡1 : T.s ≡ 1
      s≡1 = trans T.s≡ (cong suc e)

      A₂0 : IsA₂ 0
      A₂0 = subst₂ _A₂_ (trans T.at₂-k (cong 𝒫₁.at e)) (trans T.at₂-sk (cong 𝒫₁.at s≡1)) R.A₂k

      B1 : IsB 1
      B1 = subst IsB s≡1 T.Bs

      eq : T.s + R.k′ ≡ kc
      eq = trans (cong (_+ R.k′) s≡1) (sym R.k≡)

      k′≤k : R.k′ ≤ℕ kc
      k′≤k = subst (R.k′ ≤ℕ_) (sym R.k≡) (n≤1+n R.k′)

      at₂k′ : 𝒫₂.at R.k′ ≡ 𝒫₁.at kc
      at₂k′ = trans (at-rotate-≤′ T.s k′≤k (≤ℕ-trans (≤ℕ-reflexive eq) (n≤1+n kc))) (cong 𝒫₁.at eq)

      at₂sk′ : 𝒫₂.at (suc R.k′) ≡ 𝒫₁.at (suc kc)
      at₂sk′ = trans (cong 𝒫₂.at (sym R.k≡)) (trans T.at₂-k (trans (cong 𝒫₁.at e) (sym 𝒫₁.at-wrap)))

      Bk : IsB kc
      Bk = subst₂ _B_ at₂k′ at₂sk′ R.Bk′

  -- Every A of a cycle is a single A₂ between two B's, at every position read cyclically.
  module FactA (𝒞 : MinimalCycle) where
    open Steps 𝒞 using ( kc )
    open Cyclic 𝒞
    open Rotation 𝒞 using ( %-+ ; %-idem )

    factA : ∀ j → _A_ ᶜ j → (_A₂_ ᶜ j) × (_B_ ᶜ (suc j)) × (_B_ ᶜ (j + kc))
    factA j h = ᶜ-cong _A₂_ (r + 0) j e₀ (Ro.rot→ᶜ _A₂_ 0 z≤n (proj₁ fa))
              , ᶜ-cong _B_ (r + 1) (suc j) e₁ (Ro.rot→ᶜ _B_ 1 1≤k (proj₁ (proj₂ fa)))
              , ᶜ-cong _B_ (r + kc) (j + kc) e₂ (Ro.rot→ᶜ _B_ kc ≤ℕ-refl (proj₂ (proj₂ fa)))
      where
      r : ℕ
      r = j % suc kc

      module Ro = Rot r

      e₀ : (r + 0) % suc kc ≡ j % suc kc
      e₀ = trans (cong (_% suc kc) (+-identityʳ r)) (%-idem j)

      e₁ : (r + 1) % suc kc ≡ suc j % suc kc
      e₁ = trans (%-+ r j 1 (%-idem j)) (cong (_% suc kc) (+-comm j 1))

      e₂ : (r + kc) % suc kc ≡ (j + kc) % suc kc
      e₂ = %-+ r j kc (%-idem j)

      A0 : Steps.IsA Ro.𝒞′ 0
      A0 = Ro.ᶜ→rot _A_ 0 z≤n (ᶜ-cong _A_ j (r + 0) (sym e₀) h)

      fa : Steps.IsA₂ Ro.𝒞′ 0 × Steps.IsB Ro.𝒞′ 1 × Steps.IsB Ro.𝒞′ kc
      fa = factA0 Ro.𝒞′ A0

      1≤k : 1 ≤ℕ kc
      1≤k = from (m≤n⇒m<n∨m≡n (z≤n {kc}))
        where
        from : 0 <ℕ kc ⊎ 0 ≡ kc → 1 ≤ℕ kc
        from (inj₁ lt) = lt
        from (inj₂ e)  = ⊥-elim (A∧B A0 (subst (Steps.IsB Ro.𝒞′) (sym e) (proj₂ (proj₂ fa))))
```

#### The B's of any cycle, and Lemma 5.54

The dual cycle, through κ, turns the B's into A's (Lemma 2.63), so the fact
about A's, for the dual lattice, says that the first step of a cycle, if a B,
lies between two A's.  That fact is the parameter `factB0` of the module
`Final`{.AgdaModule}, supplied by [Lattices.Nation.Lemma554][], where
the dual lattice is in reach; from it every B is a single B
between two A's at every position (`factB`{.AgdaFunction}).  With the main
argument's last conclusion every B is then a B₁ (`factB₁`{.AgdaFunction}): a
B₂ would be the last B of the rotation that starts two steps after it.  A
minimal C-cycle read from a B therefore alternates B₁ and A₂ and has an even
number of steps: with two it puts its first member both below and not below
its second, and with more it is a cycle Lemma 5.53 excludes
(`lemma-5-54`{.AgdaFunction}).

```agda
  module Final (factB0 : (𝒞₁ : MinimalCycle) → Steps.IsB 𝒞₁ 0 → Steps.IsA 𝒞₁ 1 × Steps.IsA 𝒞₁ (Steps.kc 𝒞₁)) where

    -- Every B of a cycle is a single B between two A's, at every position read cyclically.
    module FactB (𝒞 : MinimalCycle) where
      open Steps 𝒞 using ( kc )
      open Cyclic 𝒞
      open Rotation 𝒞 using ( %-+ ; %-idem )

      factB : ∀ j → _B_ ᶜ j → (_A_ ᶜ (suc j)) × (_A_ ᶜ (j + kc))
      factB j h = ᶜ-cong _A_ (r + 1) (suc j) e₁ (Ro.rot→ᶜ _A_ 1 1≤k (proj₁ fb))
                , ᶜ-cong _A_ (r + kc) (j + kc) e₂ (Ro.rot→ᶜ _A_ kc ≤ℕ-refl (proj₂ fb))
        where
        r : ℕ
        r = j % suc kc

        module Ro = Rot r

        e₀ : (r + 0) % suc kc ≡ j % suc kc
        e₀ = trans (cong (_% suc kc) (+-identityʳ r)) (%-idem j)

        e₁ : (r + 1) % suc kc ≡ suc j % suc kc
        e₁ = trans (%-+ r j 1 (%-idem j)) (cong (_% suc kc) (+-comm j 1))

        e₂ : (r + kc) % suc kc ≡ (j + kc) % suc kc
        e₂ = %-+ r j kc (%-idem j)

        B0 : Steps.IsB Ro.𝒞′ 0
        B0 = Ro.ᶜ→rot _B_ 0 z≤n (ᶜ-cong _B_ j (r + 0) (sym e₀) h)

        fb : Steps.IsA Ro.𝒞′ 1 × Steps.IsA Ro.𝒞′ kc
        fb = factB0 Ro.𝒞′ B0

        1≤k : 1 ≤ℕ kc
        1≤k = from (m≤n⇒m<n∨m≡n (z≤n {kc}))
          where
          from : 0 <ℕ kc ⊎ 0 ≡ kc → 1 ≤ℕ kc
          from (inj₁ lt) = lt
          from (inj₂ e)  = ⊥-elim (A∧B (subst (Steps.IsA Ro.𝒞′) (sym e) (proj₂ fb)) B0)

    -- In a cycle of at least three steps, every B is a B₁: a B₂ at j would be the last B of the rotation to j + 2,
    -- preceded there by the A at j - 1, which the main argument excludes.
    module FactB₁ (𝒞 : MinimalCycle) (2≤k : 2 ≤ℕ MinimalCycle.k 𝒞) where
      open Steps 𝒞 using ( kc )
      open Cyclic 𝒞
      open FactA 𝒞 using ( factA )
      open FactB 𝒞 using ( factB )
      open Rotation 𝒞 using ( %-+ ; %-idem ; %-wrap )

      factB₁ : ∀ j → _B_ ᶜ j → _B₁_ ᶜ j
      factB₁ j h = from (B→B₁⊎B₂ h)
        where
        Asj : _A_ ᶜ (suc j)
        Asj = proj₁ (factB j h)

        Bssj : _B_ ᶜ (suc (suc j))
        Bssj = proj₁ (proj₂ (factA (suc j) Asj))

        Ajk : _A_ ᶜ (j + kc)
        Ajk = proj₂ (factB j h)

        r : ℕ
        r = suc (suc j) % suc kc

        module Ro = Rot r

        rr : r % suc kc ≡ suc (suc j) % suc kc
        rr = %-idem (suc (suc j))

        B0 : Steps.IsB Ro.𝒞′ 0
        B0 = Ro.ᶜ→rot _B_ 0 z≤n (ᶜ-cong _B_ (suc (suc j)) (r + 0) (sym (trans (cong (_% suc kc) (+-identityʳ r)) rr)) Bssj)

        Ak : Steps.IsA Ro.𝒞′ kc
        Ak = Ro.ᶜ→rot _A_ kc ≤ℕ-refl (ᶜ-cong _A_ (suc j) (r + kc) ek Asj)
          where
          ek : suc j % suc kc ≡ (r + kc) % suc kc
          ek = sym (trans (%-+ r (suc (suc j)) kc rr)
                          (trans (cong (_% suc kc) (cong suc (sym (+-suc j kc)))) (%-wrap (suc j))))

        module R = Result (main Ro.𝒞′ B0 Ak)

        k′≤k : R.k′ ≤ℕ kc
        k′≤k = subst (R.k′ ≤ℕ_) (sym R.k≡) (n≤1+n R.k′)

        not21 : ¬ 2 ≤ℕ 1
        not21 (s≤s ())

        contra : _B₂_ ᶜ j → ⊥
        contra b₂ = go R.k′ refl
          where
          e′ : j % suc kc ≡ (r + R.k′) % suc kc
          e′ = sym (trans (%-+ r (suc (suc j)) R.k′ rr) (trans (cong (_% suc kc) eq′) (%-wrap j)))
            where
            eq′ : suc (suc j) + R.k′ ≡ j + suc kc
            eq′ = sym (trans (+-suc j kc) (cong suc (trans (cong (j +_) R.k≡) (+-suc j R.k′))))

          B₂k′ : MinimalCycleProperties.at Ro.𝒞′ R.k′ B₂ MinimalCycleProperties.at Ro.𝒞′ (suc R.k′)
          B₂k′ = Ro.ᶜ→rot _B₂_ R.k′ k′≤k (ᶜ-cong _B₂_ j (r + R.k′) e′ b₂)

          go : ∀ t → R.k′ ≡ t → ⊥
          go zero     e = not21 (subst (2 ≤ℕ_) (trans R.k≡ (cong suc e)) 2≤k)
          go (suc k″) e = R.noB₂ e Ak″ B₂k′
            where
            kk : kc ≡ suc (suc k″)
            kk = trans R.k≡ (cong suc e)

            k″≤k : k″ ≤ℕ kc
            k″≤k = subst (k″ ≤ℕ_) (sym kk) (≤ℕ-trans (n≤1+n k″) (n≤1+n (suc k″)))

            e″ : (j + kc) % suc kc ≡ (r + k″) % suc kc
            e″ = sym (trans (%-+ r (suc (suc j)) k″ rr) (cong (_% suc kc) eq″))
              where
              eq″ : suc (suc j) + k″ ≡ j + kc
              eq″ = sym (trans (cong (j +_) kk) (trans (+-suc j (suc k″)) (cong suc (+-suc j k″))))

            Ak″ : Steps.IsA Ro.𝒞′ k″
            Ak″ = Ro.ᶜ→rot _A_ k″ k″≤k (ᶜ-cong _A_ (j + kc) (r + k″) e″ Ajk)

        from : _B₁_ ᶜ j ⊎ _B₂_ ᶜ j → _B₁_ ᶜ j
        from (inj₁ b₁) = b₁
        from (inj₂ b₂) = ⊥-elim (contra b₂)

    -- Twice a number, as Lemma 5.53 counts the steps of an alternating cycle.
    two : ℕ → ℕ
    two j = j + j

    two-suc : ∀ j → two (suc j) ≡ suc (suc (two j))
    two-suc j = cong suc (+-suc j j)

    -- Every number is even or odd.
    parity : ∀ k → Σ ℕ λ h → k ≡ two h ⊎ k ≡ suc (two h)
    parity zero    = 0 , inj₁ refl
    parity (suc k) = from (parity k)
      where
      from : (Σ ℕ λ h → k ≡ two h ⊎ k ≡ suc (two h)) → Σ ℕ λ h → suc k ≡ two h ⊎ suc k ≡ suc (two h)
      from (h , inj₁ e) = h , inj₂ (cong suc e)
      from (h , inj₂ e) = suc h , inj₁ (trans (cong suc e) (sym (two-suc h)))

    -- No minimal C-cycle: read from a B, it alternates B₁ and A₂.
    no-minimal : MinimalCycle → ⊥
    no-minimal 𝒞 = final (parity kc)
      where
      open Steps 𝒞 using ( kc ; some-B )
      module C₀ = Cyclic 𝒞

      b : ℕ
      b = proj₁ some-B

      module Ro = C₀.Rot b

      𝒟 : MinimalCycle
      𝒟 = Ro.𝒞′

      module C = Cyclic 𝒟
      open FactA 𝒟 using ( factA )
      open FactB 𝒟 using ( factB )

      at𝒟 : ℕ → Fin (suc n)
      at𝒟 = MinimalCycleProperties.at 𝒟

      B0ᶜ : _B_ C.ᶜ 0
      B0ᶜ = C.→ᶜ _B_ z≤n (Ro.ᶜ→rot _B_ 0 z≤n (C₀.ᶜ-cong _B_ b (b + 0) (cong (_% suc kc) (sym (+-identityʳ b)))
                                                  (C₀.→ᶜ _B_ (proj₁ (proj₂ some-B)) (proj₂ (proj₂ some-B)))))

      -- The steps alternate from the base: B's at even positions, A's at odd ones.
      alt : ∀ j → (_B_ C.ᶜ two j) × (_A_ C.ᶜ suc (two j))
      alt zero    = B0ᶜ , proj₁ (factB 0 B0ᶜ)
      alt (suc j) = Bss , proj₁ (factB (two (suc j)) Bss)
        where
        Bss : _B_ C.ᶜ two (suc j)
        Bss = subst (λ t → _B_ C.ᶜ t) (sym (two-suc j)) (proj₁ (proj₂ (factA (suc (two j)) (proj₂ (alt j)))))

      final : (Σ ℕ λ h → kc ≡ two h ⊎ kc ≡ suc (two h)) → ⊥
      final (h , inj₁ e)       = A∧B (subst (λ t → _A_ C.ᶜ t) e (proj₂ (factB 0 B0ᶜ))) (proj₁ (alt h))
      final (zero , inj₂ e)    = B→≰ B01 (proj₁ (A→< A10))
        where
        B01 : at𝒟 0 B at𝒟 1
        B01 = C.ᶜ→ _B_ z≤n B0ᶜ

        A12 : at𝒟 1 A at𝒟 2
        A12 = C.ᶜ→ _A_ (subst (1 ≤ℕ_) (sym e) ≤ℕ-refl) (proj₁ (factB 0 B0ᶜ))

        A10 : at𝒟 1 A at𝒟 0
        A10 = subst (at𝒟 1 A_) (trans (cong (λ t → at𝒟 (suc t)) (sym e)) (MinimalCycleProperties.at-wrap 𝒟)) A12
      final (suc n″ , inj₂ e)  = AlternatingModule.Alternating.Lemma553.lemma-5-53 laws sd w 𝒟 (suc n″) e Bs As
        where
        2≤k : 2 ≤ℕ kc
        2≤k = subst (2 ≤ℕ_) (sym e) (s≤s (subst (1 ≤ℕ_) (sym (two-suc n″)) (s≤s z≤n)))

        module F₁ = FactB₁ 𝒟 2≤k

        Bs : AlternatingModule.Alternating.Lemma553.Bs-type laws sd w 𝒟
        Bs j 2j≤k = C.ᶜ→ _B₁_ 2j≤k (F₁.factB₁ (two j) (proj₁ (alt j)))

        As : AlternatingModule.Alternating.Lemma553.As-type laws sd w 𝒟
        As j s2j≤k = C.ᶜ→ _A₂_ s2j≤k (proj₁ (factA (suc (two j)) (proj₂ (alt j))))

    -- Lemma 5.54, given the fact about B's.
    lemma-5-54 : ∀ {k} → ¬ Cycle k
    lemma-5-54 c = no-minimal (minimize c)
```
