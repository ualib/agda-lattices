---
layout: default
file: "src/Lattices/Nation/BType.lagda.md"
title: "Lattices.Nation.BType module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Consecutive A's and B's in a minimal C-cycle, and B-type sequences

This is the [Lattices.Nation.BType][] module of the [agda-lattices][] library.

Nation's argument that an S-lattice contains no C-cycle (Lemma 5.54 of
[Freese, Ježek, and Nation (1995)][]) studies a minimal C-cycle through its
subsequences, in the sense of [Lattices.Nation.Cycle][]: families of members at
increasing positions, not necessarily consecutive.  This module begins the
argument with the lemmas of pp. 111 to 114 and the tools the later lemmas
share.  It supplies the following, for a table lattice with both
semidistributive laws and (W), through [Lattices.Nation.Kappa][]:

+  **Prefix joins** (`⋁<`{.AgdaFunction}): `⋁< x j` is the join of `x 0`
   to `x (j - 1)`, the book's `⋁ᵢ₍ⱼ xᵢ`, with its bounds; and two searches,
   for the least index with a decidable property (`least-index`{.AgdaFunction})
   and for a minimal element with a decidable property below a given one
   (`minimal-with`{.AgdaFunction}), each by a bounded search with no classical
   principle; (W) over a prefix join (`W-⋁<`{.AgdaFunction}); a join irreducible
   element that is a join of a list is one of the joinands
   (`irr-⋁<`{.AgdaFunction}); and the lower cover of an element `a₀` within an
   interval above `a` (`LowerCoverAbove`{.AgdaModule}), the join of the
   elements of the interval strictly below `a₀`.
+  **Lemma 5.36** (`lemma-5-36`{.AgdaFunction}): if `p₀ A₂ p₁ A p₂` in a
   minimal C-cycle, then `p₂ = p₁₋` and `p₁ A₂ p₂`.
+  **Lemma 5.37** (`lemma-5-37`{.AgdaFunction}): if `q₀ B q₁ B q₂` in a minimal
   C-cycle, then `q₁ B₁ q₂`.
+  **B-type sequences** (`BType`{.AgdaRecord}): a family `q 0, …, q k` of join
   irreducible elements with (B1) `qᵢ₋₁₋ ≰ qᵢ`, (B2) `qᵢ ≤ κ(qⱼ)` for `i < j`,
   (B3) `qᵢ₋ ≤ κ(qᵢ₋₁)`, and (B4) `qⱼ₋ ≰ κ(qᵢ)` for `i + 2 ≤ j` (p. 113); and
   Lemma 5.41 (`lemma-5-41`{.AgdaFunction}): a subsequence of a minimal
   C-cycle with `qᵢ B qᵢ₊₁` throughout is a B-type sequence.  (B2) and (B4)
   are proved by induction on the distance of the indices, through the chain
   `κ(qᵢ) < κ(qᵢ₊₁)` that Lemma 2.63 gives.
+  **Index tools** for the inductive applications of the later lemmas: a
   B-type sequence shifted by `m` indices (`BType-shift`{.AgdaFunction}) or
   read through a family that agrees with it up to some index
   (`BType-cong`{.AgdaFunction}) is a B-type sequence; and the reindexing
   `keep-then j m` (the identity up to `j`, then `m`), which reads
   `q₀, …, q_j, p` out of `q₀, …, q_k, p` as the family `x ∘ keep-then j (k + 1)`
   and is strictly increasing on the indices up to `j + 1`
   (`keep-then-mono`{.AgdaFunction}).

Nation's paper states Lemma 5.41 as its Lemma 2.1, with the same proof.  The
lemmas take the cycle as a parameter and a subsequence of it as an argument;
`x i` is the member at index `i`, so that the book's `q₀, …, q_k, p` is a
subsequence read at the indices `0` to `k + 1`, with `p` at `k + 1`.

The module checks in 0.8 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.BType where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Properties                    using ( any? ; _≟_ )
open import Data.List.Base                         using ( filter ; allFin )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-allFin )
import Data.List.Relation.Unary.All as All
open import Data.Bool.Base                         using ( if_then_else_ ; true ; false )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; _≤ᵇ_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( <⇒≤ ; n<1+n ; n≤1+n ; m≤n⇒m<n∨m≡n ; +-suc ; +-identityʳ
                                                         ; ≤ᵇ-reflects-≤ ; +-monoˡ-< ; +-monoˡ-≤ ; +-monoʳ-< ; +-monoʳ-≤
                                                         ; ≮⇒≥ ; ≰⇒> ; m∸n+n≡m ; m+n∸n≡m ; m≤n+m ; n∸n≡0 ; ∸-monoˡ-< ; ∸-monoˡ-≤ )
                                                   renaming ( ≤-refl to ≤ℕ-refl ; ≤-reflexive to ≤ℕ-reflexive ; ≤-trans to ≤ℕ-trans
                                                            ; <-trans to <ℕ-trans ; <-≤-trans to <ℕ-≤-trans ; ≤-<-trans to ≤ℕ-<-trans
                                                            ; <-irrefl to <ℕ-irrefl ; _<?_ to _<ℕ?_ ; _≤?_ to _≤ℕ?_ )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ ; ofʸ ; ofⁿ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; _×-dec_ )

-- Imports from this library ----------------------------------------------------
open import Lattices.Nation.Cycle      using ( module Cycles )
open import Lattices.Nation.Kappa      using ( module Kappa ; module KappaDuality )
open import Lattices.Semidistributive  using ( IsSemidistributive ; SatisfiesW )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

#### Prefix joins and two searches

```agda
module BType {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
             (laws : LatticeTableLaws _∧_ _∨_)
             (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
             (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open KappaDuality laws sd using ( B→Aᵈ )
  open Cycles laws sd w

  -- (W), with the table lattice's order.
  W : ∀ s₁ s₂ t₁ t₂ → s₁ ∧ s₂ ≤ t₁ ∨ t₂
    → (s₁ ≤ t₁ ∨ t₂ ⊎ s₂ ≤ t₁ ∨ t₂) ⊎ (s₁ ∧ s₂ ≤ t₁ ⊎ s₁ ∧ s₂ ≤ t₂)
  W = w

  -- Lemma 2.63 read on the order: a B b gives κ a < κ b.
  B→κ< : ∀ {a b} → a B b → κ a < κ b
  B→κ< aBb = <ᵈ→ (proj₁ (proj₂ (proj₂ (B→Aᵈ aBb))))

  -- The join of x 0, …, x (j - 1).
  ⋁< : (ℕ → Fin (suc n)) → ℕ → Fin (suc n)
  ⋁< x zero     = ⊥ᴸ
  ⋁< x (suc j)  = ⋁< x j ∨ x j

  ⋁<-upper : ∀ x {i j} → i <ℕ j → x i ≤ ⋁< x j
  ⋁<-upper x {i} {suc j} i<sj = from (m≤n⇒m<n∨m≡n (s≤s⁻¹ i<sj))
    where
    from : i <ℕ j ⊎ i ≡ j → x i ≤ ⋁< x (suc j)
    from (inj₁ i<j)   = ≤∨ˡ (⋁<-upper x i<j)
    from (inj₂ refl)  = ∨-upperʳ

  ⋁<-least : ∀ x {j z} → (∀ i → i <ℕ j → x i ≤ z) → ⋁< x j ≤ z
  ⋁<-least x {zero}   _  = ⊥ᴸ-least _
  ⋁<-least x {suc j}  f  = ∨-least (⋁<-least x λ i i<j → f i (<ℕ-trans i<j (n<1+n j))) (f j (n<1+n j))

  ⋁<-prefix : ∀ x {j j′} → j ≤ℕ j′ → ⋁< x j ≤ ⋁< x j′
  ⋁<-prefix x j≤j′ = ⋁<-least x λ i i<j → ⋁<-upper x (<ℕ-≤-trans i<j j≤j′)

  -- A prefix join not below z has a member not below z.
  ⋁<-escape : ∀ y m {z} → ¬ ⋁< y m ≤ z → Σ ℕ λ i → i <ℕ m × ¬ y i ≤ z
  ⋁<-escape y zero     {z} h = ⊥-elim (h (⊥ᴸ-least z))
  ⋁<-escape y (suc m)  {z} h = decide (y m ≤? z)
    where
    decide : Dec (y m ≤ z) → Σ ℕ λ i → i <ℕ suc m × ¬ y i ≤ z
    decide (no ym≰z)   = m , n<1+n m , ym≰z
    decide (yes ym≤z)  = from (⋁<-escape y m λ ⋁≤z → h (∨-least ⋁≤z ym≤z))
      where
      from : Σ ℕ (λ i → i <ℕ m × ¬ y i ≤ z) → Σ ℕ λ i → i <ℕ suc m × ¬ y i ≤ z
      from (i , i<m , yi≰z) = i , <ℕ-trans i<m (n<1+n m) , yi≰z

  -- A prefix join lies below z when the members before m do, and the rest, read from m, do.
  ⋁<-around : ∀ x {z} m k → (∀ i → i <ℕ m → x i ≤ z) → (∀ i → i <ℕ k ∸ m → x (i + m) ≤ z) → ⋁< x k ≤ z
  ⋁<-around x {z} m k low high = ⋁<-least x λ i i<k → pick i i<k (i <ℕ? m)
    where
    pick : ∀ i → i <ℕ k → Dec (i <ℕ m) → x i ≤ z
    pick i i<k (yes i<m) = low i i<m
    pick i i<k (no i≮m)  = subst (λ v → x v ≤ z) (m∸n+n≡m (≮⇒≥ i≮m)) (high (i ∸ m) (∸-monoˡ-< i<k (≮⇒≥ i≮m)))

  -- Prefix joins of families that agree below the bound agree.
  ⋁<-cong : ∀ {y y′} m → (∀ i → i <ℕ m → y i ≡ y′ i) → ⋁< y m ≡ ⋁< y′ m
  ⋁<-cong zero     _ = refl
  ⋁<-cong (suc m)  f = cong₂ _∨_ (⋁<-cong m λ i i<m → f i (<ℕ-trans i<m (n<1+n m))) (f m (n<1+n m))

  -- The reindexing that keeps the indices up to j and sends every later index to m.
  keep-then : ℕ → ℕ → ℕ → ℕ
  keep-then j m i = if i ≤ᵇ j then i else m

  keep-then-≤ : ∀ {j m i} → i ≤ℕ j → keep-then j m i ≡ i
  keep-then-≤ {j} {m} {i} i≤j with i ≤ᵇ j | ≤ᵇ-reflects-≤ i j
  ... | true   | _        = refl
  ... | false  | ofⁿ i≰j  = ⊥-elim (i≰j i≤j)

  keep-then-> : ∀ {j m i} → j <ℕ i → keep-then j m i ≡ m
  keep-then-> {j} {m} {i} j<i with i ≤ᵇ j | ≤ᵇ-reflects-≤ i j
  ... | true   | ofʸ i≤j  = ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans j<i i≤j))
  ... | false  | _        = refl

  -- Below the index suc j it is strictly increasing, when j < m.
  keep-then-mono : ∀ {j m} → j <ℕ m → ∀ {i i′} → i <ℕ i′ → i′ ≤ℕ suc j → keep-then j m i <ℕ keep-then j m i′
  keep-then-mono {j} {m} j<m {i} {i′} i<i′ i′≤sj = from (m≤n⇒m<n∨m≡n i′≤sj)
    where
    i≤j : i ≤ℕ j
    i≤j = s≤s⁻¹ (<ℕ-≤-trans i<i′ i′≤sj)

    from : i′ <ℕ suc j ⊎ i′ ≡ suc j → keep-then j m i <ℕ keep-then j m i′
    from (inj₁ i′<sj)  = subst₂ _<ℕ_ (sym (keep-then-≤ i≤j)) (sym (keep-then-≤ (s≤s⁻¹ i′<sj))) i<i′
    from (inj₂ refl)   = subst₂ _<ℕ_ (sym (keep-then-≤ i≤j)) (sym (keep-then-> (n<1+n j))) (≤ℕ-trans (s≤s i≤j) j<m)

  keep-then-bound : ∀ {j m l} → j ≤ℕ l → m ≤ℕ l → ∀ {i} → i ≤ℕ suc j → keep-then j m i ≤ℕ l
  keep-then-bound {j} {m} {l} j≤l m≤l {i} i≤sj = from (m≤n⇒m<n∨m≡n i≤sj)
    where
    from : i <ℕ suc j ⊎ i ≡ suc j → keep-then j m i ≤ℕ l
    from (inj₁ i<sj)  = subst (_≤ℕ l) (sym (keep-then-≤ (s≤s⁻¹ i<sj))) (≤ℕ-trans (s≤s⁻¹ i<sj) j≤l)
    from (inj₂ refl)  = subst (_≤ℕ l) (sym (keep-then-> (n<1+n j))) m≤l

  -- The greatest index up to m with a decidable property, given one at i ≤ m.
  greatest-index : {P : ℕ → Type} (P? : ∀ i → Dec (P i)) → ∀ m i → i ≤ℕ m → P i
                 → Σ ℕ λ j → i ≤ℕ j × j ≤ℕ m × P j × (∀ i′ → j <ℕ i′ → i′ ≤ℕ m → ¬ P i′)
  greatest-index {P} P? zero     i i≤m Pi = i , ≤ℕ-refl , i≤m , Pi , λ i′ j<i′ i′≤0 → ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans j<i′ (≤ℕ-trans i′≤0 z≤n)))
  greatest-index {P} P? (suc m) i i≤sm Pi = decide (P? (suc m))
    where
    decide : Dec (P (suc m)) → Σ ℕ λ j → i ≤ℕ j × j ≤ℕ suc m × P j × (∀ i′ → j <ℕ i′ → i′ ≤ℕ suc m → ¬ P i′)
    decide (yes Psm) = suc m , i≤sm , ≤ℕ-refl , Psm , λ i′ sm<i′ i′≤sm → ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans sm<i′ i′≤sm))
    decide (no ¬Psm) = from (m≤n⇒m<n∨m≡n i≤sm)
      where
      from : i <ℕ suc m ⊎ i ≡ suc m → Σ ℕ λ j → i ≤ℕ j × j ≤ℕ suc m × P j × (∀ i′ → j <ℕ i′ → i′ ≤ℕ suc m → ¬ P i′)
      from (inj₂ e)    = ⊥-elim (¬Psm (subst P e Pi))
      from (inj₁ i<sm) = let (j , i≤j , j≤m , Pj , none) = greatest-index P? m i (s≤s⁻¹ i<sm) Pi
                         in j , i≤j , ≤ℕ-trans j≤m (n≤1+n m) , Pj , λ i′ j<i′ i′≤sm → bound i′ j<i′ (m≤n⇒m<n∨m≡n i′≤sm) none
        where
        bound : ∀ i′ → _ <ℕ i′ → i′ <ℕ suc m ⊎ i′ ≡ suc m → (∀ i′ → _ <ℕ i′ → i′ ≤ℕ m → ¬ P i′) → ¬ P i′
        bound i′ j<i′ (inj₁ i′<sm) none = none i′ j<i′ (s≤s⁻¹ i′<sm)
        bound i′ j<i′ (inj₂ e)     none = λ Pi′ → ¬Psm (subst P e Pi′)

  -- A reindexing continued flatly after the index S: keep up to S, then c, c + 1, … .
  after : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℕ
  after keep S c t = if t ≤ᵇ S then keep t else (t ∸ suc S) + c

  after-≤ : ∀ keep S c {t} → t ≤ℕ S → after keep S c t ≡ keep t
  after-≤ keep S c {t} t≤S with t ≤ᵇ S | ≤ᵇ-reflects-≤ t S
  ... | true   | _        = refl
  ... | false  | ofⁿ t≰S  = ⊥-elim (t≰S t≤S)

  after-> : ∀ keep S c {t} → S <ℕ t → after keep S c t ≡ (t ∸ suc S) + c
  after-> keep S c {t} S<t with t ≤ᵇ S | ≤ᵇ-reflects-≤ t S
  ... | true   | ofʸ t≤S  = ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans S<t t≤S))
  ... | false  | _        = refl

  after-suc : ∀ keep S c → after keep S c (suc S) ≡ c
  after-suc keep S c = trans (after-> keep S c (n<1+n S)) (cong (_+ c) (n∸n≡0 S))

  after-+ : ∀ keep S c l → after keep S c (l + suc S) ≡ l + c
  after-+ keep S c l = trans (after-> keep S c (m≤n+m (suc S) l)) (cong (_+ c) (m+n∸n≡m l (suc S)))

  -- It is strictly increasing when keep is, up to S, and c lies above keep S.
  after-mono : ∀ keep S c → (∀ {i j} → i <ℕ j → j ≤ℕ S → keep i <ℕ keep j) → keep S <ℕ c
             → ∀ {i j} → i <ℕ j → after keep S c i <ℕ after keep S c j
  after-mono keep S c mono S<c {i} {j} i<j = cases (i ≤ℕ? S) (j ≤ℕ? S)
    where
    keep≤ : i ≤ℕ S → keep i ≤ℕ keep S
    keep≤ i≤S = from (m≤n⇒m<n∨m≡n i≤S)
      where
      from : i <ℕ S ⊎ i ≡ S → keep i ≤ℕ keep S
      from (inj₁ i<S) = <⇒≤ (mono i<S ≤ℕ-refl)
      from (inj₂ e)   = ≤ℕ-reflexive (cong keep e)

    cases : Dec (i ≤ℕ S) → Dec (j ≤ℕ S) → after keep S c i <ℕ after keep S c j
    cases (yes i≤S) (yes j≤S) = subst₂ _<ℕ_ (sym (after-≤ keep S c i≤S)) (sym (after-≤ keep S c j≤S)) (mono i<j j≤S)
    cases (yes i≤S) (no j≰S)  = subst₂ _<ℕ_ (sym (after-≤ keep S c i≤S)) (sym (after-> keep S c (≰⇒> j≰S)))
                                  (<ℕ-≤-trans (≤ℕ-<-trans (keep≤ i≤S) S<c) (m≤n+m c _))
    cases (no i≰S)  (yes j≤S) = ⊥-elim (i≰S (≤ℕ-trans (<⇒≤ i<j) j≤S))
    cases (no i≰S)  (no j≰S)  = subst₂ _<ℕ_ (sym (after-> keep S c (≰⇒> i≰S))) (sym (after-> keep S c (≰⇒> j≰S)))
                                  (+-monoˡ-< c (∸-monoˡ-< i<j (≰⇒> i≰S)))

  -- It is bounded by N when keep is, up to S, and the continuation is, up to the index in view.
  after-bound : ∀ keep S c {N} → (∀ {i} → i ≤ℕ S → keep i ≤ℕ N) → ∀ {j} → (j ∸ suc S) + c ≤ℕ N
              → ∀ {i} → i ≤ℕ j → after keep S c i ≤ℕ N
  after-bound keep S c {N} bound {j} cj≤N {i} i≤j = cases (i ≤ℕ? S)
    where
    cases : Dec (i ≤ℕ S) → after keep S c i ≤ℕ N
    cases (yes i≤S) = subst (_≤ℕ N) (sym (after-≤ keep S c i≤S)) (bound i≤S)
    cases (no i≰S)  = subst (_≤ℕ N) (sym (after-> keep S c (≰⇒> i≰S))) (≤ℕ-trans (+-monoˡ-≤ c (∸-monoˡ-≤ (suc S) i≤j)) cj≤N)

  -- The least index up to m with a decidable property, given one.
  least-index : {P : ℕ → Type} (P? : ∀ i → Dec (P i)) → ∀ m → P m
              → Σ ℕ λ j → j ≤ℕ m × P j × (∀ i → i <ℕ j → ¬ P i)
  least-index {P} P? m Pm = find 0 m (λ i ()) (subst P (sym (+-identityʳ′ m)) Pm)
    where
    +-identityʳ′ : ∀ m → 0 + m ≡ m
    +-identityʳ′ m = refl

    find : ∀ s d → (∀ i → i <ℕ s → ¬ P i) → P (s + d) → Σ ℕ λ j → j ≤ℕ s + d × P j × (∀ i → i <ℕ j → ¬ P i)
    find s zero     none p = s , subst (s ≤ℕ_) (sym (+-identityʳ s)) ≤ℕ-refl , subst P (+-identityʳ s) p , none
    find s (suc d)  none p = decide (P? s)
      where
      decide : Dec (P s) → Σ ℕ λ j → j ≤ℕ s + suc d × P j × (∀ i → i <ℕ j → ¬ P i)
      decide (yes ps)  = s , subst (s ≤ℕ_) (sym (+-suc s d)) (<⇒≤ (s≤s (m≤m+n′ s d))) , ps , none
        where
        m≤m+n′ : ∀ s d → s ≤ℕ s + d
        m≤m+n′ zero     d = z≤n
        m≤m+n′ (suc s)  d = s≤s (m≤m+n′ s d)
      decide (no ¬ps)  = from (find (suc s) d none′ (subst P (+-suc s d) p))
        where
        none′ : ∀ i → i <ℕ suc s → ¬ P i
        none′ i i<ss pi with m≤n⇒m<n∨m≡n (s≤s⁻¹ i<ss)
        ... | inj₁ i<s   = none i i<s pi
        ... | inj₂ refl  = ¬ps pi

        from : Σ ℕ (λ j → j ≤ℕ suc s + d × P j × (∀ i → i <ℕ j → ¬ P i))
             → Σ ℕ λ j → j ≤ℕ s + suc d × P j × (∀ i → i <ℕ j → ¬ P i)
        from (j , j≤ , pj , least) = j , subst (j ≤ℕ_) (sym (+-suc s d)) j≤ , pj , least

  -- A minimal element with a decidable property, below a given one that has it.
  minimal-with : {P : Fin (suc n) → Type} (P? : ∀ y → Dec (P y)) → ∀ x → P x
               → Σ (Fin (suc n)) λ m → m ≤ x × P m × (∀ y → y < m → ¬ P y)
  minimal-with {P} P? x Px = go x (<-acc x) Px ≤-refl
    where
    go : ∀ y → Acc _<_ y → P y → y ≤ x → Σ (Fin (suc n)) λ m → m ≤ x × P m × (∀ z → z < m → ¬ P z)
    go y (acc smaller) Py y≤x = decide (any? λ z → z <? y ×-dec P? z)
      where
      decide : Dec (Σ (Fin (suc n)) λ z → z < y × P z) → Σ (Fin (suc n)) λ m → m ≤ x × P m × (∀ z → z < m → ¬ P z)
      decide (yes (z , z<y , Pz))  = go z (smaller z<y) Pz (≤-trans (proj₁ z<y) y≤x)
      decide (no none)             = y , y≤x , Py , λ z z<y Pz → none (z , z<y , Pz)

  -- (W) over a prefix join with a base: the meet lies below some x i, i < j, or below the base,
  -- unless a meetand lies below the whole join.
  W-⋁< : ∀ {s₁ s₂} x j {v} → s₁ ∧ s₂ ≤ ⋁< x j ∨ v
       → (s₁ ≤ ⋁< x j ∨ v ⊎ s₂ ≤ ⋁< x j ∨ v) ⊎ ((Σ ℕ λ i → i <ℕ j × s₁ ∧ s₂ ≤ x i) ⊎ s₁ ∧ s₂ ≤ v)
  W-⋁< {s₁} {s₂} x zero {v} h = cases (W s₁ s₂ ⊥ᴸ v h)
    where
    cases : (s₁ ≤ ⊥ᴸ ∨ v ⊎ s₂ ≤ ⊥ᴸ ∨ v) ⊎ (s₁ ∧ s₂ ≤ ⊥ᴸ ⊎ s₁ ∧ s₂ ≤ v) → _
    cases (inj₁ s)          = inj₁ s
    cases (inj₂ (inj₁ m≤⊥)) = inj₂ (inj₂ (≤-trans m≤⊥ (⊥ᴸ-least v)))
    cases (inj₂ (inj₂ m≤v)) = inj₂ (inj₂ m≤v)
  W-⋁< {s₁} {s₂} x (suc j) {v} h = cases (W s₁ s₂ (⋁< x j) (x j ∨ v) (≤-trans h assoc))
    where
    -- (⋁< x j ∨ x j) ∨ v ≤ ⋁< x j ∨ (x j ∨ v), and back.
    assoc : (⋁< x j ∨ x j) ∨ v ≤ ⋁< x j ∨ (x j ∨ v)
    assoc = ∨-least (∨-mono ≤-refl ∨-upperˡ) (≤∨ʳ ∨-upperʳ)

    assoc′ : ⋁< x j ∨ (x j ∨ v) ≤ (⋁< x j ∨ x j) ∨ v
    assoc′ = ∨-least (≤∨ˡ ∨-upperˡ) (∨-mono ∨-upperʳ ≤-refl)

    cases : (s₁ ≤ ⋁< x j ∨ (x j ∨ v) ⊎ s₂ ≤ ⋁< x j ∨ (x j ∨ v)) ⊎ (s₁ ∧ s₂ ≤ ⋁< x j ⊎ s₁ ∧ s₂ ≤ x j ∨ v) → _
    cases (inj₁ (inj₁ s₁≤))  = inj₁ (inj₁ (≤-trans s₁≤ assoc′))
    cases (inj₁ (inj₂ s₂≤))  = inj₁ (inj₂ (≤-trans s₂≤ assoc′))
    cases (inj₂ (inj₁ m≤⋁))  = inner (W-⋁< x j {⊥ᴸ} (≤-trans m≤⋁ ∨-upperˡ))
      where
      inner : _ → _
      inner (inj₁ (inj₁ s₁≤))       = inj₁ (inj₁ (≤-trans s₁≤ (∨-least (≤∨ˡ ∨-upperˡ) (⊥ᴸ-least _))))
      inner (inj₁ (inj₂ s₂≤))       = inj₁ (inj₂ (≤-trans s₂≤ (∨-least (≤∨ˡ ∨-upperˡ) (⊥ᴸ-least _))))
      inner (inj₂ (inj₁ (i , i<j , m≤)))  = inj₂ (inj₁ (i , <ℕ-trans i<j (n<1+n j) , m≤))
      inner (inj₂ (inj₂ m≤⊥))       = inj₂ (inj₂ (≤-trans m≤⊥ (⊥ᴸ-least v)))
    cases (inj₂ (inj₂ m≤xv))  = inner (W s₁ s₂ (x j) v m≤xv)
      where
      inner : _ → _
      inner (inj₁ (inj₁ s₁≤))  = inj₁ (inj₁ (≤-trans s₁≤ (∨-mono ∨-upperʳ ≤-refl)))
      inner (inj₁ (inj₂ s₂≤))  = inj₁ (inj₂ (≤-trans s₂≤ (∨-mono ∨-upperʳ ≤-refl)))
      inner (inj₂ (inj₁ m≤x))  = inj₂ (inj₁ (j , n<1+n j , m≤x))
      inner (inj₂ (inj₂ m≤v))  = inj₂ (inj₂ m≤v)

  -- A join irreducible element that is a binary join is one of the joinands.
  irr-∨ : ∀ {b u v} → HasOneLowerCover b → b ≡ u ∨ v → b ≡ u ⊎ b ≡ v
  irr-∨ {b} {u} {v} one e = decide (b ≟ u) (b ≟ v)
    where
    decide : Dec (b ≡ u) → Dec (b ≡ v) → b ≡ u ⊎ b ≡ v
    decide (yes b≡u) _          = inj₁ b≡u
    decide (no _)    (yes b≡v)  = inj₂ b≡v
    decide (no b≢u)  (no b≢v)   = ⊥-elim (proj₂ one (≤-antisym (₋≤ b) (subst (_≤ b ₋) (sym e) (∨-least u≤b₋ v≤b₋))))
      where
      u≤b₋ : u ≤ b ₋
      u≤b₋ = <→≤₋′ (subst (u ≤_) (sym e) ∨-upperˡ) λ u≡b → b≢u (sym u≡b)

      v≤b₋ : v ≤ b ₋
      v≤b₋ = <→≤₋′ (subst (v ≤_) (sym e) ∨-upperʳ) λ v≡b → b≢v (sym v≡b)

  -- A join irreducible element that is a prefix join over a base is the base or a member.
  irr-⋁< : ∀ {b} → HasOneLowerCover b → ∀ y m {z} → b ≡ ⋁< y m ∨ z → b ≡ z ⊎ (Σ ℕ λ i → i <ℕ m × b ≡ y i)
  irr-⋁< {b} one y zero {z} e = inj₁ (trans e (∨-absorbˡ (⊥ᴸ-least z)))
  irr-⋁< {b} one y (suc m) {z} e = cases (irr-∨ one e′)
    where
    e′ : b ≡ (⋁< y m ∨ z) ∨ y m
    e′ = trans e (≤-antisym (∨-least (∨-mono ∨-upperˡ ≤-refl) (≤∨ˡ ∨-upperʳ)) (∨-least (∨-mono ∨-upperˡ ≤-refl) (≤∨ˡ ∨-upperʳ)))

    cases : b ≡ ⋁< y m ∨ z ⊎ b ≡ y m → b ≡ z ⊎ (Σ ℕ λ i → i <ℕ suc m × b ≡ y i)
    cases (inj₂ b≡ym)  = inj₂ (m , n<1+n m , b≡ym)
    cases (inj₁ b≡)    = inner (irr-⋁< one y m b≡)
      where
      inner : _ → b ≡ z ⊎ (Σ ℕ λ i → i <ℕ suc m × b ≡ y i)
      inner (inj₁ b≡z)              = inj₁ b≡z
      inner (inj₂ (i , i<m , b≡yi)) = inj₂ (i , <ℕ-trans i<m (n<1+n m) , b≡yi)

  -- The lower cover of a₀ in an interval above a, when a < a₀: the join of the elements between.
  module LowerCoverAbove (a a₀ : Fin (suc n)) (a<a₀ : a < a₀) where

    between? : ∀ y → Dec (a ≤ y × y < a₀)
    between? y = a ≤? y ×-dec y <? a₀

    -- The elements of the interval strictly below a₀.
    between : Fin (suc n)
    between = ⋁ (filter between? (allFin (suc n)))

    a≤between : a ≤ between
    a≤between = ∨*-upper {cs = filter between? (allFin (suc n))} {⊥ᴸ} (∈-filter⁺ between? (∈-allFin a) (≤-refl , a<a₀))

    between≤ : ∀ {z} → (∀ y → a ≤ y → y < a₀ → y ≤ z) → between ≤ z
    between≤ f = ∨*-least {filter between? (allFin (suc n))} {⊥ᴸ}
      (All.tabulate λ y∈ → let (y∈all , a≤y , y<a₀) = ∈-filter⁻ between? {xs = allFin (suc n)} y∈ in f _ a≤y y<a₀)
      (⊥ᴸ-least _)

    -- If between ≠ a₀, it is a lower cover of a₀ in the interval.
    between⋖ : between ≢ a₀ → between ⋖ a₀
    between⋖ ne = (between≤ (λ y _ y<a₀ → proj₁ y<a₀) , ne)
                , λ c b<c c<a₀ → <-irrefl (<-≤-trans b<c (≤-trans (∨*-upper {cs = filter between? (allFin (suc n))} {⊥ᴸ}
                     (∈-filter⁺ between? (∈-allFin c) (≤-trans a≤between (proj₁ b<c) , c<a₀))) ≤-refl))
```

#### Lemmas 5.36 and 5.37

Fix a minimal C-cycle.  For Lemma 5.36, with `p₀ A₂ p₁`, the meet `p₀ ∧ κ p₁` is
`p₁₋`, which lies below `p₂ ∨ κ p₂` since `p₁` does; (W) applied there gives
four cases.  `p₀ ≤ p₂ ∨ κ p₂` would make `p₀ A p₂`, against minimality, and so
would `κ p₁ ≤ p₂ ∨ κ p₂`, through `p₀ ≤ p₁ ∨ κ p₁`.  `p₁₋ ≤ κ p₂` would put `p₂`
below `κ p₂`, since `p₂ < p₁` puts `p₂ ≤ p₁₋`.  So `p₁₋ ≤ p₂`, hence `p₂ = p₁₋`,
and then `p₁ ∧ κ p₂`, strictly below `p₁` and below `κ p₂`, is `p₂ ∧ κ p₂ = p₂₋`.
For Lemma 5.37, `q₀ ≤ q₀₋ ∨ q₁ ≤ q₀₋ ∨ q₁₋ ∨ q₂` with `q₀₋ ∨ q₁₋ ≤ κ q₀`, so
`q₂ ≰ κ q₀`; the free star principle gives `q₂₋ ≰ κ q₀`, hence `q₂₋ ≰ q₁₋`, and
`q₂₋ ≤ q₁` would put `q₂₋ ≤ q₁₋` or `q₁ = q₂₋ < q₂`.

```agda
  module InCycle (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞

    -- Lemma 5.36: p₀ A₂ p₁ A p₂ in a minimal C-cycle gives p₂ = p₁₋ and p₁ A₂ p₂.
    lemma-5-36 : ∀ {x} → Sub 2 x → x 0 A₂ x 1 → x 1 A x 2 → x 2 ≡ x 1 ₋ × x 1 A₂ x 2
    lemma-5-36 {x} sub (p₀Ap₁@(_ , i₁ , p₁<p₀ , p₀≤) , e) p₁Ap₂@(_ , i₂ , p₂<p₁ , p₁≤) =
      cases (W (x 0) (κ (x 1)) (x 2) (κ (x 2)) (subst (_≤ x 2 ∨ κ (x 2)) (sym e) (≤-trans (₋≤ (x 1)) p₁≤)))
      where
      -- p₀ A p₂ is excluded by minimality.
      ¬p₀Ap₂ : ¬ x 0 A x 2
      ¬p₀Ap₂ p₀Ap₂ = from (Sub-inorder sub z≤n ≤ℕ-refl (inj₁ p₀Ap₂))
        where
        from : 2 ≡ 1 ⊎ (0 ≡ 2 × 2 ≡ 0) → ⊥
        from (inj₁ ())
        from (inj₂ (() , _))

      p₂≤p₁₋ : x 2 ≤ x 1 ₋
      p₂≤p₁₋ = <→≤₋ p₂<p₁

      cases : (x 0 ≤ x 2 ∨ κ (x 2) ⊎ κ (x 1) ≤ x 2 ∨ κ (x 2)) ⊎ (x 0 ∧ κ (x 1) ≤ x 2 ⊎ x 0 ∧ κ (x 1) ≤ κ (x 2))
            → x 2 ≡ x 1 ₋ × x 1 A₂ x 2
      cases (inj₁ (inj₁ p₀≤′))   = ⊥-elim (¬p₀Ap₂ (proj₁ p₀Ap₁ , i₂ , <-trans p₂<p₁ p₁<p₀ , p₀≤′))
      cases (inj₁ (inj₂ κ₁≤))    = ⊥-elim (¬p₀Ap₂ (proj₁ p₀Ap₁ , i₂ , <-trans p₂<p₁ p₁<p₀
                                             , ≤-trans p₀≤ (∨-least p₁≤ κ₁≤)))
      cases (inj₂ (inj₂ m≤κ₂))   = ⊥-elim (a≰κ i₂ (≤-trans p₂≤p₁₋ (subst (_≤ κ (x 2)) e m≤κ₂)))
      cases (inj₂ (inj₁ m≤p₂))   = p₂≡p₁₋ , (p₁Ap₂ , p₁∧κ₂≡)
        where
        p₂≡p₁₋ : x 2 ≡ x 1 ₋
        p₂≡p₁₋ = ≤-antisym p₂≤p₁₋ (subst (_≤ x 2) e m≤p₂)

        -- p₁ ∧ κ p₂ lies strictly below p₁, hence below p₁₋ = p₂, and below κ p₂.
        p₁∧κ₂≡ : x 1 ∧ κ (x 2) ≡ x 2 ₋
        p₁∧κ₂≡ = ≤-antisym
          (≤-trans (∧-greatest (subst (x 1 ∧ κ (x 2) ≤_) (sym p₂≡p₁₋) (<→≤₋′ ∧-lowerˡ λ m≡p₁ → A→≰κ p₁Ap₂ (≤-from-∧ m≡p₁)))
                               ∧-lowerʳ)
                   (≤-reflexive′ (a∧κ i₂)))
          (∧-greatest (≤-trans (₋≤ (x 2)) (proj₁ p₂<p₁)) (₋≤κ (x 2)))
          where
          ≤-from-∧ : x 1 ∧ κ (x 2) ≡ x 1 → x 1 ≤ κ (x 2)
          ≤-from-∧ m≡p₁ = m≡p₁

    -- Lemma 5.37: q₀ B q₁ B q₂ in a minimal C-cycle gives q₁ B₁ q₂.
    lemma-5-37 : ∀ {x} → Sub 2 x → x 0 B x 1 → x 1 B x 2 → x 1 B₁ x 2
    lemma-5-37 {x} sub q₀Bq₁@(i₀ , i₁ , _ , q₀≤ , _) q₁Bq₂@(_ , i₂ , _ , q₁≤ , _) = q₁Bq₂ , q₂₋≰q₁
      where
      -- q₂ ≰ κ q₀, since q₀ ≤ q₀₋ ∨ q₁₋ ∨ q₂ and q₀₋ ∨ q₁₋ ≤ κ q₀.
      q₂≰κ₀ : ¬ x 2 ≤ κ (x 0)
      q₂≰κ₀ q₂≤κ₀ = a≰κ i₀ (≤-trans q₀≤ (∨-least (₋≤κ (x 0)) (≤-trans q₁≤ (∨-least (B→₋≤κ q₀Bq₁) q₂≤κ₀))))

      -- By the free star principle, q₂₋ ≰ κ q₀, hence q₂₋ ≰ q₁₋.
      q₂₋≰κ₀ : ¬ x 2 ₋ ≤ κ (x 0)
      q₂₋≰κ₀ q₂₋≤κ₀ = q₂≰κ₀ (Sub-freeStar′ sub z≤n ≤ℕ-refl (λ ()) (λ ()) (λ { (() , _) }) q₂₋≤κ₀)

      q₂₋≰q₁₋ : ¬ x 2 ₋ ≤ x 1 ₋
      q₂₋≰q₁₋ q₂₋≤q₁₋ = q₂₋≰κ₀ (≤-trans q₂₋≤q₁₋ (B→₋≤κ q₀Bq₁))

      q₂₋≰q₁ : ¬ x 2 ₋ ≤ x 1
      q₂₋≰q₁ q₂₋≤q₁ = q₂₋≰q₁₋ (<→≤₋′ q₂₋≤q₁ λ q₂₋≡q₁ → B→≰ q₁Bq₂ (subst (_≤ x 2) q₂₋≡q₁ (₋≤ (x 2))))
```

#### B-type sequences and Lemma 5.41

```agda
    -- A B-type sequence q 0, …, q k (FJN p. 113).
    record BType (k : ℕ) (q : ℕ → Fin (suc n)) : Type where
      field
        B1 : ∀ {i} → suc i ≤ℕ k → ¬ q i ₋ ≤ q (suc i)
        B2 : ∀ {i j} → i <ℕ j → j ≤ℕ k → q i ≤ κ (q j)
        B3 : ∀ {i} → suc i ≤ℕ k → q (suc i) ₋ ≤ κ (q i)
        B4 : ∀ {i j} → suc i <ℕ j → j ≤ℕ k → ¬ q j ₋ ≤ κ (q i)

    -- A prefix of a B-type sequence is a B-type sequence.
    BType-prefix : ∀ {k k′ q} → k′ ≤ℕ k → BType k q → BType k′ q
    BType-prefix k′≤k bt = record
      { B1 = λ si≤k′ → B1 (≤ℕ-trans si≤k′ k′≤k) ; B2 = λ i<j j≤k′ → B2 i<j (≤ℕ-trans j≤k′ k′≤k)
      ; B3 = λ si≤k′ → B3 (≤ℕ-trans si≤k′ k′≤k) ; B4 = λ si<j j≤k′ → B4 si<j (≤ℕ-trans j≤k′ k′≤k) }
      where open BType bt

    -- A B-type sequence shifted by m indices is a B-type sequence.
    BType-shift : ∀ {k q} m k′ → m + k′ ≤ℕ k → BType k q → BType k′ (λ i → q (m + i))
    BType-shift {k} {q} m k′ m+k′≤k bt = record
      { B1 = λ {i} si≤k′ → subst (λ z → ¬ q (m + i) ₋ ≤ q z) (sym (+-suc m i)) (B1 (bound si≤k′))
      ; B2 = λ {i} {j} i<j j≤k′ → B2 (+-monoʳ-< m i<j) (bound′ j≤k′)
      ; B3 = λ {i} si≤k′ → subst (λ z → q z ₋ ≤ κ (q (m + i))) (sym (+-suc m i)) (B3 (bound si≤k′))
      ; B4 = λ {i} {j} si<j j≤k′ → B4 {m + i} {m + j} (subst (_<ℕ m + j) (+-suc m i) (+-monoʳ-< m si<j)) (bound′ j≤k′) }
      where
      open BType bt
      bound′ : ∀ {j} → j ≤ℕ k′ → m + j ≤ℕ k
      bound′ j≤k′ = ≤ℕ-trans (+-monoʳ-≤ m j≤k′) m+k′≤k
      bound : ∀ {i} → suc i ≤ℕ k′ → suc (m + i) ≤ℕ k
      bound si≤k′ = subst (_≤ℕ k) (+-suc m _) (bound′ si≤k′)

    -- The same shift with the offset on the right, which reads the last member definitionally.
    BType-shiftʳ : ∀ {k q} m k′ → k′ + m ≤ℕ k → BType k q → BType k′ (λ i → q (i + m))
    BType-shiftʳ {k} {q} m k′ k′+m≤k bt = record
      { B1 = λ {i} si≤k′ → B1 (bound si≤k′)
      ; B2 = λ {i} {j} i<j j≤k′ → B2 (+-monoˡ-< m i<j) (bound′ j≤k′)
      ; B3 = λ {i} si≤k′ → B3 (bound si≤k′)
      ; B4 = λ {i} {j} si<j j≤k′ → B4 (+-monoˡ-< m si<j) (bound′ j≤k′) }
      where
      open BType bt
      bound′ : ∀ {j} → j ≤ℕ k′ → j + m ≤ℕ k
      bound′ j≤k′ = ≤ℕ-trans (+-monoˡ-≤ m j≤k′) k′+m≤k
      bound : ∀ {i} → suc i ≤ℕ k′ → suc (i + m) ≤ℕ k
      bound si≤k′ = bound′ si≤k′

    -- A family agreeing with a B-type sequence up to j ≤ k is a B-type sequence up to j.
    BType-cong : ∀ {k j q q′} → j ≤ℕ k → (∀ i → i ≤ℕ j → q′ i ≡ q i) → BType k q → BType j q′
    BType-cong {k} {j} {q} {q′} j≤k f bt = record
      { B1 = λ {i} si≤j → subst₂ (λ a b → ¬ a ₋ ≤ b) (sym (f i (<⇒≤ si≤j))) (sym (f (suc i) si≤j)) (B1 (≤ℕ-trans si≤j j≤k))
      ; B2 = λ {i} {j′} i<j′ j′≤j → subst₂ (λ a b → a ≤ κ b) (sym (f i (<⇒≤ (<ℕ-≤-trans i<j′ j′≤j)))) (sym (f j′ j′≤j)) (B2 i<j′ (≤ℕ-trans j′≤j j≤k))
      ; B3 = λ {i} si≤j → subst₂ (λ a b → a ₋ ≤ κ b) (sym (f (suc i) si≤j)) (sym (f i (<⇒≤ si≤j))) (B3 (≤ℕ-trans si≤j j≤k))
      ; B4 = λ {i} {j′} si<j′ j′≤j → subst₂ (λ a b → ¬ a ₋ ≤ κ b) (sym (f j′ j′≤j)) (sym (f i (<⇒≤ (<ℕ-≤-trans (<ℕ-trans (n<1+n i) si<j′) j′≤j)))) (B4 si<j′ (≤ℕ-trans j′≤j j≤k)) }
      where open BType bt

    -- Lemma 5.41: a subsequence q 0, …, q k of the cycle with q i B q (suc i) is a B-type sequence.
    module Lemma541 {k : ℕ} {q : ℕ → Fin (suc n)} (sub : Sub k q) (Bs : ∀ {i} → suc i ≤ℕ k → q i B q (suc i)) where

      -- κ q i < κ q j for i < j, by Lemma 2.63 along the chain.
      κ-chain : ∀ {i j} → i <ℕ j → j ≤ℕ k → κ (q i) < κ (q j)
      κ-chain {i} {suc j} i<sj sj≤k = from (m≤n⇒m<n∨m≡n (s≤s⁻¹ i<sj))
        where
        from : i <ℕ j ⊎ i ≡ j → κ (q i) < κ (q (suc j))
        from (inj₂ refl)  = B→κ< (Bs sj≤k)
        from (inj₁ i<j)   = <-trans (κ-chain i<j (<⇒≤ sj≤k)) (B→κ< (Bs sj≤k))

      -- (B2): q i ≤ κ q (suc i) by Lemma 2.58, then along the chain.
      B2′ : ∀ {i j} → i <ℕ j → j ≤ℕ k → q i ≤ κ (q j)
      B2′ {i} {j} i<j j≤k = from (m≤n⇒m<n∨m≡n i<j)
        where
        from : suc i <ℕ j ⊎ suc i ≡ j → q i ≤ κ (q j)
        from (inj₂ refl)  = B→≤κ (Bs j≤k)
        from (inj₁ si<j)  = ≤-trans (B→≤κ (Bs (<⇒≤ (<ℕ-≤-trans si<j j≤k)))) (proj₁ (κ-chain si<j j≤k))

      -- (B4) at distance two: q (suc (suc i))₋ ≰ κ q i, by the free star principle.
      B4-two : ∀ {i} → suc (suc i) ≤ℕ k → ¬ q (suc (suc i)) ₋ ≤ κ (q i)
      B4-two {i} ssi≤k q₋≤κ = q₂≰κ (Sub-freeStar′ sub (<⇒≤ (<⇒≤ ssi≤k)) ssi≤k (λ ()) (λ ()) (λ { (_ , ()) }) q₋≤κ)
        where
        -- q (suc i) ≤ q (suc i)₋ ∨ q (suc (suc i)), while q (suc i) ≰ κ q i and q (suc i)₋ ≤ κ q i.
        q₂≰κ : ¬ q (suc (suc i)) ≤ κ (q i)
        q₂≰κ q₂≤κ = B→≰κ (Bs (<⇒≤ ssi≤k))
          (≤-trans (proj₁ (proj₂ (proj₂ (proj₂ (Bs ssi≤k))))) (∨-least (B→₋≤κ (Bs (<⇒≤ ssi≤k))) q₂≤κ))

      -- (B4) in general, by induction on the distance beyond two.
      B4′ : ∀ d {i j} → j ≡ suc (suc i) + d → j ≤ℕ k → ¬ q j ₋ ≤ κ (q i)
      B4′ zero     {i} {j} e     j≤k = subst (λ j → ¬ q j ₋ ≤ κ (q i)) (sym e′) (B4-two (subst (_≤ℕ k) e′ j≤k))
        where
        e′ : j ≡ suc (suc i)
        e′ = trans e (+-identityʳ (suc (suc i)))
      B4′ (suc d)  {i} {j} e     j≤k q₋≤κ =
        B4′ d {suc i} (trans e (+-suc (suc (suc i)) d)) j≤k (≤-trans q₋≤κ (proj₁ (κ-chain (n<1+n i) si≤k)))
        where
        si≤k : suc i ≤ℕ k
        si≤k = ≤ℕ-trans (<⇒≤ (n<1+n (suc i))) (≤ℕ-trans (subst (suc (suc i) ≤ℕ_) (sym e) (m≤m+n′ (suc (suc i)) (suc d))) j≤k)
          where
          m≤m+n′ : ∀ s d → s ≤ℕ s + d
          m≤m+n′ zero     d = z≤n
          m≤m+n′ (suc s)  d = s≤s (m≤m+n′ s d)

      lemma-5-41 : BType k q
      lemma-5-41 = record
        { B1 = λ si≤k → B→≱′ (Bs si≤k)
        ; B2 = B2′
        ; B3 = λ si≤k → B→₋≤κ (Bs si≤k)
        ; B4 = λ {i} {j} si<j j≤k → B4′ (j ∸ suc (suc i)) (sym (m+[n∸m]≡n si<j)) j≤k }
        where
        open import Data.Nat.Base using ( _∸_ )
        open import Data.Nat.Properties using ( m+[n∸m]≡n )

        -- (B1): a B b gives a₋ ≰ b, since a ≰ a₋ ∨ b₋ and b ≤ b… no: a₋ ≤ b would put a ≤ a₋ ∨ b ≤ b.
        B→≱′ : ∀ {a b} → a B b → ¬ a ₋ ≤ b
        B→≱′ aBb@(_ , _ , _ , a≤ , _) a₋≤b = B→≰ aBb (≤-trans a≤ (∨-least a₋≤b ≤-refl))
```
