---
layout: default
file: "src/Lattices/Free/WhitmanChains.lagda.md"
title: "Lattices.Free.WhitmanChains module"
date: "2026-10-17"
author: "William DeMeo"
---

### The strict chains and Lemma 1.29

Theorem 1.23 makes the chains of Example 1.24 strict: equality of adjacent
iterates would be a fixed point.  This module proves their order reflects
the order of their indices, and establishes the exclusions of Lemma 1.29
in Freese, Ježek, and Nation, *Free Lattices* (1995).

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.WhitmanChains where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Empty using ( ⊥-elim )
open import Data.Fin.Patterns using ( 0F )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Base using ( ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s )
open import Data.Nat.Properties using ( ≤-<-connex )
open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base using ( [_,_]′ )
open import Relation.Binary.PropositionalEquality using ( sym ; subst ; subst₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable.Core using ( from-no ; from-yes )

open import Lattices.Free.Term using ( _∨̇_ )
open import Lattices.Free.Whitman
  using ( _≤ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ≤∧-inv ; ℊ≤∨-inv ; ∧≤ℊ-inv
        ; ∨≤-inv ; module Decision )
open import Lattices.Free.Duality using ( dual-reflects )
open import Lattices.Free.FixedPointFree using ( p-fixed-point-free )
open import Lattices.Free.WhitmanPolynomials
  using ( Term₃ ; x ; y ; z ; p ; f₅ ; iterate ; ascending ; descending
        ; core ; w ; p-mono ; b≰p ; p-a≰a ; a≰c ; ascending-step
        ; descending-step ; dual-ascending ; second-chain )
```

An increasing sequence with strict adjacent steps reflects its indices.
The decreasing form is written separately to keep its inequalities in the
same direction as the book's second chain.

```agda
-- Adjacent inequalities extend to every ordered pair of indices.
chain-mono : (s : ℕ → Term₃) → (∀ n → s n ≤ʷ s (suc n))
  → ∀ {m n} → m ≤ n → s m ≤ʷ s n
chain-mono s step {zero} {zero} z≤n = ≤ʷ-refl
chain-mono s step {zero} {suc n} z≤n =
  ≤ʷ-trans (step zero) (chain-mono (λ i → s (suc i)) (λ i → step (suc i)) z≤n)
chain-mono s step {suc m} {suc n} (s≤s h) =
  chain-mono (λ i → s (suc i)) (λ i → step (suc i)) h

-- Strict adjacent steps prohibit a reversed pair of indices.
chain-reflects : (s : ℕ → Term₃) → (step : ∀ n → s n ≤ʷ s (suc n))
  → (∀ n → ¬ (s (suc n) ≤ʷ s n)) → ∀ m n → s m ≤ʷ s n → m ≤ n
chain-reflects s step strict m n h =
  [ (λ e → e) , (λ e → ⊥-elim (strict n (≤ʷ-trans (chain-mono s step e) h))) ]′
    (≤-<-connex m n)

-- Adjacent inequalities extend along a decreasing sequence.
chain-antitone : (s : ℕ → Term₃) → (∀ n → s (suc n) ≤ʷ s n)
  → ∀ {m n} → m ≤ n → s n ≤ʷ s m
chain-antitone s step {zero} {zero} z≤n = ≤ʷ-refl
chain-antitone s step {zero} {suc n} z≤n =
  ≤ʷ-trans (chain-antitone (λ i → s (suc i)) (λ i → step (suc i)) z≤n) (step zero)
chain-antitone s step {suc m} {suc n} (s≤s h) =
  chain-antitone (λ i → s (suc i)) (λ i → step (suc i)) h

-- A strictly decreasing sequence reflects the reversed index order.
descending-reflects : (s : ℕ → Term₃) → (step : ∀ n → s (suc n) ≤ʷ s n)
  → (∀ n → ¬ (s n ≤ʷ s (suc n))) → ∀ m n → s m ≤ʷ s n → n ≤ m
descending-reflects s step strict m n h =
  [ (λ e → e) , (λ e → ⊥-elim (strict m (≤ʷ-trans h (chain-antitone s step e)))) ]′
    (≤-<-connex n m)

-- Example 1.24: every ascending step is strict by Theorem 1.23.
ascending-strict : ∀ n → ¬ (ascending (suc n) ≤ʷ ascending n)
ascending-strict n h = p-fixed-point-free 0F (ascending n) (h , ascending-step n)

-- The ascending chain reflects its index order.
ascending-reflects : ∀ m n → ascending m ≤ʷ ascending n → m ≤ n
ascending-reflects = chain-reflects ascending ascending-step ascending-strict

-- Every ascending term lies above x.
x≤ascending : ∀ n → x ≤ʷ ascending n
x≤ascending n = chain-mono ascending ascending-step {zero} {n} z≤n

-- Every descending term lies below x.
descending≤x : ∀ n → descending n ≤ʷ x
descending≤x n = chain-antitone descending descending-step {zero} {n} z≤n
```

Joining the descending terms with `y` gives iterates of `f₅`, by the
definitional identity in the polynomial module.  These iterates descend
strictly because `f₅` has no fixed point.

```agda
open Decision (_≟_ {3}) using ( _≤ʷ?_ )

-- The starting inequality for the second descending chain.
second-start : f₅ (x ∨̇ y) ≤ʷ x ∨̇ y
second-start = from-yes (f₅ (x ∨̇ y) ≤ʷ? x ∨̇ y)

-- All subsequent steps follow by monotonicity.
second-step : ∀ n → iterate f₅ (suc n) (x ∨̇ y) ≤ʷ iterate f₅ n (x ∨̇ y)
second-step zero = second-start
second-step (suc n) = p-mono (Lattices.Free.WhitmanPolynomials.rot 0F) (second-step n)

-- Equality of successive terms would be a fixed point of f₅.
second-strict : ∀ n → ¬ (iterate f₅ n (x ∨̇ y) ≤ʷ iterate f₅ (suc n) (x ∨̇ y))
second-strict n h = p-fixed-point-free (Lattices.Free.WhitmanPolynomials.rot 0F)
  (iterate f₅ n (x ∨̇ y)) (second-step n , h)

-- The joined descending terms reflect the reversed order of indices.
joined-descending-reflects : ∀ m n → descending m ∨̇ y ≤ʷ descending n ∨̇ y → n ≤ m
joined-descending-reflects m n h =
  descending-reflects (λ i → iterate f₅ i (x ∨̇ y)) second-step second-strict m n
    (subst₂ _≤ʷ_ (sym (second-chain m)) (sym (second-chain n)) h)
```

Lemma 1.29 holds at each positive index.  We also record the elementary
generator exclusions used in the two applications of Whitman's condition
in the proof of Theorem 1.28.

```agda
-- Distinct generators cannot be ordered.
x≰y : ¬ (x ≤ʷ y)
x≰y = from-no (x ≤ʷ? y)

-- The second and third generators are incomparable.
y≰z : ¬ (y ≤ʷ z)
y≰z = from-no (y ≤ʷ? z)

-- The converse comparison fails too.
z≰y : ¬ (z ≤ʷ y)
z≰y = from-no (z ≤ʷ? y)

-- The third generator is not below the first.
z≰x : ¬ (z ≤ʷ x)
z≰x = from-no (z ≤ʷ? x)

-- The middle generator is not below the first.
y≰x : ¬ (y ≤ʷ x)
y≰x = from-no (y ≤ʷ? x)

-- Lemma 1.29(1): y lies below no positive ascending term.
y≰ascending : ∀ n → ¬ (y ≤ʷ ascending (suc n))
y≰ascending n = b≰p 0F (ascending n)

-- Lemma 1.29(3): each ascending term lies above x, so not below z.
ascending≰z : ∀ n → ¬ (ascending n ≤ʷ z)
ascending≰z n h = a≰c 0F (≤ʷ-trans (x≤ascending n) h)

-- The first dual step already excludes x, and later terms are smaller.
x≰descending : ∀ n → ¬ (x ≤ʷ descending (suc n))
x≰descending n h = p-a≰a 0F
  (dual-reflects {t = x} {s = p 0F x}
    (≤ʷ-trans h (chain-antitone descending descending-step {1} {suc n} (s≤s z≤n))))

-- Lemma 1.29(2): primality reduces this to the ascending exclusion.
y≰w : ∀ n → ¬ (y ≤ʷ w (suc n))
y≰w n h = [ y≰z , (λ e → y≰ascending n (proj₁ (≤∧-inv e))) ]′ (ℊ≤∨-inv h)

-- Lemma 1.29(5): two uses of primality reduce to part (4).
x≰w : ∀ n → ¬ (x ≤ʷ w (suc n))
x≰w n h = [ a≰c 0F , (λ e →
  [ x≰descending n , x≰y ]′ (ℊ≤∨-inv (proj₂ (≤∧-inv e)))) ]′ (ℊ≤∨-inv h)

-- The third generator cannot lie below the joined descending term.
z≰descending∨y : ∀ n → ¬ (z ≤ʷ descending n ∨̇ y)
z≰descending∨y n h =
  [ (λ e → z≰x (≤ʷ-trans e (descending≤x n))) , z≰y ]′ (ℊ≤∨-inv h)

-- No meet core collapses below z.
core≰z : ∀ n → ¬ (core n ≤ʷ z)
core≰z n h =
  [ ascending≰z n , (λ e → y≰z (proj₂ (∨≤-inv e))) ]′ (∧≤ℊ-inv h)

-- Hence no family member collapses to its lower bound z.
w≰z : ∀ n → ¬ (w n ≤ʷ z)
w≰z n h = core≰z n (proj₂ (∨≤-inv h))

-- A positive ascending term cannot return to its initial value.
ascending≰x : ∀ n → ¬ (ascending (suc n) ≤ʷ x)
ascending≰x n h = p-a≰a 0F
  (≤ʷ-trans (chain-mono ascending ascending-step {1} {suc n} (s≤s z≤n)) h)

-- The dual of Lemma 1.29(1) excludes the middle generator above d_n.
descending≰y : ∀ n → ¬ (descending (suc n) ≤ʷ y)
descending≰y n h = y≰ascending n
  (dual-reflects {t = ascending (suc n)} {s = y}
    (subst (_≤ʷ y) (sym (dual-ascending (suc n))) h))

-- A positive meet core is not below x.
core≰x : ∀ n → ¬ (core (suc n) ≤ʷ x)
core≰x n h =
  [ ascending≰x n , (λ e → y≰x (proj₂ (∨≤-inv e))) ]′ (∧≤ℊ-inv h)

-- Nor is a positive meet core below y.
core≰y : ∀ n → ¬ (core (suc n) ≤ʷ y)
core≰y n h =
  [ (λ e → x≰y (≤ʷ-trans (x≤ascending (suc n)) e))
  , (λ e → descending≰y n (proj₁ (∨≤-inv e))) ]′ (∧≤ℊ-inv h)
```

#### The statement of Lemma 1.29

Lemma 1.29 is one definition whose type is the statement,
`FJN-1·29`{.AgdaFunction}, a record with one field for each of its five parts;
[Lattices.Free.FJN][] lists it with the rest of Chapter I.  In the book's
notation `cₙ = fⁿ(x)` is `ascending n`{.AgdaFunction}, `dₙ` is
`descending n`{.AgdaFunction}, and `wₙ = z ∨ (cₙ ∧ (dₙ ∨ y))` is
`w n`{.AgdaFunction}; for every `n ≥ 1`, written `suc n`: (1) `y ≰ cₙ`,
(2) `y ≰ wₙ`, (3) `cₙ ≰ z`, (4) `x ≰ dₙ`, (5) `x ≰ wₙ`.  The statement
quantifies over no level, so it is a type at level zero.

```agda
-- FJN Lemma 1.29: five non-inequalities between the generators and the chains.
record FJN-1·29 : Type where
  field
    part-1 : ∀ n → ¬ (y ≤ʷ ascending (suc n))
    part-2 : ∀ n → ¬ (y ≤ʷ w (suc n))
    part-3 : ∀ n → ¬ (ascending (suc n) ≤ʷ z)
    part-4 : ∀ n → ¬ (x ≤ʷ descending (suc n))
    part-5 : ∀ n → ¬ (x ≤ʷ w (suc n))

fjn-1·29 : FJN-1·29
fjn-1·29 = record  { part-1 = y≰ascending
                   ; part-2 = y≰w
                   ; part-3 = λ n → ascending≰z (suc n)
                   ; part-4 = x≰descending
                   ; part-5 = x≰w
                   }
```
