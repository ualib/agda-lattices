---
layout: default
file: "src/Lattices/Free/WhitmanPolynomials.lagda.md"
title: "Lattices.Free.WhitmanPolynomials module"
date: "2026-10-17"
author: "William DeMeo"
---

### Whitman's polynomials

The six unary polynomials preceding Theorem 1.23 of Freese, Ježek, and
Nation, *Free Lattices* (1995), are three cyclic instances of a polynomial
and their duals.  We retain the cyclic index explicitly, so the descent in
the proof of Theorem 1.23 can change the index without renaming a term.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.WhitmanPolynomials where

open import Data.Fin.Base using ( Fin ; toℕ )
open import Data.Fin.Patterns using ( 0F ; 1F ; 2F )
open import Data.Fin.Properties using ( _≟_ )
open import Data.Nat.Base using ( ℕ ; zero ; suc )
open import Data.Product using ( _,_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; cong )
open import Relation.Nullary using ( ¬_ )
open import Relation.Nullary.Decidable.Core using ( from-no )

open import Lattices.Free.Term using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman
  using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤∧ ; ≤ʷ-trans
        ; ∨̇-upperˡ ; ∨̇-upperʳ ; ∧̇-lowerˡ ; ∧̇-lowerʳ
        ; module Decision )
open import Lattices.Free.Duality using ( dual )
open import Lattices.Free.Substitution using ( Sub )

-- Terms over the three generators.
Term₃ : Set
Term₃ = LatTerm (Fin 3)

-- The cyclic permutation of the generator positions.
rot : Fin 3 → Fin 3
rot 0F = 1F
rot 1F = 2F
rot 2F = 0F

-- Three rotations return to the starting position.
rot³ : (k : Fin 3) → rot (rot (rot k)) ≡ k
rot³ 0F = refl
rot³ 1F = refl
rot³ 2F = refl

-- The generators in cyclic order, starting at k.
a b c : Fin 3 → Term₃
a k = ℊ k
b k = ℊ (rot k)
c k = ℊ (rot (rot k))

-- The three named generators used in Theorem 1.28.
x y z : Term₃
x = a 0F
y = b 0F
z = c 0F

-- The meet part of the polynomial, before its final join.
r : Fin 3 → Term₃ → Term₃
r k u = ((((u ∧̇ b k) ∨̇ c k) ∧̇ a k) ∨̇ b k) ∧̇ c k

-- The polynomial p(u,x,y,z), with cyclically permuted generators.
p : Fin 3 → Term₃ → Term₃
p k u = r k u ∨̇ a k

-- The dual polynomial, with the same generator positions.
q : Fin 3 → Term₃ → Term₃
q k u = (((((u ∨̇ b k) ∧̇ c k) ∨̇ a k) ∧̇ b k) ∨̇ c k) ∧̇ a k

-- FJN's six polynomials, in the order printed before Theorem 1.23.
f₁ f₂ f₃ f₄ f₅ f₆ : Term₃ → Term₃
f₁ = p 0F
f₂ = q 1F
f₃ = p 2F
f₄ = q 0F
f₅ = p 1F
f₆ = q 2F
```

Monotonicity follows by composing the monotonicity of meet and join.
Keeping these small order lemmas explicit avoids evaluating a decision on
a term whose argument is itself a large iterate.

```agda
-- Meeting with a fixed right operand is monotone.
meet-mono : ∀ {u v t : Term₃} → u ≤ʷ v → u ∧̇ t ≤ʷ v ∧̇ t
meet-mono h = ≤∧ (≤ʷ-trans ∧̇-lowerˡ h) ∧̇-lowerʳ

-- Joining with a fixed right operand is monotone.
join-mono : ∀ {u v t : Term₃} → u ≤ʷ v → u ∨̇ t ≤ʷ v ∨̇ t
join-mono h = ∨≤ (≤ʷ-trans h ∨̇-upperˡ) ∨̇-upperʳ

-- The meet part preserves the order of its argument.
r-mono : (k : Fin 3) {u v : Term₃} → u ≤ʷ v → r k u ≤ʷ r k v
r-mono k h = meet-mono (join-mono (meet-mono (join-mono (meet-mono h))))

-- Each cyclic instance of p is monotone.
p-mono : (k : Fin 3) {u v : Term₃} → u ≤ʷ v → p k u ≤ʷ p k v
p-mono k h = join-mono (r-mono k h)

-- Each cyclic instance of q is monotone.
q-mono : (k : Fin 3) {u v : Term₃} → u ≤ʷ v → q k u ≤ʷ q k v
q-mono k h = meet-mono (join-mono (meet-mono (join-mono (meet-mono (join-mono h)))))

-- Equality of arguments passes through the meet part.
r-cong : (k : Fin 3) {u v : Term₃} → u ≈ʷ v → r k u ≈ʷ r k v
r-cong k (h , h') = r-mono k h , r-mono k h'

-- Equality of arguments passes through p.
p-cong : (k : Fin 3) {u v : Term₃} → u ≈ʷ v → p k u ≈ʷ p k v
p-cong k (h , h') = p-mono k h , p-mono k h'

-- Equality of arguments passes through q.
q-cong : (k : Fin 3) {u v : Term₃} → u ≈ʷ v → q k u ≈ʷ q k v
q-cong k (h , h') = q-mono k h , q-mono k h'

-- Duality exchanges the two polynomials.
dual-p : (k : Fin 3) (u : Term₃) → dual (p k u) ≡ q k (dual u)
dual-p k u = refl

-- The other half of the exchange.
dual-q : (k : Fin 3) (u : Term₃) → dual (q k u) ≡ p k (dual u)
dual-q k u = refl

-- Equation (6) of FJN: the meet part intertwines p and a rotated q.
r-step : (k : Fin 3) (u : Term₃) → q (rot (rot k)) (r k u) ≡ r k (p k u)
r-step 0F u = refl
r-step 1F u = refl
r-step 2F u = refl
```

The range of each polynomial omits two principal filters.  The three
small decisions below are the bounds used in the proof of Theorem 1.23.
All further instances follow by monotonicity.

```agda
-- The greatest element of FL(3).
top : Term₃
top = (x ∨̇ y) ∨̇ z

-- Every generator lies below the greatest element.
gen≤top : (k : Fin 3) → ℊ k ≤ʷ top
gen≤top 0F = ≤ʷ-trans ∨̇-upperˡ ∨̇-upperˡ
gen≤top 1F = ≤ʷ-trans ∨̇-upperʳ ∨̇-upperˡ
gen≤top 2F = ∨̇-upperʳ

-- Every term lies below the greatest element.
term≤top : (u : Term₃) → u ≤ʷ top
term≤top (ℊ k) = gen≤top k
term≤top (u ∧̇ v) = ≤ʷ-trans ∧̇-lowerˡ (term≤top u)
term≤top (u ∨̇ v) = ∨≤ (term≤top u) (term≤top v)

private
  open Decision (_≟_ {3}) using ( _≤ʷ?_ )

  -- The middle generator is absent from the range's upper bound.
  b≰p-top : (k : Fin 3) → ¬ (b k ≤ʷ p k top)
  b≰p-top 0F = from-no (b 0F ≤ʷ? p 0F top)
  b≰p-top 1F = from-no (b 1F ≤ʷ? p 1F top)
  b≰p-top 2F = from-no (b 2F ≤ʷ? p 2F top)

  -- The last generator is absent from the same upper bound.
  c≰p-top : (k : Fin 3) → ¬ (c k ≤ʷ p k top)
  c≰p-top 0F = from-no (c 0F ≤ʷ? p 0F top)
  c≰p-top 1F = from-no (c 1F ≤ʷ? p 1F top)
  c≰p-top 2F = from-no (c 2F ≤ʷ? p 2F top)

-- The first iterate strictly exceeds its starting generator.
p-a≰a : (k : Fin 3) → ¬ (p k (a k) ≤ʷ a k)
p-a≰a 0F = from-no (p 0F (a 0F) ≤ʷ? a 0F)
p-a≰a 1F = from-no (p 1F (a 1F) ≤ʷ? a 1F)
p-a≰a 2F = from-no (p 2F (a 2F) ≤ʷ? a 2F)

-- Distinct first and last generators are incomparable.
a≰c : (k : Fin 3) → ¬ (a k ≤ʷ c k)
a≰c 0F = from-no (a 0F ≤ʷ? c 0F)
a≰c 1F = from-no (a 1F ≤ʷ? c 1F)
a≰c 2F = from-no (a 2F ≤ʷ? c 2F)

-- The middle generator lies below no value of p.
b≰p : (k : Fin 3) (u : Term₃) → ¬ (b k ≤ʷ p k u)
b≰p k u h = b≰p-top k (≤ʷ-trans h (p-mono k (term≤top u)))

-- The last generator lies below no value of p.
c≰p : (k : Fin 3) (u : Term₃) → ¬ (c k ≤ʷ p k u)
c≰p k u h = c≰p-top k (≤ʷ-trans h (p-mono k (term≤top u)))
```

The chains start at index zero.  The freely generating family of Theorem
1.28 starts at index one, so both the infinite substitution and its finite
restrictions use an explicit successor.

```agda
-- Iteration of a unary polynomial.
iterate : (Term₃ → Term₃) → ℕ → Term₃ → Term₃
iterate f zero u = u
iterate f (suc n) u = f (iterate f n u)

-- Example 1.24's ascending chain.
ascending : ℕ → Term₃
ascending n = iterate f₁ n x

-- The dual descending chain in Theorem 1.28.
descending : ℕ → Term₃
descending n = iterate f₄ n x

-- The meet inside Whitman's freely generating elements.
core : ℕ → Term₃
core n = ascending n ∧̇ (descending n ∨̇ y)

-- The elements w_n of Theorem 1.28, including the unused w_0.
w : ℕ → Term₃
w n = z ∨̇ core n

-- The countable family begins with w_1.
σ : Sub ℕ (Fin 3)
σ n = w (suc n)

-- Restriction to the first n members.
σ-finite : (n : ℕ) → Sub (Fin n) (Fin 3)
σ-finite n i = σ (toℕ i)

-- The identity behind the second chain is definitional at one step.
f₅-join : (u : Term₃) → f₅ (u ∨̇ y) ≡ f₄ u ∨̇ y
f₅-join u = refl

-- Its iterated form, used to recover the reverse inequality of indices.
second-chain : (n : ℕ) → iterate f₅ n (x ∨̇ y) ≡ descending n ∨̇ y
second-chain zero = refl
second-chain (suc n) = cong f₅ (second-chain n)

-- The two chains are dual term by term.
dual-ascending : (n : ℕ) → dual (ascending n) ≡ descending n
dual-ascending zero = refl
dual-ascending (suc n) = cong f₄ (dual-ascending n)

-- Each ascending term lies below its successor.
ascending-step : (n : ℕ) → ascending n ≤ʷ ascending (suc n)
ascending-step zero = ∨̇-upperʳ
ascending-step (suc n) = p-mono 0F (ascending-step n)

-- Each descending successor lies below its predecessor.
descending-step : (n : ℕ) → descending (suc n) ≤ʷ descending n
descending-step zero = ∧̇-lowerʳ
descending-step (suc n) = q-mono 0F (descending-step n)
```
