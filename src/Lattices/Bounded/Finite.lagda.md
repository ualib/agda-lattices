---
layout: default
file: "src/Lattices/Bounded/Finite.lagda.md"
title: "Lattices.Bounded.Finite module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Join dependency and lower boundedness in a finite lattice

This is the [Lattices.Bounded.Finite][] module of the [agda-lattices][] library.

In a lattice `L`, an element `a` *depends* on an element `b`, written `a D b`,
when `a ≠ b`, `b` is join irreducible, and some `x` has `a ≤ b ∨ x` while
`a ≰ c ∨ x` for every `c < b` ([Freese, Ježek, and Nation (1995)][], p. 39).  In a
finite lattice a join irreducible element `b` has exactly one lower cover `b₋`,
and the last condition reads `a ≰ b₋ ∨ x`.  A *D-cycle* is a sequence of join
irreducible elements `a₀ D a₁ D ⋯ D aₙ₋₁ D a₀` (p. 41), and a finite lattice is
lower bounded if and only if it has none (Corollary 2.39).  This module develops
that finite theory for the table lattices of [Lattices.Table][], whose carrier is
`Fin n` with propositional equality, so that every predicate here is decidable and
every proof by contradiction is a case split on a decision.  It supplies the
following:

+  **Lower covers** (`_₋`{.AgdaFunction}, `HasOneLowerCover`{.AgdaFunction}).
   `b ₋` is the join of the elements strictly below `b`, and `b` has one lower
   cover, namely `b ₋`, exactly when `b ₋ < b`.  These are the join irreducible
   elements `J(L)` of a finite lattice, with FJN's convention (p. 8) that the
   least element is not one; the predicate is named for what it says, not
   `IsJoinIrreducible`, which elsewhere in the library is the binary notion, under
   which the least element of a lattice is join irreducible.
+  **The D relation** (`_D_`{.AgdaFunction}, decided by `_D?_`{.AgdaFunction}).
   Its left side is any element, as in FJN's definition; Day's original
   definition, which FJN's note 3 on p. 39 recalls, also asks `a` to be join
   irreducible.  Since `a D b` forces `b` to be join irreducible, every D-cycle
   lies in `J(L)` either way, so the two relations have the same cycles.
+  **Lower boundedness** (`LowerBounded`{.AgdaFunction}, decided by
   `lowerBounded?`{.AgdaFunction}), defined as the absence of a D-cycle, the
   right-hand side of Corollary 2.39.  FJN define a finitely generated lattice
   to be lower bounded by the equivalent conditions of their Theorem 2.13, one
   of which is `D(L) = L` (p. 34), through the sets `Dₖ(L)` of p. 31; those sets
   are defined in [Lattices.Bounded.Covers][], not here.  Of the agreement of
   the two definitions for finite lattices, which is Corollary 2.39, one half,
   that a table lattice with no D-cycle has `D(L) = L`, is
   `lowerBounded→D-total`{.AgdaFunction} of [Lattices.Kostinsky.Finite][]; the
   other half is stated, not proved.
   `Bounded`{.AgdaFunction} is lower bounded and dually upper bounded.
+  **Well-foundedness** (`D-acc`{.AgdaFunction}).  On a finite set, a decidable
   relation with no cycle is well founded, since a path longer than the number of
   elements repeats one (`no-cycle→acc`{.AgdaFunction}, by the standard library's
   pigeonhole principle).  In a lower bounded finite lattice, then, every element
   is accessible for the converse of `D`, and a proof can descend along `D` by
   well-founded induction with no rank function.  The same lemma makes the strict
   order well founded (`<-acc`{.AgdaFunction}).
+  **The D-rank** (`ρ`{.AgdaFunction}), the length of the longest D-path from an
   element, by recursion along that accessibility; it strictly decreases along
   `D` (`ρ-decreasing`{.AgdaFunction}).  FJN's D-rank (p. 31) is the least `k`
   with `a ∈ Dₖ(L)`; the two are not compared here.
+  **Minimal join covers** (`minimal-cover`{.AgdaFunction}).  Every nontrivial
   join cover of `p` refines to a minimal nontrivial join cover, in FJN's sense
   (p. 30), whose members are join irreducible and each a dependency of `p`: the
   properties FJN Lemma 2.31 gives every minimal nontrivial join cover, here for
   the one the proof constructs.  The *escape lemma* (`escape`{.AgdaFunction})
   reads off, from a cover `{x, y}`, one member below `x` and not below `y`.
+  **Join irreducible elements below an element**
   (`separate`{.AgdaFunction}, `join-of-irreducibles`{.AgdaFunction}): every
   element is the join of the join irreducible elements below it, so `s ≰ t`
   puts some join irreducible element below `s` and not below `t`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Bounded.Finite where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ) renaming ( _<_ to _<ᶠ_ )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; any? ; ¬∀⟶∃¬ ; pigeonhole )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; foldr ; filter ; allFin )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-allFin )
open import Data.List.Properties                   using ( foldr-++ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.All.Properties using ( ++⁺ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; s≤s ; z≤n ; _⊔_ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( n<1+n ; m≤m⊔n ; m≤n⊔m )
                                                   renaming ( ≤-trans to ≤ℕ-trans ; ≤-refl to ≤ℕ-refl )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( flip ; _∘_ ; id )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Relation.Binary.Construct.Closure.Transitive
                                                   using ( TransClosure ; [_] ; _∷_ ; _∷ʳ_ ; transitive⁻ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; ¬? ; _×-dec_ ; _→-dec_
                                                         ; decidable-stable )

import Data.List.Membership.DecPropositional as DecMembership
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Anyₚ

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice  using ( module Lattice-Order )
open import Lattices.Table                using ( LatticeTableLaws ; tableLattice )
```
-->

#### A relation with no cycle on a finite set

Fix a decidable relation `_≻_` on `Fin n`, read as a step from an element to a
smaller one.  `Short k a`{.AgdaFunction} says that every `≻`-path from `a` has
fewer than `k` steps; it is decidable by recursion on `k`, and an element all of
whose paths are short is accessible for the converse relation
(`short→acc`{.AgdaFunction}).  If not every path from `a` is short, the decision
finds a first step whose target again has a long path
(`long-step`{.AgdaFunction}), and iterating it gives the points of a path of `k`
steps (`point`{.AgdaFunction}), along which every point reaches every later one
(`point-reach`{.AgdaFunction}).  A path of `n` steps has `n + 1` points in a set
of `n` elements, so two of them coincide, which closes a cycle
(`long→cycle`{.AgdaFunction}).  Conversely an accessible element lies on no
cycle (`acc→no-cycle`{.AgdaFunction}), by induction on accessibility, rotating
the cycle one step at each descent.  So the absence of a cycle gives
accessibility of every element (`no-cycle→acc`{.AgdaFunction}), and the
existence of a cycle is decidable (`cycle?`{.AgdaFunction}).

The decision explores the paths of at most `n` steps from every element, so its
cost grows with their number: it is fast on small acyclic lattices (30 ms for the
five-element lattice `N₅`), and on a lattice with a cycle, where the paths
multiply, an explicit cycle is the cheaper certificate.

```agda
module _ {n : ℕ} {_≻_ : Fin n → Fin n → Type} (_≻?_ : ∀ a b → Dec (a ≻ b)) where

  -- Every ≻-path from a has fewer than k steps.
  Short : ℕ → Fin n → Type
  Short zero     a = ⊥
  Short (suc k)  a = ∀ b → a ≻ b → Short k b

  short? : ∀ k a → Dec (Short k a)
  short? zero     a = no λ ()
  short? (suc k)  a = all? λ b → a ≻? b →-dec short? k b

  -- An element all of whose paths are short is accessible.
  short→acc : ∀ k {a} → Short k a → Acc (flip _≻_) a
  short→acc (suc k) s = acc λ {b} a≻b → short→acc k (s b a≻b)

  -- The first step of a path that is not short.
  long-step : ∀ k a → ¬ Short (suc k) a → Σ (Fin n) λ b → a ≻ b × ¬ Short k b
  long-step k a ¬s with ¬∀⟶∃¬ n _ (λ b → a ≻? b →-dec short? k b) ¬s
  ... | b , ¬step with a ≻? b
  ...   | yes a≻b  = b , a≻b , λ s → ¬step λ _ → s
  ...   | no ¬a≻b  = ⊥-elim (¬step λ a≻b → ⊥-elim (¬a≻b a≻b))

  -- The points of a path of k steps from a.
  point : ∀ k a → ¬ Short k a → Fin (suc k) → Fin n
  point k        a ¬s zero     = a
  point (suc k)  a ¬s (suc i)  =
    point k (proj₁ (long-step k a ¬s)) (proj₂ (proj₂ (long-step k a ¬s))) i

  -- Along the path, every point reaches every later one.
  point-reach : ∀ k a ¬s {i j : Fin (suc k)} → i <ᶠ j
              → TransClosure _≻_ (point k a ¬s i) (point k a ¬s j)
  point-reach (suc k) a ¬s {zero} {suc zero} _ = [ proj₁ (proj₂ (long-step k a ¬s)) ]
  point-reach (suc k) a ¬s {zero} {suc (suc j)} _ =
    proj₁ (proj₂ (long-step k a ¬s)) ∷ point-reach k _ _ {zero} {suc j} (s≤s z≤n)
  point-reach (suc k) a ¬s {suc i} {suc j} (s≤s i<j) = point-reach k _ _ i<j

  -- A path of n steps through n elements repeats one, which closes a cycle.
  long→cycle : ∀ a → ¬ Short n a → Σ (Fin n) λ b → TransClosure _≻_ b b
  long→cycle a ¬s with pigeonhole (n<1+n n) (point n a ¬s)
  ... | i , j , i<j , pi≡pj =
    point n a ¬s i , subst (TransClosure _≻_ (point n a ¬s i)) (sym pi≡pj) (point-reach n a ¬s i<j)

  -- An accessible element lies on no cycle.
  acc→no-cycle : ∀ {a} → Acc (flip _≻_) a → ¬ TransClosure _≻_ a a
  acc→no-cycle (acc rs) [ a≻a ]      = acc→no-cycle (rs a≻a) [ a≻a ]
  acc→no-cycle (acc rs) (a≻b ∷ b⁺a)  = acc→no-cycle (rs a≻b) (b⁺a ∷ʳ a≻b)

  -- With no cycle, every element is accessible.
  no-cycle→acc : (∀ a → ¬ TransClosure _≻_ a a) → ∀ a → Acc (flip _≻_) a
  no-cycle→acc nc a = short→acc n (decidable-stable (short? n a) λ ¬s →
    let (b , b⁺b) = long→cycle a ¬s in nc b b⁺b)

  -- Whether there is a cycle is decidable.
  cycle? : Dec (Σ (Fin n) λ a → TransClosure _≻_ a a)
  cycle? with all? (short? n)
  ... | yes short  = no λ (a , a⁺a) → acc→no-cycle (short→acc n (short a)) a⁺a
  ... | no ¬short  = let (a , ¬s) = ¬∀⟶∃¬ n (Short n) (short? n) ¬short in yes (long→cycle a ¬s)
```

#### Maxima of finite families of numbers

`⨆ᶠ f`{.AgdaFunction} is the largest value of a finite family of numbers, used
for the D-rank below.

```agda
-- The largest value of a finite family of numbers (0 for the empty family).
⨆ᶠ : ∀ {m} → (Fin m → ℕ) → ℕ
⨆ᶠ {zero}   f = 0
⨆ᶠ {suc m}  f = f zero ⊔ ⨆ᶠ (f ∘ suc)

≤⨆ᶠ : ∀ {m} (f : Fin m → ℕ) i → f i ≤ℕ ⨆ᶠ f
≤⨆ᶠ f zero     = m≤m⊔n _ _
≤⨆ᶠ f (suc i)  = ≤ℕ-trans (≤⨆ᶠ (f ∘ suc) i) (m≤n⊔m _ _)

⨆ᶠ-cong : ∀ {m} {f g : Fin m → ℕ} → (∀ i → f i ≡ g i) → ⨆ᶠ f ≡ ⨆ᶠ g
⨆ᶠ-cong {zero}   f≡g = refl
⨆ᶠ-cong {suc m}  f≡g = cong₂ _⊔_ (f≡g zero) (⨆ᶠ-cong (f≡g ∘ suc))
```

#### The finite lattice of a pair of tables

The rest of the module is about one table lattice, given by its two tables on
`Fin (suc n)` and their laws.  (The carrier is nonempty, so that the least element
can be named.)  The order is the meet order of [Classical.Properties.Lattice][],
`a ≤ b` meaning `a ∧ b ≡ a`, decided by the meet table, and `_<_`{.AgdaFunction}
is the strict order.  The module re-exports the order lemmas it uses, so that a
client opens only `JoinDependency laws`{.AgdaModule}.

```agda
module JoinDependency {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                      (laws : LatticeTableLaws _∧_ _∨_) where

  open Lattice-Order (tableLattice _∧_ _∨_ laws) public
    using ( _≤_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest
          ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open DecMembership (_≟_ {suc n}) using ( _∈?_ )

  infix 4 _≤?_ _<_ _<?_

  -- The order is decided by the meet table.
  _≤?_ : ∀ a b → Dec (a ≤ b)
  a ≤? b = (a ∧ b) ≟ a

  -- The strict order.
  _<_ : Fin (suc n) → Fin (suc n) → Type
  a < b = a ≤ b × a ≢ b

  _<?_ : ∀ a b → Dec (a < b)
  a <? b = a ≤? b ×-dec ¬? (a ≟ b)

  <-irrefl : ∀ {a} → ¬ a < a
  <-irrefl (_ , a≢a) = a≢a refl

  <-≤-trans : ∀ {a b c} → a < b → b ≤ c → a < c
  <-≤-trans (a≤b , a≢b) b≤c = ≤-trans a≤b b≤c , λ { refl → a≢b (≤-antisym a≤b b≤c) }

  ≤-<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
  ≤-<-trans a≤b (b≤c , b≢c) = ≤-trans a≤b b≤c , λ { refl → b≢c (≤-antisym b≤c a≤b) }

  <-trans : ∀ {a b c} → a < b → b < c → a < c
  <-trans a<b b<c = <-≤-trans a<b (proj₁ b<c)

  -- The strict order is well founded.
  <-acc : ∀ a → Acc _<_ a
  <-acc = no-cycle→acc (λ a b → b <? a) λ a a⁺a → <-irrefl (transitive⁻ _ (flip <-trans) a⁺a)
```

#### Finite joins and the least element

The meet of all the elements is the least element `⊥ᴸ`{.AgdaFunction}, and
`cs ∨* z`{.AgdaFunction} is the join of a list of elements and a base element
`z`, so that the join `⋁ cs`{.AgdaFunction} of a list, empty or not, is
`cs ∨* ⊥ᴸ`.  The base is what lets a descent below carry the rest of a join cover
as one element.

```agda
  -- The meet of all the elements is the least element.
  ⊥ᴸ : Fin (suc n)
  ⊥ᴸ = foldr _∧_ zero (allFin (suc n))

  ⊥ᴸ-least : ∀ a → ⊥ᴸ ≤ a
  ⊥ᴸ-least a = lower (allFin (suc n)) (∈-allFin a)
    where
    lower : ∀ {z} xs → a ∈ xs → foldr _∧_ z xs ≤ a
    lower (x ∷ xs) (here refl)  = ∧-lowerˡ
    lower (x ∷ xs) (there a∈)   = ≤-trans ∧-lowerʳ (lower xs a∈)

  infixr 5 _∨*_

  -- The join of a list of elements and a base element.
  _∨*_ : List (Fin (suc n)) → Fin (suc n) → Fin (suc n)
  cs ∨* z = foldr _∨_ z cs

  ∨*-base : ∀ cs {z} → z ≤ cs ∨* z
  ∨*-base []        = ≤-refl
  ∨*-base (c ∷ cs)  = ≤-trans (∨*-base cs) ∨-upperʳ

  ∨*-upper : ∀ {c cs z} → c ∈ cs → c ≤ cs ∨* z
  ∨*-upper (here refl)  = ∨-upperˡ
  ∨*-upper (there c∈)   = ≤-trans (∨*-upper c∈) ∨-upperʳ

  ∨*-least : ∀ {cs z w} → All (_≤ w) cs → z ≤ w → cs ∨* z ≤ w
  ∨*-least []            z≤w = z≤w
  ∨*-least (c≤w ∷ cs≤w)  z≤w = ∨-least c≤w (∨*-least cs≤w z≤w)

  ∨*-mono : ∀ cs {z z'} → z ≤ z' → cs ∨* z ≤ cs ∨* z'
  ∨*-mono cs {z} {z'} z≤z' =
    ∨*-least {cs} {z} (All.tabulate λ c∈ → ∨*-upper {cs = cs} {z'} c∈) (≤-trans z≤z' (∨*-base cs))

  -- The join of a list.
  ⋁ : List (Fin (suc n)) → Fin (suc n)
  ⋁ cs = cs ∨* ⊥ᴸ
```

#### Lower covers

`below b`{.AgdaFunction} lists the elements strictly below `b`, and
`b ₋`{.AgdaFunction} is their join.  It lies below `b` (`₋≤`{.AgdaFunction}) and
above every element strictly below `b` (`<→≤₋`{.AgdaFunction}).  So if
`b ₋ < b`, then `b ₋` is the largest element strictly below `b`, hence a lower
cover of `b` (`₋⋖`{.AgdaFunction}) and the only one (`⋖→₋`{.AgdaFunction}); and
if not, then `b ₋ = b` (`¬one→₋≡`{.AgdaFunction}), and `b` is the least element
(the join of the empty list) or the join of the elements strictly below it.  The
converse of the first statement, that an element with exactly one lower cover
has `b ₋ < b`, also holds in a finite lattice; it is not needed here.

```agda
  -- The elements strictly below b.
  below : Fin (suc n) → List (Fin (suc n))
  below b = filter (_<? b) (allFin (suc n))

  ∈below⁺ : ∀ {b c} → c < b → c ∈ below b
  ∈below⁺ {b} {c} c<b = ∈-filter⁺ (_<? b) (∈-allFin c) c<b

  ∈below⁻ : ∀ {b c} → c ∈ below b → c < b
  ∈below⁻ {b} c∈ = proj₂ (∈-filter⁻ (_<? b) c∈)

  infix 10 _₋

  -- The join of the elements strictly below b.
  _₋ : Fin (suc n) → Fin (suc n)
  b ₋ = ⋁ (below b)

  ₋≤ : ∀ b → b ₋ ≤ b
  ₋≤ b = ∨*-least (All.tabulate λ c∈ → proj₁ (∈below⁻ c∈)) (⊥ᴸ-least b)

  <→≤₋ : ∀ {b c} → c < b → c ≤ b ₋
  <→≤₋ c<b = ∨*-upper (∈below⁺ c<b)

  -- b has a largest element strictly below it, b ₋, which is then its one lower cover.
  HasOneLowerCover : Fin (suc n) → Type
  HasOneLowerCover b = b ₋ < b

  hasOneLowerCover? : ∀ b → Dec (HasOneLowerCover b)
  hasOneLowerCover? b = b ₋ <? b

  infix 4 _⋖_

  -- a is a lower cover of b.
  _⋖_ : Fin (suc n) → Fin (suc n) → Type
  a ⋖ b = a < b × ∀ c → a < c → ¬ c < b

  ₋⋖ : ∀ {b} → HasOneLowerCover b → b ₋ ⋖ b
  ₋⋖ b₋<b = b₋<b , λ c b₋<c c<b → <-irrefl (<-≤-trans b₋<c (<→≤₋ c<b))

  ⋖→₋ : ∀ {a b} → a ⋖ b → HasOneLowerCover b → a ≡ b ₋
  ⋖→₋ {a} {b} (a<b , cover) b₋<b with a ≟ b ₋
  ... | yes a≡b₋  = a≡b₋
  ... | no a≢b₋   = ⊥-elim (cover (b ₋) (<→≤₋ a<b , a≢b₋) b₋<b)

  -- Without one lower cover, b is the join of the elements strictly below it.
  ¬one→₋≡ : ∀ {b} → ¬ HasOneLowerCover b → b ₋ ≡ b
  ¬one→₋≡ {b} ¬one with b ₋ ≟ b
  ... | yes b₋≡b  = b₋≡b
  ... | no b₋≢b   = ⊥-elim (¬one (₋≤ b , b₋≢b))
```

#### The join dependency relation

The relation is FJN's, with the lower cover in place of the elements below `b`,
and it is decided by a sweep over the witness `x`.  A D-cycle is an element that
depends on itself through a chain of dependencies, the standard library's
transitive closure of `D` at a point; since `D` is irreflexive, such a chain has
at least two steps, and its elements are join irreducible, so this is FJN's
D-cycle of p. 41.

```agda
  infix 4 _D_ _D?_

  -- a D b: a ≠ b, b has one lower cover, and some x has a ≤ b ∨ x and a ≰ b₋ ∨ x.
  _D_ : Fin (suc n) → Fin (suc n) → Type
  a D b = a ≢ b × HasOneLowerCover b × Σ (Fin (suc n)) λ x → a ≤ (b ∨ x) × ¬ a ≤ ((b ₋) ∨ x)

  _D?_ : ∀ a b → Dec (a D b)
  a D? b = ¬? (a ≟ b) ×-dec hasOneLowerCover? b
           ×-dec any? λ x → a ≤? (b ∨ x) ×-dec ¬? (a ≤? ((b ₋) ∨ x))

  -- A D-cycle: an element that depends on itself through a chain of dependencies.
  DCycle : Type
  DCycle = Σ (Fin (suc n)) λ a → TransClosure _D_ a a

  dCycle? : Dec DCycle
  dCycle? = cycle? _D?_

  -- A finite lattice is lower bounded when it has no D-cycle (FJN Corollary 2.39).
  LowerBounded : Type
  LowerBounded = ¬ DCycle

  lowerBounded? : Dec LowerBounded
  lowerBounded? = ¬? dCycle?

  -- In a lower bounded finite lattice the converse of D is well founded.
  D-acc : LowerBounded → ∀ a → Acc (flip _D_) a
  D-acc lb = no-cycle→acc _D?_ λ a a⁺a → lb (a , a⁺a)
```

#### The D-rank

`rankᴰ a acc`{.AgdaFunction} is one more than the largest rank of an element `a`
depends on, and `0` when there is none, by recursion on the accessibility proof
`acc`; it does not depend on the proof (`rankᴰ-irrelevant`{.AgdaFunction}), and it
strictly decreases along `D` (`rankᴰ-decreasing`{.AgdaFunction}).  In a lower
bounded lattice every element is accessible, which gives the D-rank
`ρ`{.AgdaFunction}.

```agda
  -- The length of the longest D-path from a, by recursion along accessibility.
  rankᴰ       : ∀ a → Acc (flip _D_) a → ℕ
  rankᴰ-step  : ∀ {a} → (∀ {b} → a D b → Acc (flip _D_) b) → ∀ b → Dec (a D b) → ℕ

  rankᴰ a (acc rs) = ⨆ᶠ λ b → rankᴰ-step rs b (a D? b)
  rankᴰ-step rs b (yes aDb)  = suc (rankᴰ b (rs aDb))
  rankᴰ-step rs b (no _)     = 0

  -- The rank does not depend on the accessibility proof.
  rankᴰ-irrelevant : ∀ a p q → rankᴰ a p ≡ rankᴰ a q
  rankᴰ-irrelevant a (acc rs) (acc rs') = ⨆ᶠ-cong λ b → step-irrelevant b (a D? b)
    where
    step-irrelevant : ∀ b d → rankᴰ-step rs b d ≡ rankᴰ-step rs' b d
    step-irrelevant b (yes aDb)  = cong suc (rankᴰ-irrelevant b (rs aDb) (rs' aDb))
    step-irrelevant b (no _)     = refl

  -- The rank strictly decreases along D.
  rankᴰ-decreasing : ∀ {a b} (p : Acc (flip _D_) a) (q : Acc (flip _D_) b) → a D b → rankᴰ b q <ℕ rankᴰ a p
  rankᴰ-decreasing {a} {b} (acc rs) q aDb =
    ≤ℕ-trans (step-yes (a D? b)) (≤⨆ᶠ (λ b' → rankᴰ-step rs b' (a D? b')) b)
    where
    step-yes : ∀ d → suc (rankᴰ b q) ≤ℕ rankᴰ-step rs b d
    step-yes (yes aDb')  = s≤s (subst (_≤ℕ rankᴰ b (rs aDb')) (rankᴰ-irrelevant b (rs aDb') q) ≤ℕ-refl)
    step-yes (no ¬aDb)   = ⊥-elim (¬aDb aDb)

  -- The D-rank of an element of a lower bounded finite lattice.
  ρ : LowerBounded → Fin (suc n) → ℕ
  ρ lb a = rankᴰ a (D-acc lb a)

  ρ-decreasing : (lb : LowerBounded) → ∀ {a b} → a D b → ρ lb b <ℕ ρ lb a
  ρ-decreasing lb = rankᴰ-decreasing (D-acc lb _) (D-acc lb _)
```

#### Minimal join covers

A *join cover* of `p` is a finite set `Q` with `p ≤ ⋁Q`; it is *nontrivial* if
`p ≰ q` for every `q ∈ Q`, and it *refines* `R`, `Q ≪ R`, if every member of `Q`
lies below some member of `R`.  A nontrivial join cover `Q` of `p` is *minimal*
if every join cover of `p` that refines `Q` contains `Q` (FJN p. 30).  The proof
that a nontrivial join cover refines to a minimal one is a descent,
`refine`{.AgdaFunction}, on one member `u` at a time, the rest of the cover joined
into a base `w`; the invariant is `p ≤ u ∨ w`, `p ≰ u`, and the result is a list
of members below `u` that, with `w`, covers `p` and is minimal over the base `w`
(`Refinement`{.AgdaRecord}).  The cases, by well-founded induction on `u` in the
strict order, are the following:

+  If `p ≤ w`, no member is needed (`refine-nil`{.AgdaFunction}).
+  If `u` has one lower cover and `p ≰ u₋ ∨ w`, then `u` itself is a refinement
   (`refine-single`{.AgdaFunction}): `p D u` via `w`, and a join cover refining
   `{u}` that omits `u` lies below `u₋`, hence fails to cover `p` over `w`.
+  If `u` has one lower cover and `p ≤ u₋ ∨ w`, the descent replaces `u` by `u₋`.
+  If `u` has not one lower cover, it is not the least element (else
   `p ≤ w`), so it is the join `a ∨ b` of two smaller elements
   (`two-below`{.AgdaFunction}).  The descent refines `b` over the base `a ∨ w`,
   then `a` over the base formed by the first result and `w`, and
   `refine-join`{.AgdaFunction} combines the two; minimality of the union is
   inherited from the two parts, by splitting a refining cover into the members
   below some member of the first part and the rest.

`refine-list`{.AgdaFunction} runs the descent on the members of a finite join
cover in turn, combining as `refine-join` does, and `minimal-cover`{.AgdaFunction}
starts it with the base `⊥ᴸ`.  The minimal cover is found by the descent, not
chosen by a measure among all the refinements.  `escape`{.AgdaFunction} applies it
to `{x, y}` and reads off a member below `x` and not below `y`, which exists since
otherwise `p ≤ ⋁Q ≤ y`.

```agda
  infix 4 _≪_

  -- Join refinement: every element of A lies below some element of B.
  _≪_ : List (Fin (suc n)) → List (Fin (suc n)) → Type
  A ≪ B = All (λ a → Any (a ≤_) B) A

  any≤→≤∨* : ∀ {x R z} → Any (x ≤_) R → x ≤ R ∨* z
  any≤→≤∨* (here x≤r)  = ≤-trans x≤r ∨-upperˡ
  any≤→≤∨* (there x≤)  = ≤-trans (any≤→≤∨* x≤) ∨-upperʳ

  any≤→≤ : ∀ {x a R} → Any (x ≤_) R → All (_≤ a) R → x ≤ a
  any≤→≤ (here x≤r)  (r≤a ∷ _)    = ≤-trans x≤r r≤a
  any≤→≤ (there x≤)  (_ ∷ R≤a)    = any≤→≤ x≤ R≤a

  -- An element that is a join of smaller elements, and not the least one, is a join of two.
  two-below : ∀ {u} cs z → All (_< u) cs → z < u → cs ∨* z ≡ u
            → Σ (Fin (suc n)) λ a → Σ (Fin (suc n)) λ b → a < u × b < u × a ∨ b ≡ u
  two-below {u} [] z _ z<u z≡u = ⊥-elim (<-irrefl (subst (_< u) z≡u z<u))
  two-below {u} (c ∷ cs) z (c<u ∷ cs<u) z<u c∨s≡u with (cs ∨* z) ≟ u
  ... | yes s≡u  = two-below cs z cs<u z<u s≡u
  ... | no s≢u   = c , cs ∨* z , c<u , (∨*-least (All.map proj₁ cs<u) (proj₁ z<u) , s≢u) , c∨s≡u

  module _ (p : Fin (suc n)) where

    -- A refinement of a join cover of p over the base w: members join irreducible, each a
    -- D-dependency of p, minimal among the covers that refine it.
    record Refinement (w : Fin (suc n)) : Type where
      field
        members      : List (Fin (suc n))
        covers       : p ≤ members ∨* w
        irreducible  : All HasOneLowerCover members
        depends      : All (p D_) members
        minimal      : ∀ B → B ≪ members → p ≤ B ∨* w → All (_∈ B) members

    open Refinement

    -- Nothing is needed when p lies below the base.
    refine-nil : ∀ {w} → p ≤ w → Refinement w
    refine-nil p≤w = record { members = [] ; covers = p≤w ; irreducible = [] ; depends = []
                            ; minimal = λ _ _ _ → [] }

    -- An element with one lower cover u₋ and p ≰ u₋ ∨ w is a refinement by itself.
    refine-single : ∀ {u w} → ¬ p ≤ u → p ≤ u ∨ w → HasOneLowerCover u → ¬ p ≤ (u ₋) ∨ w
                  → Refinement w
    refine-single {u} {w} p≰u p≤ one p≰ = record
      { members      = u ∷ []
      ; covers       = p≤
      ; irreducible  = one ∷ []
      ; depends      = ((λ { refl → p≰u ≤-refl }) , one , w , p≤ , p≰) ∷ []
      ; minimal      = λ B B≪ p≤B → u∈ B B≪ p≤B ∷ []
      }
      where
      u∈ : ∀ B → B ≪ u ∷ [] → p ≤ B ∨* w → u ∈ B
      u∈ B B≪ p≤B = decidable-stable (u ∈? B) λ u∉B →
        p≰ (≤-trans p≤B (∨*-least (All.tabulate λ b∈ → ≤-trans (<→≤₋ (b<u b∈ u∉B)) ∨-upperˡ) ∨-upperʳ))
        where
        b<u : ∀ {b} → b ∈ B → ¬ u ∈ B → b < u
        b<u {b} b∈ u∉B with All.lookup B≪ b∈
        ... | here b≤u = b≤u , λ { refl → u∉B b∈ }

    -- Refinements of b over a ∨ w and of a over the first one's join with w combine into one.
    refine-join : ∀ {a w} (Rb : Refinement (a ∨ w)) (Ra : Refinement (members Rb ∨* w))
                → All (_≤ a) (members Ra) → Refinement w
    refine-join {a} {w} Rb Ra Ra≤a = record
      { members      = members Ra ++ members Rb
      ; covers       = subst (p ≤_) (sym (foldr-++ _∨_ w (members Ra) (members Rb))) (covers Ra)
      ; irreducible  = ++⁺ (irreducible Ra) (irreducible Rb)
      ; depends      = ++⁺ (depends Ra) (depends Rb)
      ; minimal      = minimal′
      }
      where
      inA? : ∀ x → Dec (Any (x ≤_) (members Ra))
      inA? x = Any.any? (x ≤?_) (members Ra)

      minimal′ : ∀ B → B ≪ members Ra ++ members Rb → p ≤ B ∨* w
               → All (_∈ B) (members Ra ++ members Rb)
      minimal′ B B≪ p≤B = ++⁺ (All.map (λ x∈ → proj₁ (∈-filter⁻ inA? {xs = B} x∈)) (minimal Ra B₁ B₁≪ p≤B₁))
                              (All.map (λ x∈ → proj₁ (∈-filter⁻ (¬? ∘ inA?) {xs = B} x∈))
                                       (minimal Rb B₂ B₂≪ p≤B₂))
        where
        B₁ B₂ : List (Fin (suc n))
        B₁ = filter inA? B
        B₂ = filter (¬? ∘ inA?) B

        B₁≪ : B₁ ≪ members Ra
        B₁≪ = All.tabulate λ x∈ → proj₂ (∈-filter⁻ inA? {xs = B} x∈)

        B₂≪ : B₂ ≪ members Rb
        B₂≪ = All.tabulate λ x∈ →
          let (x∈B , ¬inA) = ∈-filter⁻ (¬? ∘ inA?) {xs = B} x∈
          in [ (λ inA → ⊥-elim (¬inA inA)) , id ]′ (Anyₚ.++⁻ (members Ra) (All.lookup B≪ x∈B))

        p≤B₁ : p ≤ B₁ ∨* (members Rb ∨* w)
        p≤B₁ = ≤-trans p≤B (∨*-least (All.tabulate split) (≤-trans (∨*-base (members Rb)) (∨*-base B₁)))
          where
          split : ∀ {x} → x ∈ B → x ≤ B₁ ∨* (members Rb ∨* w)
          split {x} x∈ with inA? x
          ... | yes inA  = ∨*-upper (∈-filter⁺ inA? x∈ inA)
          ... | no ¬inA  = ≤-trans (any≤→≤∨* (All.lookup B₂≪ (∈-filter⁺ (¬? ∘ inA?) x∈ ¬inA)))
                                   (∨*-base B₁)

        p≤B₂ : p ≤ B₂ ∨* (a ∨ w)
        p≤B₂ = ≤-trans p≤B (∨*-least (All.tabulate split) (≤-trans ∨-upperʳ (∨*-base B₂)))
          where
          split : ∀ {x} → x ∈ B → x ≤ B₂ ∨* (a ∨ w)
          split {x} x∈ with inA? x
          ... | yes inA  = ≤-trans (≤-trans (any≤→≤ inA Ra≤a) ∨-upperˡ) (∨*-base B₂)
          ... | no ¬inA  = ∨*-upper (∈-filter⁺ (¬? ∘ inA?) x∈ ¬inA)

    -- The base can be traded with a join of the members.
    shift : ∀ {a w} R → R ∨* (a ∨ w) ≤ a ∨ (R ∨* w)
    shift {a} {w} R = ∨*-least (All.tabulate λ r∈ → ≤-trans (∨*-upper {cs = R} {w} r∈) ∨-upperʳ)
                               (∨-least ∨-upperˡ (≤-trans (∨*-base R) ∨-upperʳ))

    -- A join cover {u} ∪ {w} of p refines to a minimal one below u, by descent on u.
    refine : ∀ u → Acc _<_ u → ∀ w → ¬ p ≤ u → p ≤ u ∨ w
           → Σ (Refinement w) λ R → All (_≤ u) (members R)
    refine u (acc rs) w p≰u p≤ with p ≤? w
    ... | yes p≤w = refine-nil p≤w , []
    ... | no p≰w with hasOneLowerCover? u
    ...   | yes one with p ≤? (u ₋) ∨ w
    ...     | no p≰u₋∨w = refine-single p≰u p≤ one p≰u₋∨w , ≤-refl ∷ []
    ...     | yes p≤u₋∨w =
      let (R , R≤u₋) = refine (u ₋) (rs one) w (λ p≤u₋ → p≰u (≤-trans p≤u₋ (₋≤ u))) p≤u₋∨w
      in R , All.map (λ r≤ → ≤-trans r≤ (₋≤ u)) R≤u₋
    refine u (acc rs) w p≰u p≤ | no p≰w | no ¬one with ⊥ᴸ ≟ u
    ... | yes ⊥≡u = ⊥-elim (p≰w (≤-trans p≤ (∨-least (subst (_≤ w) ⊥≡u (⊥ᴸ-least w)) ≤-refl)))
    ... | no ⊥≢u with two-below (below u) ⊥ᴸ (All.tabulate ∈below⁻) (⊥ᴸ-least u , ⊥≢u) (¬one→₋≡ ¬one)
    ...   | a , b , a<u , b<u , a∨b≡u =
      let (Rb , Rb≤b) = refine b (rs b<u) (a ∨ w) (λ p≤b → p≰u (≤-trans p≤b (proj₁ b<u)))
                               (≤-trans p≤ (subst (λ v → v ∨ w ≤ b ∨ (a ∨ w)) a∨b≡u
                                 (∨-least (∨-least (≤-trans ∨-upperˡ ∨-upperʳ) ∨-upperˡ)
                                          (≤-trans ∨-upperʳ ∨-upperʳ))))
          (Ra , Ra≤a) = refine a (rs a<u) (members Rb ∨* w) (λ p≤a → p≰u (≤-trans p≤a (proj₁ a<u)))
                               (≤-trans (covers Rb) (shift (members Rb)))
      in refine-join Rb Ra Ra≤a
       , ++⁺ (All.map (λ r≤ → ≤-trans r≤ (proj₁ a<u)) Ra≤a) (All.map (λ r≤ → ≤-trans r≤ (proj₁ b<u)) Rb≤b)

    -- The base can be traded back.
    unshift : ∀ {a w} R → a ∨ (R ∨* w) ≤ R ∨* (a ∨ w)
    unshift R = ∨-least (≤-trans ∨-upperˡ (∨*-base R)) (∨*-mono R ∨-upperʳ)

    -- A join cover R of p over the base w, with p below none of its members, refines to a
    -- minimal one over w, member by member.
    refine-list : ∀ R w → All (λ r → ¬ p ≤ r) R → p ≤ R ∨* w → Σ (Refinement w) λ Q → members Q ≪ R
    refine-list []       w _            p≤w = refine-nil p≤w , []
    refine-list (r ∷ R)  w (p≰r ∷ p≰R)  p≤  =
      let (Q′ , Q′≪R) = refine-list R (r ∨ w) p≰R (≤-trans p≤ (unshift R))
          (Qr , Qr≤r) = refine r (<-acc r) (members Q′ ∨* w) p≰r
                               (≤-trans (covers Q′) (shift (members Q′)))
      in refine-join Q′ Qr Qr≤r , ++⁺ (All.map here Qr≤r) (All.map there Q′≪R)

    -- Below a member of R, an element is not above p.
    below-member : ∀ {q R} → Any (q ≤_) R → All (λ r → ¬ p ≤ r) R → ¬ p ≤ q
    below-member (here q≤r)  (p≰r ∷ _)  p≤q = p≰r (≤-trans p≤q q≤r)
    below-member (there q≤)  (_ ∷ p≰R)  p≤q = below-member q≤ p≰R p≤q

    -- FJN p. 30: a minimal nontrivial join cover of p refining R, of join irreducible elements,
    -- each of which p depends on (the properties FJN Lemma 2.31 gives every such cover).
    record MinimalJoinCover (R : List (Fin (suc n))) : Type where
      field
        cover        : List (Fin (suc n))
        joins        : p ≤ ⋁ cover
        nontrivial   : All (λ q → ¬ p ≤ q) cover
        refines      : cover ≪ R
        irreducibles : All HasOneLowerCover cover
        dependencies : All (p D_) cover
        minimality   : ∀ B → B ≪ cover → p ≤ ⋁ B → All (_∈ B) cover

    -- A nontrivial join cover of p refines to a minimal one.
    minimal-cover : ∀ R → p ≤ ⋁ R → All (λ r → ¬ p ≤ r) R → MinimalJoinCover R
    minimal-cover R p≤ p≰R = record
      { cover         = members Q
      ; joins         = covers Q
      ; nontrivial    = All.map (λ q≤ → below-member q≤ p≰R) Q≪R
      ; refines       = Q≪R
      ; irreducibles  = irreducible Q
      ; dependencies  = depends Q
      ; minimality    = minimal Q
      }
      where
      Q : Refinement ⊥ᴸ
      Q = proj₁ (refine-list R ⊥ᴸ p≰R p≤)
      Q≪R : members Q ≪ R
      Q≪R = proj₂ (refine-list R ⊥ᴸ p≰R p≤)

    -- The escape lemma: some q with one lower cover lies below x and not below y, and p D q.
    escape : ∀ {x y} → p ≤ x ∨ y → ¬ p ≤ x → ¬ p ≤ y
           → Σ (Fin (suc n)) λ q → p D q × q ≤ x × ¬ q ≤ y
    escape {x} {y} p≤ p≰x p≰y =
      from-cover (minimal-cover (x ∷ y ∷ []) (≤-trans p≤ (∨-least ∨-upperˡ (≤-trans ∨-upperˡ ∨-upperʳ)))
                                (p≰x ∷ p≰y ∷ []))
      where
      from-cover : MinimalJoinCover (x ∷ y ∷ []) → Σ (Fin (suc n)) λ q → p D q × q ≤ x × ¬ q ≤ y
      from-cover C = pick (Any.any? (λ q → ¬? (q ≤? y)) cover)
        where
        open MinimalJoinCover C

        below-x : ∀ {q} → q ∈ cover → ¬ q ≤ y → q ≤ x
        below-x q∈ q≰y with All.lookup refines q∈
        ... | here q≤x          = q≤x
        ... | there (here q≤y)  = ⊥-elim (q≰y q≤y)

        pick : Dec (Any (λ q → ¬ q ≤ y) cover) → Σ (Fin (suc n)) λ q → p D q × q ≤ x × ¬ q ≤ y
        pick (yes some) =
          let (q , q∈ , q≰y) = find some in q , All.lookup dependencies q∈ , below-x q∈ q≰y , q≰y
        pick (no none) = ⊥-elim (p≰y (≤-trans joins (∨*-least (All.tabulate λ q∈ →
                           decidable-stable (_ ≤? y) λ q≰y → none (lose q∈ q≰y)) (⊥ᴸ-least y))))
```

#### Join irreducible elements below an element

`separate`{.AgdaFunction} descends from `s` in the strict order: `s` itself, if
it has one lower cover, and otherwise some element strictly below `s` and not
below `t`, which exists since `s` is the join of those elements.  It follows that
every element is the join of the join irreducible elements below it
(`join-of-irreducibles`{.AgdaFunction}).

```agda
  -- If s ≰ t, some element with one lower cover lies below s and not below t.
  separate : ∀ {s t} → ¬ s ≤ t → Σ (Fin (suc n)) λ p → HasOneLowerCover p × p ≤ s × ¬ p ≤ t
  separate {s} {t} = go s (<-acc s)
    where
    go : ∀ s → Acc _<_ s → ¬ s ≤ t → Σ (Fin (suc n)) λ p → HasOneLowerCover p × p ≤ s × ¬ p ≤ t
    go s (acc rs) s≰t with hasOneLowerCover? s
    ... | yes one = s , one , ≤-refl , s≰t
    ... | no ¬one with Any.any? (λ c → ¬? (c ≤? t)) (below s)
    ...   | yes some =
      let (c , c∈ , c≰t) = find some
          (q , one , q≤c , q≰t) = go c (rs (∈below⁻ c∈)) c≰t
      in q , one , ≤-trans q≤c (proj₁ (∈below⁻ c∈)) , q≰t
    ...   | no none = ⊥-elim (s≰t (subst (_≤ t) (¬one→₋≡ ¬one)
                        (∨*-least (All.tabulate λ c∈ → decidable-stable (_ ≤? t) λ c≰t → none (lose c∈ c≰t))
                                  (⊥ᴸ-least t))))

  -- The join irreducible elements below s.
  irreducibles-below : Fin (suc n) → List (Fin (suc n))
  irreducibles-below s = filter (λ q → hasOneLowerCover? q ×-dec q ≤? s) (allFin (suc n))

  -- Every element is the join of the join irreducible elements below it.
  join-of-irreducibles : ∀ s → ⋁ (irreducibles-below s) ≡ s
  join-of-irreducibles s = ≤-antisym
    (∨*-least {irreducibles-below s} {⊥ᴸ}
      (All.tabulate λ q∈ → proj₂ (proj₂ (∈-filter⁻ J? {xs = allFin (suc n)} q∈))) (⊥ᴸ-least s))
    (decidable-stable (s ≤? ⋁ (irreducibles-below s)) λ s≰ →
      let (q , one , q≤s , q≰) = separate s≰
      in q≰ (∨*-upper {cs = irreducibles-below s} {⊥ᴸ} (∈-filter⁺ J? (∈-allFin q) (one , q≤s))))
    where
    J? : ∀ q → Dec (HasOneLowerCover q × q ≤ s)
    J? q = hasOneLowerCover? q ×-dec q ≤? s
```

#### Upper boundedness

The dual of a pair of lattice tables is the pair swapped
(`dual-laws`{.AgdaFunction}), and its join dependency relation is the meet
dependency relation `Dᵈ` of the original (`MeetDependency`{.AgdaModule}).  A
finite lattice is upper bounded when `Dᵈ` has no cycle, and bounded when it is
lower and upper bounded.

The module checks in 0.9 s of its own under `--profile=modules` (measured
2026-10-22).

```agda
-- The dual of a pair of lattice tables is a pair of lattice tables.
dual-laws : ∀ {n} {_∧_ _∨_ : Fin n → Fin n → Fin n} → LatticeTableLaws _∧_ _∨_ → LatticeTableLaws _∨_ _∧_
dual-laws {_∧_ = _∧_} {_∨_} (∧-assoc , ∧-comm , ∧-idem , ∨-assoc , ∨-comm , ∨-idem , absorbˡ , absorbʳ) =
  ∨-assoc , ∨-comm , ∨-idem , ∧-assoc , ∧-comm , ∧-idem
  , (λ a b → trans (∨-comm a (a ∧ b)) (absorbʳ a b))
  , (λ a b → trans (∧-comm (a ∨ b) a) (absorbˡ a b))

-- The meet dependency relation is the join dependency relation of the dual.
module MeetDependency {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                      (laws : LatticeTableLaws _∧_ _∨_) = JoinDependency (dual-laws laws)

module _ {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)} (laws : LatticeTableLaws _∧_ _∨_) where

  -- Upper bounded: no meet dependency cycle.
  UpperBounded : Type
  UpperBounded = MeetDependency.LowerBounded laws

  -- Bounded: lower and upper bounded.
  Bounded : Type
  Bounded = JoinDependency.LowerBounded laws × UpperBounded

  bounded? : Dec Bounded
  bounded? = JoinDependency.lowerBounded? laws ×-dec MeetDependency.lowerBounded? laws
```
