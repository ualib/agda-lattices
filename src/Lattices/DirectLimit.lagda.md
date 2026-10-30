---
layout: default
file: "src/Lattices/DirectLimit.lagda.md"
title: "Lattices.DirectLimit module"
date: "2026-10-28"
author: "the agda-algebras development team"
---

### Direct limits of sequences of lattices

This is the [Lattices.DirectLimit][] module of the [agda-lattices][] library.

A sequence of lattices `L₀, L₁, L₂, …` with homomorphisms
`θₖ : Lₖ → Lₖ₊₁` has a *direct limit*: a lattice `L` with homomorphisms
`ιₖ : Lₖ → L` such that `ιₖ₊₁ ∘ θₖ = ιₖ`, universal among lattices with such
a family.  The construction is the one for sets with the operations computed at
a common stage ([Bergman (2015)][], Chapter 8, in its section on direct and
inverse limits): an element of `L` is a pair `(k , x)` with `x` in `Lₖ`, two
pairs are equal when their images at some common later stage are equal, and the
meet and the join of two pairs are computed at the larger of their two stages.
When every `θₖ` is an embedding, the canonical maps `ιₖ` are embeddings too, and
`L` is the union of the stages read as a chain of sublattices of it;
[Lattices.DirectLimit.Union][] proves that the union of any ascending chain of
sublattices of a lattice is the direct limit of the inclusions.

The module defines the following, for a sequence `𝑳`{.AgdaBound} of lattices on
setoids and a sequence `θ`{.AgdaBound} of homomorphisms between consecutive
ones:

+  the *transition maps* `push p`{.AgdaFunction} from stage `k` to stage `n`, one
   for each proof `p : k ≤′ n`, as homomorphisms (`push-hom`{.AgdaFunction});
   they compose (`push-push`{.AgdaFunction}) and do not depend on the proof
   (`push-irrelevant`{.AgdaFunction});
+  the limit lattice `DirectLimit 𝑳 θ`{.AgdaFunction}, on the setoid
   `limitSetoid`{.AgdaFunction} of pairs `Staged`{.AgdaFunction} under
   `_≈∞_`{.AgdaFunction}, with the meet `_∧∞_`{.AgdaFunction} and the join
   `_∨∞_`{.AgdaFunction};
+  the canonical homomorphisms `ι∞ k`{.AgdaFunction}, which commute with the
   `θ`{.AgdaBound} (`ι∞-cocone`{.AgdaFunction}), so that their ranges ascend
   (`ι∞-range-ascends`{.AgdaFunction});
+  the universal property: a family of homomorphisms `f k` into a lattice
   `𝑴`{.AgdaBound} that commutes with the `θ`{.AgdaBound}
   (`Cocone`{.AgdaFunction}) extends to a homomorphism from the limit
   (`limit-extend-hom`{.AgdaFunction}) that composes with each `ι∞ k` to
   `f k` (`limit-extend-ι`{.AgdaFunction}), the only such homomorphism up to
   the equality of `𝑴`{.AgdaBound} (`limit-extend-unique`{.AgdaFunction}),
   and an embedding when every `f k` is
   (`limit-extend-embedding`{.AgdaFunction});
+  for a sequence of embeddings: every transition map is an embedding
   (`push-embedding`{.AgdaFunction}); two pairs equal in the limit have equal
   images at *every* common later stage (`≈∞-everywhere`{.AgdaFunction}), so
   that equality in the limit is equality at the stage `k ⊔ m`
   (`≈∞⇔⊔`{.AgdaFunction}); every canonical map is an embedding
   (`ι∞-embedding`{.AgdaFunction}) that reflects the transition maps
   (`ι∞-reflects`{.AgdaFunction}); and the ranges of the canonical maps
   ascend strictly wherever `θ k` is not onto (`ι∞-range-step`{.AgdaFunction}).

The direct limit exists for algebras of any signature with finitary operations,
by the same construction; this module states it for the lattices of this
library, algebras over the lattice signature on a setoid, which is the case
it is needed for.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.DirectLimit where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Nat.Base                          using ( ℕ ; suc ; _⊔_ ; _≤′_ ; ≤′-reflexive
                                                         ; ≤′-step ; ≤′-refl )
open import Data.Nat.Properties                    using ( ≤′-trans ; ≤⇒≤′ ; ≤′⇒≤ ; m≤m⊔n
                                                         ; m≤n⊔m ; ⊔-lub ; ≡-irrelevant ; 1+n≰n )
open import Data.Product                           using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level ) renaming ( _⊔_ to _⊔ˡ_ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
                                                   renaming ( cong to ≡-cong ; sym to ≡-sym
                                                            ; trans to ≡-trans )
open import Relation.Unary                         using ( _∈_ ; _⊆_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret      using ( interp-cong )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op ; setoidEqsToLattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsInjective ; IsInRange )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map ; IsHom )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )

open import Lattices.Semidistributive           using ( hom-preserves-∧ ; hom-preserves-∨ )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ β ρᵇ : Level
```
-->

#### Stages and inequalities

Stages are indexed by `ℕ`.  A transition from stage `k` to stage `n` is indexed
by a proof of `k ≤′ n`, the form of `k ≤ n` whose proofs are built up one step
at a time from `k`, which is the order in which the maps `θ`{.AgdaBound} compose.
Two proofs of `k ≤′ n` are equal (`≤′-irrelevant`{.AgdaFunction}): the
standard library's `≤′` carries an equation `k ≡ n` in its reflexive case, and
equations between natural numbers are unique since equality of natural numbers
is decidable.  The three inequalities about `_⊔_` that the construction uses
are `≤′-⊔ˡ`{.AgdaFunction}, `≤′-⊔ʳ`{.AgdaFunction} and
`⊔-lub′`{.AgdaFunction}.

```agda
-- Two proofs of m ≤′ n are equal.
≤′-irrelevant : {m n : ℕ} (p q : m ≤′ n) → p ≡ q
≤′-irrelevant (≤′-reflexive e) (≤′-reflexive e′)  = ≡-cong ≤′-reflexive (≡-irrelevant e e′)
≤′-irrelevant (≤′-reflexive refl) (≤′-step q)     = ⊥-elim (1+n≰n (≤′⇒≤ q))
≤′-irrelevant (≤′-step p) (≤′-reflexive refl)     = ⊥-elim (1+n≰n (≤′⇒≤ p))
≤′-irrelevant (≤′-step p) (≤′-step q)             = ≡-cong ≤′-step (≤′-irrelevant p q)

-- Each of k and m is at most k ⊔ m, and k ⊔ m is the least such.
≤′-⊔ˡ : (k m : ℕ) → k ≤′ k ⊔ m
≤′-⊔ˡ k m = ≤⇒≤′ (m≤m⊔n k m)

≤′-⊔ʳ : (k m : ℕ) → m ≤′ k ⊔ m
≤′-⊔ʳ k m = ≤⇒≤′ (m≤n⊔m k m)

⊔-lub′ : {k m n : ℕ} → k ≤′ n → m ≤′ n → k ⊔ m ≤′ n
⊔-lub′ p q = ≤⇒≤′ (⊔-lub (≤′⇒≤ p) (≤′⇒≤ q))
```

#### The transition maps

Fix a sequence `𝑳`{.AgdaBound} of lattices, all at the same universe levels, and
homomorphisms `θ k` from each stage to the next.  The transition map
`push p`{.AgdaFunction} for `p : k ≤′ n` is the composite of the `θ`{.AgdaBound}
from stage `k` up to stage `n`, by recursion on `p`: the identity at `k ≤′ k`,
and one more `θ`{.AgdaBound} at each step.  It respects equality and the
operations, by induction on `p`, so it is a homomorphism
(`push-hom`{.AgdaFunction}).  Composites compose along
`≤′-trans`{.AgdaFunction}, by induction on the second proof
(`push-trans`{.AgdaFunction}), and since the proofs of an inequality are equal,
the transition map from `k` to `n` is one map whatever the route
(`push-irrelevant`{.AgdaFunction}, `push-push`{.AgdaFunction}).

The elements, the equality and the operations of stage `n` are written
`Stage n`{.AgdaFunction}, `_≈ₛ_`{.AgdaFunction}, `_∧ₛ_`{.AgdaFunction} and
`_∨ₛ_`{.AgdaFunction}, with the stage implicit in the last three.

```agda
module _ (𝑳 : ℕ → Lattice α ρ) (θ : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ (𝑳 (suc k)))) where

  private variable k m j n N : ℕ

  -- The elements of stage n.
  Stage : ℕ → Type α
  Stage n = 𝕌[ proj₁ (𝑳 n) ]

  infix  4 _≈ₛ_
  infixl 7 _∧ₛ_ _∨ₛ_

  -- The equality, the meet and the join of stage n.
  _≈ₛ_ : Stage n → Stage n → Type ρ
  _≈ₛ_ {n} = Setoid._≈_ 𝔻[ proj₁ (𝑳 n) ]

  _∧ₛ_ _∨ₛ_ : Stage n → Stage n → Stage n
  _∧ₛ_ {n} = Lattice-Op._∧_ (𝑳 n)
  _∨ₛ_ {n} = Lattice-Op._∨_ (𝑳 n)

  private
    ≈ₛ-refl : {x : Stage n} → x ≈ₛ x
    ≈ₛ-refl {n} = Setoid.refl 𝔻[ proj₁ (𝑳 n) ]

    ≈ₛ-reflexive : {x y : Stage n} → x ≡ y → x ≈ₛ y
    ≈ₛ-reflexive {n} = Setoid.reflexive 𝔻[ proj₁ (𝑳 n) ]

    ≈ₛ-sym : {x y : Stage n} → x ≈ₛ y → y ≈ₛ x
    ≈ₛ-sym {n} = Setoid.sym 𝔻[ proj₁ (𝑳 n) ]

    ≈ₛ-trans : {x y z : Stage n} → x ≈ₛ y → y ≈ₛ z → x ≈ₛ z
    ≈ₛ-trans {n} = Setoid.trans 𝔻[ proj₁ (𝑳 n) ]

    ∧ₛ-cong : {x y u v : Stage n} → x ≈ₛ y → u ≈ₛ v → x ∧ₛ u ≈ₛ y ∧ₛ v
    ∧ₛ-cong {n} = Lattice-Op.∧-cong (𝑳 n)

    ∨ₛ-cong : {x y u v : Stage n} → x ≈ₛ y → u ≈ₛ v → x ∨ₛ u ≈ₛ y ∨ₛ v
    ∨ₛ-cong {n} = Lattice-Op.∨-cong (𝑳 n)

  -- The transition map from stage k to stage n, the composite of the θ between them.
  push : k ≤′ n → Stage k → Stage n
  push ≤′-refl          x = x
  push (≤′-step {n} p)  x = proj₁ (θ n) ⟨$⟩ push p x

  -- A transition map respects equality.
  push-cong : (p : k ≤′ n) {x y : Stage k} → x ≈ₛ y → push p x ≈ₛ push p y
  push-cong ≤′-refl          e = e
  push-cong (≤′-step {n} p)  e = cong (proj₁ (θ n)) (push-cong p e)

  -- A transition map as a setoid map.
  push-func : k ≤′ n → Func 𝔻[ proj₁ (𝑳 k) ] 𝔻[ proj₁ (𝑳 n) ]
  push-func p = record { to = push p ; cong = push-cong p }

  -- A transition map commutes with the operations, since each θ does.
  push-compatible : (p : k ≤′ n) → compatible-map (proj₁ (𝑳 k)) (proj₁ (𝑳 n)) (push-func p)
  push-compatible ≤′-refl          = ≈ₛ-refl
  push-compatible (≤′-step {n} p)  =
    ≈ₛ-trans (cong (proj₁ (θ n)) (push-compatible p)) (IsHom.compatible (proj₂ (θ n)))

  -- A transition map is a homomorphism.
  push-hom : k ≤′ n → hom (proj₁ (𝑳 k)) (proj₁ (𝑳 n))
  push-hom {k = k} {n = n} p = mkhom (proj₁ (𝑳 k)) (proj₁ (𝑳 n)) (push-func p) (push-compatible p)

  -- A transition map preserves meets and joins.
  push-∧ : (p : k ≤′ n) (x y : Stage k) → push p (x ∧ₛ y) ≈ₛ push p x ∧ₛ push p y
  push-∧ {k = k} {n = n} p = hom-preserves-∧ (𝑳 k) (𝑳 n) (push-hom p)

  push-∨ : (p : k ≤′ n) (x y : Stage k) → push p (x ∨ₛ y) ≈ₛ push p x ∨ₛ push p y
  push-∨ {k = k} {n = n} p = hom-preserves-∨ (𝑳 k) (𝑳 n) (push-hom p)

  -- Transition maps compose along ≤′-trans.
  push-trans : (p : k ≤′ m) (q : m ≤′ n) (x : Stage k) → push q (push p x) ≡ push (≤′-trans p q) x
  push-trans p ≤′-refl          x = refl
  push-trans p (≤′-step {n} q)  x = ≡-cong (proj₁ (θ n) ⟨$⟩_) (push-trans p q x)

  -- The transition map from k to n does not depend on the proof of k ≤′ n.
  push-irrelevant : (p q : k ≤′ n) (x : Stage k) → push p x ≡ push q x
  push-irrelevant p q x = ≡-cong (λ r → push r x) (≤′-irrelevant p q)

  -- Transition maps compose: going from k to m and then to n is going from k to n.
  push-push : (p : k ≤′ m) (q : m ≤′ n) (r : k ≤′ n) (x : Stage k) → push q (push p x) ≡ push r x
  push-push p q r x = ≡-trans (push-trans p q x) (push-irrelevant (≤′-trans p q) r x)
```

#### The limit setoid

An element of the limit is a pair `(k , x)` with `x` in stage `k`
(`Staged`{.AgdaFunction}).  The pair `(k , x)` *is* `u` at stage `n`
(`At n (k , x) u`{.AgdaFunction}) when `k ≤′ n` and the transition map carries
`x` to `u`.  Since the transition map does not depend on the proof, a pair is
at most one element of each later stage, up to equality
(`at-unique`{.AgdaFunction}), and what it is at stage `n` it carries to every
later stage (`at-up`{.AgdaFunction}).  Two pairs are equal in the limit
(`_≈∞_`{.AgdaFunction}) when they are the same element at some common later
stage, and an equation in the limit holds at every stage above the one where
it is witnessed (`≈∞-above`{.AgdaFunction}).  So the relation is an
equivalence: reflexive at the pair's own stage, symmetric by swapping, and
transitive by going to the larger of the two stages at which the two equations
hold, where the middle pair is one element.  No hypothesis on the
`θ`{.AgdaBound} is needed.

```agda
  -- An element of the limit: an element of some stage, with its stage.
  Staged : Type α
  Staged = Σ[ k ∈ ℕ ] Stage k

  -- (k , x) is u at stage n: some transition map from k to n carries x to u.
  At : (n : ℕ) → Staged → Stage n → Type ρ
  At n (k , x) u = Σ[ p ∈ k ≤′ n ] push p x ≈ₛ u

  -- Two elements of the limit are equal when their images at some common later stage are.
  infix 4 _≈∞_

  _≈∞_ : Staged → Staged → Type ρ
  (k , x) ≈∞ (m , y) = Σ[ n ∈ ℕ ] Σ[ p ∈ k ≤′ n ] Σ[ q ∈ m ≤′ n ] push p x ≈ₛ push q y

  private variable
    a b c a′ b′ : Staged
    u v : Stage n

  -- Every transition map gives a pair's value at a later stage.
  at-push : (p : k ≤′ n) (x : Stage k) → At n (k , x) (push p x)
  at-push p x = p , ≈ₛ-refl

  -- A pair is at most one element of each stage.
  at-unique : At n a u → At n a v → u ≈ₛ v
  at-unique {a = k , x} (p , e) (q , e′) =
    ≈ₛ-trans (≈ₛ-sym e) (≈ₛ-trans (≈ₛ-reflexive (push-irrelevant p q x)) e′)

  -- What a pair is at a stage it is at every later stage, carried there.
  at-up : At n a u → (s : n ≤′ N) → At N a (push s u)
  at-up {a = k , x} (p , e) s =
    ≤′-trans p s , ≈ₛ-trans (≈ₛ-reflexive (≡-sym (push-trans p s x))) (push-cong s e)

  -- Two pairs that are equal elements of one stage are equal in the limit.
  ≈∞-intro : At n a u → At n b v → u ≈ₛ v → a ≈∞ b
  ≈∞-intro {n = n} (p , e) (q , e′) uv = n , p , q , ≈ₛ-trans e (≈ₛ-trans uv (≈ₛ-sym e′))

  -- The stage at which an equation of the limit is witnessed.
  witness-stage : a ≈∞ b → ℕ
  witness-stage w = proj₁ w

  -- An equation of the limit holds at every stage above its witness.
  ≈∞-above : (w : a ≈∞ b) → witness-stage w ≤′ N → At N a u → At N b v → u ≈ₛ v
  ≈∞-above {a = k , x} {b = m , y} (n , p , q , e) s A B =
    ≈ₛ-trans (at-unique A (at-up (at-push p x) s))
             (≈ₛ-trans (push-cong s e) (at-unique (at-up (at-push q y) s) B))

  ≈∞-refl : a ≈∞ a
  ≈∞-refl {a = k , x} = k , ≤′-refl , ≤′-refl , ≈ₛ-refl

  ≈∞-sym : a ≈∞ b → b ≈∞ a
  ≈∞-sym (n , p , q , e) = n , q , p , ≈ₛ-sym e

  ≈∞-trans : a ≈∞ b → b ≈∞ c → a ≈∞ c
  ≈∞-trans {a = k , x} {b = m , y} {c = j , z} w₁@(n₁ , p₁ , q₁ , _) w₂@(n₂ , p₂ , q₂ , _) =
    ≈∞-intro A C (≈ₛ-trans (≈∞-above w₁ s₁ A B) (≈∞-above w₂ s₂ B C))
    where
    s₁ : n₁ ≤′ n₁ ⊔ n₂
    s₁ = ≤′-⊔ˡ n₁ n₂

    s₂ : n₂ ≤′ n₁ ⊔ n₂
    s₂ = ≤′-⊔ʳ n₁ n₂

    A : At (n₁ ⊔ n₂) (k , x) (push s₁ (push p₁ x))
    A = at-up (at-push p₁ x) s₁

    B : At (n₁ ⊔ n₂) (m , y) (push s₁ (push q₁ y))
    B = at-up (at-push q₁ y) s₁

    C : At (n₁ ⊔ n₂) (j , z) (push s₂ (push q₂ z))
    C = at-up (at-push q₂ z) s₂

  -- The setoid of the limit.
  limitSetoid : Setoid α ρ
  limitSetoid = record
    { Carrier        = Staged
    ; _≈_            = _≈∞_
    ; isEquivalence  = record { refl = ≈∞-refl ; sym = ≈∞-sym ; trans = ≈∞-trans }
    }
```

#### The limit lattice

The meet of `(k , x)` and `(m , y)` is the meet of their images at stage
`k ⊔ m`, and the join likewise.  What the meet of two pairs is at a stage is
the meet of what they are there (`at-∧`{.AgdaFunction}), since the transition
maps preserve meets and compose; and the join likewise
(`at-∨`{.AgdaFunction}).  So each lattice law holds in the limit because it
holds at a stage above all its variables, among the elements they are there;
and the operations respect the equality of the limit because, at a stage above
both witnesses, equal pairs are the same elements.

```agda
  infixl 7 _∧∞_ _∨∞_

  -- Meet and join in the limit, computed at the larger stage.
  _∧∞_ _∨∞_ : Staged → Staged → Staged
  (k , x) ∧∞ (m , y) = k ⊔ m , push (≤′-⊔ˡ k m) x ∧ₛ push (≤′-⊔ʳ k m) y
  (k , x) ∨∞ (m , y) = k ⊔ m , push (≤′-⊔ˡ k m) x ∨ₛ push (≤′-⊔ʳ k m) y

  -- What a meet of pairs is at a stage is the meet of what they are there.
  at-∧ : At n a u → At n b v → At n (a ∧∞ b) (u ∧ₛ v)
  at-∧ {n = n} {a = k , x} {u = u} {b = m , y} {v = v} (p , e) (q , e′) =
    r , ≈ₛ-trans (push-∧ r (push (≤′-⊔ˡ k m) x) (push (≤′-⊔ʳ k m) y)) (∧ₛ-cong ex ey)
    where
    r : k ⊔ m ≤′ n
    r = ⊔-lub′ p q

    ex : push r (push (≤′-⊔ˡ k m) x) ≈ₛ u
    ex = ≈ₛ-trans (≈ₛ-reflexive (push-push (≤′-⊔ˡ k m) r p x)) e

    ey : push r (push (≤′-⊔ʳ k m) y) ≈ₛ v
    ey = ≈ₛ-trans (≈ₛ-reflexive (push-push (≤′-⊔ʳ k m) r q y)) e′

  -- What a join of pairs is at a stage is the join of what they are there.
  at-∨ : At n a u → At n b v → At n (a ∨∞ b) (u ∨ₛ v)
  at-∨ {n = n} {a = k , x} {u = u} {b = m , y} {v = v} (p , e) (q , e′) =
    r , ≈ₛ-trans (push-∨ r (push (≤′-⊔ˡ k m) x) (push (≤′-⊔ʳ k m) y)) (∨ₛ-cong ex ey)
    where
    r : k ⊔ m ≤′ n
    r = ⊔-lub′ p q

    ex : push r (push (≤′-⊔ˡ k m) x) ≈ₛ u
    ex = ≈ₛ-trans (≈ₛ-reflexive (push-push (≤′-⊔ˡ k m) r p x)) e

    ey : push r (push (≤′-⊔ʳ k m) y) ≈ₛ v
    ey = ≈ₛ-trans (≈ₛ-reflexive (push-push (≤′-⊔ʳ k m) r q y)) e′
```

The congruences go to the larger of the two witnesses' stages; the laws in one
or two variables to the larger of their stages, and the associative laws to the
largest of three.  The names `here`{.AgdaFunction}, `atˡ`{.AgdaFunction},
`atʳ`{.AgdaFunction} and `at₁`{.AgdaFunction} to `at₃`{.AgdaFunction} give
each variable at that stage, and `setoidEqsToLattice`{.AgdaFunction} of
[Classical.Structures.Lattice.Basic][] packages the laws as the lattice
`DirectLimit 𝑳 θ`{.AgdaFunction}.

```agda
  private
    -- A pair at its own stage.
    here : (k : ℕ) (x : Stage k) → At k (k , x) x
    here k x = at-push ≤′-refl x

    -- Two pairs at the larger of their stages.
    atˡ : (k m : ℕ) (x : Stage k) → At (k ⊔ m) (k , x) (push (≤′-⊔ˡ k m) x)
    atˡ k m x = at-push (≤′-⊔ˡ k m) x

    atʳ : (k m : ℕ) (y : Stage m) → At (k ⊔ m) (m , y) (push (≤′-⊔ʳ k m) y)
    atʳ k m y = at-push (≤′-⊔ʳ k m) y

    -- Three pairs at the largest of their stages.
    at₁ : (k m j : ℕ) (x : Stage k)
      → At (k ⊔ m ⊔ j) (k , x) (push (≤′-trans (≤′-⊔ˡ k m) (≤′-⊔ˡ (k ⊔ m) j)) x)
    at₁ k m j x = at-push (≤′-trans (≤′-⊔ˡ k m) (≤′-⊔ˡ (k ⊔ m) j)) x

    at₂ : (k m j : ℕ) (y : Stage m)
      → At (k ⊔ m ⊔ j) (m , y) (push (≤′-trans (≤′-⊔ʳ k m) (≤′-⊔ˡ (k ⊔ m) j)) y)
    at₂ k m j y = at-push (≤′-trans (≤′-⊔ʳ k m) (≤′-⊔ˡ (k ⊔ m) j)) y

    at₃ : (k m j : ℕ) (z : Stage j) → At (k ⊔ m ⊔ j) (j , z) (push (≤′-⊔ʳ (k ⊔ m) j) z)
    at₃ k m j z = at-push (≤′-⊔ʳ (k ⊔ m) j) z

  -- The operations respect the equality of the limit.
  ∧∞-cong : a ≈∞ a′ → b ≈∞ b′ → a ∧∞ b ≈∞ a′ ∧∞ b′
  ∧∞-cong {a = k , x} {a′ = k′ , x′} {b = m , y} {b′ = m′ , y′}
          (n₁ , p₁ , q₁ , e₁) (n₂ , p₂ , q₂ , e₂) =
    ≈∞-intro (at-∧ (at-up (at-push p₁ x) s₁) (at-up (at-push p₂ y) s₂))
             (at-∧ (at-up (at-push q₁ x′) s₁) (at-up (at-push q₂ y′) s₂))
             (∧ₛ-cong (push-cong s₁ e₁) (push-cong s₂ e₂))
    where
    s₁ : n₁ ≤′ n₁ ⊔ n₂
    s₁ = ≤′-⊔ˡ n₁ n₂

    s₂ : n₂ ≤′ n₁ ⊔ n₂
    s₂ = ≤′-⊔ʳ n₁ n₂

  ∨∞-cong : a ≈∞ a′ → b ≈∞ b′ → a ∨∞ b ≈∞ a′ ∨∞ b′
  ∨∞-cong {a = k , x} {a′ = k′ , x′} {b = m , y} {b′ = m′ , y′}
          (n₁ , p₁ , q₁ , e₁) (n₂ , p₂ , q₂ , e₂) =
    ≈∞-intro (at-∨ (at-up (at-push p₁ x) s₁) (at-up (at-push p₂ y) s₂))
             (at-∨ (at-up (at-push q₁ x′) s₁) (at-up (at-push q₂ y′) s₂))
             (∨ₛ-cong (push-cong s₁ e₁) (push-cong s₂ e₂))
    where
    s₁ : n₁ ≤′ n₁ ⊔ n₂
    s₁ = ≤′-⊔ˡ n₁ n₂

    s₂ : n₂ ≤′ n₁ ⊔ n₂
    s₂ = ≤′-⊔ʳ n₁ n₂

  -- The laws in one and two variables, at the larger stage.
  ∧∞-comm : a ∧∞ b ≈∞ b ∧∞ a
  ∧∞-comm {a = k , x} {b = m , y} =
    ≈∞-intro (at-∧ (atˡ k m x) (atʳ k m y)) (at-∧ (atʳ k m y) (atˡ k m x))
             (Lattice-Op.∧-comm-law (𝑳 (k ⊔ m)))

  ∨∞-comm : a ∨∞ b ≈∞ b ∨∞ a
  ∨∞-comm {a = k , x} {b = m , y} =
    ≈∞-intro (at-∨ (atˡ k m x) (atʳ k m y)) (at-∨ (atʳ k m y) (atˡ k m x))
             (Lattice-Op.∨-comm-law (𝑳 (k ⊔ m)))

  ∧∞-idem : a ∧∞ a ≈∞ a
  ∧∞-idem {a = k , x} = ≈∞-intro (at-∧ (here k x) (here k x)) (here k x) (Lattice-Op.∧-idem-law (𝑳 k))

  ∨∞-idem : a ∨∞ a ≈∞ a
  ∨∞-idem {a = k , x} = ≈∞-intro (at-∨ (here k x) (here k x)) (here k x) (Lattice-Op.∨-idem-law (𝑳 k))

  ∧∞-absorbs-∨∞ : a ∧∞ (a ∨∞ b) ≈∞ a
  ∧∞-absorbs-∨∞ {a = k , x} {b = m , y} =
    ≈∞-intro (at-∧ (atˡ k m x) (at-∨ (atˡ k m x) (atʳ k m y))) (atˡ k m x)
             (Lattice-Op.absorbˡ-law (𝑳 (k ⊔ m)))

  ∨∞-absorbs-∧∞ : (a ∧∞ b) ∨∞ a ≈∞ a
  ∨∞-absorbs-∧∞ {a = k , x} {b = m , y} =
    ≈∞-intro (at-∨ (at-∧ (atˡ k m x) (atʳ k m y)) (atˡ k m x)) (atˡ k m x)
             (Lattice-Op.absorbʳ-law (𝑳 (k ⊔ m)))

  -- The associative laws, at the largest of three stages.
  ∧∞-assoc : (a ∧∞ b) ∧∞ c ≈∞ a ∧∞ (b ∧∞ c)
  ∧∞-assoc {a = k , x} {b = m , y} {c = j , z} =
    ≈∞-intro (at-∧ (at-∧ (at₁ k m j x) (at₂ k m j y)) (at₃ k m j z))
             (at-∧ (at₁ k m j x) (at-∧ (at₂ k m j y) (at₃ k m j z)))
             (Lattice-Op.∧-assoc-law (𝑳 (k ⊔ m ⊔ j)))

  ∨∞-assoc : (a ∨∞ b) ∨∞ c ≈∞ a ∨∞ (b ∨∞ c)
  ∨∞-assoc {a = k , x} {b = m , y} {c = j , z} =
    ≈∞-intro (at-∨ (at-∨ (at₁ k m j x) (at₂ k m j y)) (at₃ k m j z))
             (at-∨ (at₁ k m j x) (at-∨ (at₂ k m j y) (at₃ k m j z)))
             (Lattice-Op.∨-assoc-law (𝑳 (k ⊔ m ⊔ j)))

  -- The direct limit of the sequence.
  DirectLimit : Lattice α ρ
  DirectLimit = setoidEqsToLattice limitSetoid _∧∞_ _∨∞_ ∧∞-cong ∨∞-cong
    (λ {a} {b} {c} → ∧∞-assoc {a = a} {b = b} {c = c}) (λ {a} {b} → ∧∞-comm {a = a} {b = b})
    ∧∞-idem
    (λ {a} {b} {c} → ∨∞-assoc {a = a} {b = b} {c = c}) (λ {a} {b} → ∨∞-comm {a = a} {b = b})
    ∨∞-idem ∧∞-absorbs-∨∞ ∨∞-absorbs-∧∞
```

#### The canonical maps

The canonical map `ι∞ k`{.AgdaFunction} sends `x` to the pair `(k , x)`.  It
respects equality, read at stage `k` itself, and it commutes with the
operations, since the meet of `(k , x)` and `(k , y)` is, at stage `k`, the meet
of `x` and `y`.

```agda
  -- The canonical map from stage k into the limit, as a setoid map.
  ι∞-func : (k : ℕ) → Func 𝔻[ proj₁ (𝑳 k) ] limitSetoid
  ι∞-func k = record { to = k ,_ ; cong = λ e → k , ≤′-refl , ≤′-refl , e }

  -- The canonical map commutes with the operations.
  ι∞-compatible : (k : ℕ) → compatible-map (proj₁ (𝑳 k)) (proj₁ DirectLimit) (ι∞-func k)
  ι∞-compatible k {∧-Op} {t} =
    ≈∞-intro (here k _) (at-∧ (here k (t 0F)) (here k (t 1F)))
             (interp-cong (proj₁ (𝑳 k)) ∧-Op λ { 0F → ≈ₛ-refl ; 1F → ≈ₛ-refl })
  ι∞-compatible k {∨-Op} {t} =
    ≈∞-intro (here k _) (at-∨ (here k (t 0F)) (here k (t 1F)))
             (interp-cong (proj₁ (𝑳 k)) ∨-Op λ { 0F → ≈ₛ-refl ; 1F → ≈ₛ-refl })

  -- The canonical homomorphism from stage k into the limit.
  ι∞ : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ DirectLimit)
  ι∞ k = mkhom (proj₁ (𝑳 k)) (proj₁ DirectLimit) (ι∞-func k) (ι∞-compatible k)
```

#### The universal property

A family of homomorphisms `f k` from the stages into a lattice
`𝑴`{.AgdaBound} is a *cocone* over the sequence (`Cocone`{.AgdaFunction}) when
`f (suc k) ∘ θ k` equals `f k` for every `k`; the classical name for such a
family is a *compatible* family, a word that agda-algebras already uses for a
map that commutes with the operations.  The canonical maps form a cocone into
the limit (`ι∞-cocone`{.AgdaFunction}), since `(suc k , θ k x)` and `(k , x)`
are the same element of stage `suc k`; so the range of each lies in the range
of the next (`ι∞-range-ascends`{.AgdaFunction}).

A cocone commutes with every transition map (`cocone-push`{.AgdaFunction}), by
induction on the transition, and so it extends to the limit:
`limit-extend`{.AgdaFunction} sends `(k , x)` to `f k x`, well defined because
two pairs equal at stage `n` have, under `f n`, the images that `f k` and
`f m` give them.  It is a homomorphism (`limit-extend-hom`{.AgdaFunction}),
since the meet of two pairs is a meet at the larger stage, where `f` preserves
it (`limit-extend-∧`{.AgdaFunction}); it composes with each `ι∞ k` to `f k`,
definitionally (`limit-extend-ι`{.AgdaFunction}); and every homomorphism with
that property agrees with it (`limit-extend-unique`{.AgdaFunction}), since
every element of the limit is `ι∞ k x` for some `k` and `x`.  When every
`f k` is injective, so is the extension
(`limit-extend-injective`{.AgdaFunction}): if `f k x` equals `f m y`, then
`f (k ⊔ m)` gives the images of `x` and `y` at stage `k ⊔ m` equal values, so
the images are equal.  None of this needs a
hypothesis on the `θ`{.AgdaBound}.

```agda
  module _ (𝑴 : Lattice β ρᵇ) where
    open Setoid 𝔻[ proj₁ 𝑴 ]  using ( _≈_ ) renaming ( refl to ≈ᴹ-refl ; sym to ≈ᴹ-sym
                                                     ; trans to ≈ᴹ-trans )
    open Lattice-Op 𝑴         using () renaming ( _∧_ to _∧ᴹ_ ; _∨_ to _∨ᴹ_
                                                ; ∧-cong to ∧ᴹ-cong ; ∨-cong to ∨ᴹ-cong )

    -- A family of homomorphisms from the stages that commutes with θ.
    Cocone : ((k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ 𝑴)) → Type (α ⊔ˡ ρᵇ)
    Cocone f = (k : ℕ) (x : Stage k) → proj₁ (f (suc k)) ⟨$⟩ (proj₁ (θ k) ⟨$⟩ x) ≈ proj₁ (f k) ⟨$⟩ x

    module _ (f : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ 𝑴)) (cocone : Cocone f) where

      -- A cocone commutes with every transition map.
      cocone-push : (p : k ≤′ n) (x : Stage k) → proj₁ (f n) ⟨$⟩ push p x ≈ proj₁ (f k) ⟨$⟩ x
      cocone-push ≤′-refl          x = ≈ᴹ-refl
      cocone-push (≤′-step {n} p)  x = ≈ᴹ-trans (cocone n (push p x)) (cocone-push p x)

      private
        extend-cong : a ≈∞ b → proj₁ (f (proj₁ a)) ⟨$⟩ proj₂ a ≈ proj₁ (f (proj₁ b)) ⟨$⟩ proj₂ b
        extend-cong {a = k , x} {b = m , y} (n , p , q , e) =
          ≈ᴹ-trans (≈ᴹ-sym (cocone-push p x)) (≈ᴹ-trans (cong (proj₁ (f n)) e) (cocone-push q y))

      -- The extension of a cocone to the limit, as a setoid map.
      limit-extend : Func limitSetoid 𝔻[ proj₁ 𝑴 ]
      limit-extend = record { to = λ a → proj₁ (f (proj₁ a)) ⟨$⟩ proj₂ a ; cong = extend-cong }

      -- The extension preserves meets and joins.
      limit-extend-∧ : (a b : Staged) → limit-extend ⟨$⟩ (a ∧∞ b) ≈ limit-extend ⟨$⟩ a ∧ᴹ limit-extend ⟨$⟩ b
      limit-extend-∧ (k , x) (m , y) =
        ≈ᴹ-trans (hom-preserves-∧ (𝑳 (k ⊔ m)) 𝑴 (f (k ⊔ m)) (push (≤′-⊔ˡ k m) x) (push (≤′-⊔ʳ k m) y))
                 (∧ᴹ-cong (cocone-push (≤′-⊔ˡ k m) x) (cocone-push (≤′-⊔ʳ k m) y))

      limit-extend-∨ : (a b : Staged) → limit-extend ⟨$⟩ (a ∨∞ b) ≈ limit-extend ⟨$⟩ a ∨ᴹ limit-extend ⟨$⟩ b
      limit-extend-∨ (k , x) (m , y) =
        ≈ᴹ-trans (hom-preserves-∨ (𝑳 (k ⊔ m)) 𝑴 (f (k ⊔ m)) (push (≤′-⊔ˡ k m) x) (push (≤′-⊔ʳ k m) y))
                 (∨ᴹ-cong (cocone-push (≤′-⊔ˡ k m) x) (cocone-push (≤′-⊔ʳ k m) y))

      -- The extension commutes with the operations.
      limit-extend-compatible : compatible-map (proj₁ DirectLimit) (proj₁ 𝑴) limit-extend
      limit-extend-compatible {∧-Op} {t} = ≈ᴹ-trans (limit-extend-∧ (t 0F) (t 1F))
        (interp-cong (proj₁ 𝑴) ∧-Op λ { 0F → ≈ᴹ-refl ; 1F → ≈ᴹ-refl })
      limit-extend-compatible {∨-Op} {t} = ≈ᴹ-trans (limit-extend-∨ (t 0F) (t 1F))
        (interp-cong (proj₁ 𝑴) ∨-Op λ { 0F → ≈ᴹ-refl ; 1F → ≈ᴹ-refl })

      -- The extension of a cocone to the limit, a homomorphism.
      limit-extend-hom : hom (proj₁ DirectLimit) (proj₁ 𝑴)
      limit-extend-hom = mkhom (proj₁ DirectLimit) (proj₁ 𝑴) limit-extend limit-extend-compatible

      -- The extension composes with each canonical map to the map of the cocone.
      limit-extend-ι : (k : ℕ) (x : Stage k) → limit-extend ⟨$⟩ (proj₁ (ι∞ k) ⟨$⟩ x) ≈ proj₁ (f k) ⟨$⟩ x
      limit-extend-ι k x = ≈ᴹ-refl

      -- It is the only homomorphism that does, up to the equality of 𝑴.
      limit-extend-unique : (g : hom (proj₁ DirectLimit) (proj₁ 𝑴))
        → ((k : ℕ) (x : Stage k) → proj₁ g ⟨$⟩ (proj₁ (ι∞ k) ⟨$⟩ x) ≈ proj₁ (f k) ⟨$⟩ x)
        → (a : Staged) → proj₁ g ⟨$⟩ a ≈ limit-extend ⟨$⟩ a
      limit-extend-unique g gι (k , x) = gι k x

      -- The extension of a cocone of injective maps is injective.
      limit-extend-injective : ((k : ℕ) → IsInjective (proj₁ (f k))) → IsInjective limit-extend
      limit-extend-injective inj {k , x} {m , y} e =
        k ⊔ m , ≤′-⊔ˡ k m , ≤′-⊔ʳ k m
        , inj (k ⊔ m) (≈ᴹ-trans (cocone-push (≤′-⊔ˡ k m) x) (≈ᴹ-trans e (≈ᴹ-sym (cocone-push (≤′-⊔ʳ k m) y))))

      -- The extension of a cocone of embeddings is an embedding.
      limit-extend-embedding : ((k : ℕ) → IsInjective (proj₁ (f k)))
        → proj₁ DirectLimit IsSubalgebraOf proj₁ 𝑴
      limit-extend-embedding inj = limit-extend-hom , limit-extend-injective inj

  -- The canonical maps form a cocone into the limit.
  ι∞-cocone : Cocone DirectLimit ι∞
  ι∞-cocone k x = suc k , ≤′-refl , ≤′-step ≤′-refl , ≈ₛ-refl

  -- The range of each canonical map lies in the range of the next.
  ι∞-range-ascends : (k : ℕ) → IsInRange (proj₁ (ι∞ k)) ⊆ IsInRange (proj₁ (ι∞ (suc k)))
  ι∞-range-ascends k (x , e) = proj₁ (θ k) ⟨$⟩ x , ≈∞-trans (ι∞-cocone k x) e
```

#### Sequences of embeddings

When every `θ k` is injective, so is every transition map, by induction
(`push-injective`{.AgdaFunction}), and equality in the limit no longer depends
on the stage at which it is read: two pairs equal in the limit are the same
element at *every* common later stage (`≈∞-everywhere`{.AgdaFunction}), since
they are at a stage above both that one and the witness's, and the transition
map up to it is injective.  In particular, equality in the limit is equality at
the stage `k ⊔ m` (`≈∞⇔⊔`{.AgdaFunction}), so a limit of embeddings of
lattices with decidable equality has decidable equality.  Every canonical map
is injective (`ι∞-injective`{.AgdaFunction}), read at its own stage; and if
`ι∞ k x` equals `ι∞ n y` with `k ≤′ n`, then the transition map carries `x` to
`y` (`ι∞-reflects`{.AgdaFunction}).  At `n = suc k` this says that an element
`w` of stage `suc k` with `ι∞ (suc k) w` in the range of `ι∞ k` is in the
range of `θ k` (`ι∞-range-step`{.AgdaFunction}): where `θ k` is not onto, the
range of `ι∞ (suc k)` is strictly larger than that of `ι∞ k`.

```agda
  module _ (θ-injective : (k : ℕ) → IsInjective (proj₁ (θ k))) where

    -- Every transition map of a sequence of embeddings is injective.
    push-injective : (p : k ≤′ n) → IsInjective (push-func p)
    push-injective ≤′-refl          e = e
    push-injective (≤′-step {n} p)  e = push-injective p (θ-injective n e)

    -- Every transition map of a sequence of embeddings is an embedding.
    push-embedding : k ≤′ n → proj₁ (𝑳 k) IsSubalgebraOf proj₁ (𝑳 n)
    push-embedding p = push-hom p , push-injective p

    private
      -- Two pairs equal in the limit are one element at every common later stage.
      ≈∞-at : a ≈∞ b → At n a u → At n b v → u ≈ₛ v
      ≈∞-at {n = n} w A B =
        push-injective s (≈∞-above w (≤′-⊔ʳ n (witness-stage w)) (at-up A s) (at-up B s))
        where
        s : n ≤′ n ⊔ witness-stage w
        s = ≤′-⊔ˡ n (witness-stage w)

    -- Equal pairs have equal images at every common later stage.
    ≈∞-everywhere : {x : Stage k} {y : Stage m} → (k , x) ≈∞ (m , y)
      → (p : k ≤′ n) (q : m ≤′ n) → push p x ≈ₛ push q y
    ≈∞-everywhere {x = x} {y = y} w p q = ≈∞-at w (at-push p x) (at-push q y)

    -- Equality in the limit is equality at the larger stage.
    ≈∞⇔⊔ : {x : Stage k} {y : Stage m}
      → ((k , x) ≈∞ (m , y)) ⇔ (push (≤′-⊔ˡ k m) x ≈ₛ push (≤′-⊔ʳ k m) y)
    ≈∞⇔⊔ {k = k} {m = m} = mk⇔ (λ w → ≈∞-everywhere w (≤′-⊔ˡ k m) (≤′-⊔ʳ k m))
                               (λ e → k ⊔ m , ≤′-⊔ˡ k m , ≤′-⊔ʳ k m , e)

    -- Every canonical map of a sequence of embeddings is injective.
    ι∞-injective : (k : ℕ) → IsInjective (proj₁ (ι∞ k))
    ι∞-injective k w = ≈∞-everywhere w ≤′-refl ≤′-refl

    -- Every canonical map of a sequence of embeddings is an embedding.
    ι∞-embedding : (k : ℕ) → proj₁ (𝑳 k) IsSubalgebraOf proj₁ DirectLimit
    ι∞-embedding k = ι∞ k , ι∞-injective k

    -- If ι∞ k x equals ι∞ n y with k ≤′ n, the transition map carries x to y.
    ι∞-reflects : (p : k ≤′ n) {x : Stage k} {y : Stage n}
      → proj₁ (ι∞ k) ⟨$⟩ x ≈∞ proj₁ (ι∞ n) ⟨$⟩ y → push p x ≈ₛ y
    ι∞-reflects p w = ≈∞-everywhere w p ≤′-refl

    -- An element of stage suc k whose image is in the range of ι∞ k is in the range of θ k.
    ι∞-range-step : (k : ℕ) {w : Stage (suc k)}
      → proj₁ (ι∞ (suc k)) ⟨$⟩ w ∈ IsInRange (proj₁ (ι∞ k)) → w ∈ IsInRange (proj₁ (θ k))
    ι∞-range-step k (x , e) = x , ι∞-reflects (≤′-step ≤′-refl) e
```

--------------------------------------

[Lattices.DirectLimit]: Lattices.DirectLimit.html
[Lattices.DirectLimit.Union]: Lattices.DirectLimit.Union.html
[Classical.Structures.Lattice.Basic]: Classical.Structures.Lattice.Basic.html
[Bergman (2015)]: https://doi.org/10.1007/978-3-319-11478-1
