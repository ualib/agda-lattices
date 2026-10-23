---
layout: default
file: "src/Lattices/Free/Countable.lagda.md"
title: "Lattices.Free.Countable module"
date: "2026-10-17"
author: "William DeMeo"
---

### Theorem 1.28: a countable free generating set in FL(3)

The family `σ`{.AgdaFunction} of [Lattices.Free.WhitmanPolynomials][]
freely generates a copy of `FL(ℕ)` inside `FL(Fin 3)`.  This is Theorem
1.28 of Freese, Ježek, and Nation, *Free Lattices* (1995).  Its finite
restrictions give embeddings of every finite rank into rank three;
composing with a generator inclusion gives embeddings into every rank at
least three.  So a configuration of sublattices that occurs in a free lattice
of countable rank occurs in `FL(3)` too.

The proof first recovers both inequalities between indices from a
comparison of family members.  Whitman's condition then reduces each
finite join or meet comparison to one of these single-member comparisons,
which is exactly Corollary 1.13.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Countable where

open import Agda.Primitive using () renaming ( Set to Type )

open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base using ( Fin ; toℕ ; inject≤ )
open import Data.Fin.Properties using ( toℕ-injective ; inject≤-injective )
open import Data.List.Base using ( [] ; _∷_ ; map )
open import Data.List.Membership.Propositional using ( _∈_ )
open import Data.List.Relation.Unary.Any using ( Any ; here ; there )
open import Data.Nat.Base using ( ℕ ; suc ; _≤_ )
open import Data.Nat.Properties using ( ≤-antisym ; suc-injective )
open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Function.Bundles using ( _↣_ ; Injection )
open import Level using ( Level )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; sym )
open import Relation.Nullary using ( ¬_ )

import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any

open import Lattices.Free.Term using ( ℊ ; _∨̇_ )
open import Lattices.Free.Whitman
  using ( _≤ʷ_ ; ≤ʷ-trans ; ∨≤ ; ≤∧ ; ∨≤-inv ; ≤∧-inv ; ∧≤∨-inv
        ; ℊ≤∨-inv ; ∨̇-upperˡ ; ∨̇-upperʳ ; ∧̇-lowerʳ )
open import Lattices.Free.Canonical.Basic
  using ( ⋁⁺ ; ⋀⁺ ; gen-⋁⁺-prime ; ⋀⁺-gen-below ; W-list )
open import Lattices.Free.Generation
  using ( FreelyGenerates ; JoinCondition ; MeetCondition ; freelyGenerates→injective
        ; freelyGenerates-reindex ; generators-free )
open import Lattices.Free.Substitution using ( Sub ; _⨟_ ; subst-hom ; ⨟-injective )
open import Lattices.Free.Universal using ( FL )
open import Setoid.Functions using ( IsInjective )
open import Setoid.Homomorphisms.Basic using ( hom )
open import Setoid.Subalgebras.Basic using ( _IsSubalgebraOf_ )
open import Lattices.Free.WhitmanPolynomials
  using ( x ; y ; z ; ascending ; descending ; core ; σ ; σ-finite )
open import Lattices.Free.WhitmanChains
  using ( x≤ascending ; descending≤x ; x≰y ; y≰ascending ; x≰descending
        ; x≰w ; y≰w ; core≰z ; core≰x ; core≰y ; w≰z
        ; z≰descending∨y ; ascending-reflects ; joined-descending-reflects )
```

The three applications of Whitman's condition in the antichain argument
are kept separate.  The exclusions are Lemma 1.29 and its elementary
consequences proved in [Lattices.Free.WhitmanChains][].

```agda
-- A comparison of positive members forces a comparison of their cores.
members→cores : ∀ m n → σ m ≤ʷ σ n → core (suc m) ≤ʷ core (suc n)
members→cores m n h =
  [ [ (λ e → ⊥-elim (x≰w n (≤ʷ-trans (x≤ascending (suc m)) e)))
      , (λ e → ⊥-elim (y≰w n (proj₂ (∨≤-inv e)))) ]′
  , [ (λ e → ⊥-elim (core≰z (suc m) e)) , (λ e → e) ]′ ]′
    (∧≤∨-inv (proj₂ (∨≤-inv h)))

-- The first core inequality recovers the ascending-chain comparison.
core→ascending : ∀ m n → core (suc m) ≤ʷ ascending (suc n)
  → ascending (suc m) ≤ʷ ascending (suc n)
core→ascending m n h =
  [ [ (λ e → e) , (λ e → ⊥-elim (y≰ascending n (proj₂ (∨≤-inv e)))) ]′
  , [ (λ e → ⊥-elim (core≰z (suc m) (≤ʷ-trans e ∧̇-lowerʳ)))
      , (λ e → ⊥-elim (core≰x m e)) ]′ ]′ (∧≤∨-inv h)

-- The second core inequality recovers the joined descending comparison.
core→descending : ∀ m n → core (suc m) ≤ʷ descending (suc n) ∨̇ y
  → descending (suc m) ∨̇ y ≤ʷ descending (suc n) ∨̇ y
core→descending m n h =
  [ [ (λ e → ⊥-elim
        ([ x≰descending n , x≰y ]′ (ℊ≤∨-inv (≤ʷ-trans (x≤ascending (suc m)) e))))
      , (λ e → e) ]′
  , [ (λ e → ⊥-elim (core≰x m (≤ʷ-trans e (descending≤x (suc n)))))
      , (λ e → ⊥-elim (core≰y m e)) ]′ ]′ (∧≤∨-inv h)

-- The positive members are an antichain, with equality of indices.
σ-antichain : ∀ m n → σ m ≤ʷ σ n → m ≡ n
σ-antichain m n h = suc-injective (≤-antisym
  (ascending-reflects (suc m) (suc n) (core→ascending m n (proj₁ parts)))
  (joined-descending-reflects (suc m) (suc n) (core→descending m n (proj₂ parts))))
  where
  -- Split the meet on the right after the first application of (W).
  parts : (core (suc m) ≤ʷ ascending (suc n))
    Data.Product.× (core (suc m) ≤ʷ descending (suc n) ∨̇ y)
  parts = ≤∧-inv (members→cores m n h)
```

No join of family members lies above `x` or `y`, because those generators
are join prime.  This eliminates the meetand alternatives in Whitman's
condition for the join half of Corollary 1.13.

```agda
-- Primality excludes x from any nonempty finite join of members.
x≰join : ∀ j js → ¬ (x ≤ʷ ⋁⁺ (σ j) (map σ js))
x≰join j js h = reject (Any.map⁻ {f = σ} {xs = j ∷ js} (gen-⋁⁺-prime h))
  where
  -- Reject the member supplied by primality.
  reject : ∀ {is} → Any (λ i → x ≤ʷ σ i) is → ⊥
  reject {is = i ∷ is} (here e) = x≰w i e
  reject (there e) = reject e

-- The same exclusion for y.
y≰join : ∀ j js → ¬ (y ≤ʷ ⋁⁺ (σ j) (map σ js))
y≰join j js h = reject (Any.map⁻ {f = σ} {xs = j ∷ js} (gen-⋁⁺-prime h))
  where
  -- Reject the member supplied by primality.
  reject : ∀ {is} → Any (λ i → y ≤ʷ σ i) is → ⊥
  reject {is = i ∷ is} (here e) = y≰w i e
  reject (there e) = reject e

-- The join condition of Corollary 1.13 for the countable family.
σ-join-condition : JoinCondition σ
σ-join-condition {i} {[]} ()
σ-join-condition {i} {j ∷ js} h =
  choose (W-list (descending (suc i) ∨̇ y ∷ []) (map σ js)
    (≤ʷ-trans ∨̇-upperʳ h))
  where
  -- A core below a member puts the whole member below it, by adjoining z.
  select : ∀ {is} → Any (λ k → core (suc i) ≤ʷ σ k) is → i ∈ is
  select {is = k ∷ is} (here e) = here (σ-antichain i k (∨≤ ∨̇-upperˡ e))
  select (there e) = there (select e)

  -- The meetand alternatives would put x or y below the join.
  choose : Any (_≤ʷ ⋁⁺ (σ j) (map σ js))
      (ascending (suc i) ∷ (descending (suc i) ∨̇ y) ∷ [])
    ⊎ Any (core (suc i) ≤ʷ_) (map σ (j ∷ js)) → i ∈ j ∷ js
  choose (inj₁ (here e)) = ⊥-elim (x≰join j js (≤ʷ-trans (x≤ascending (suc i)) e))
  choose (inj₁ (there (here e))) = ⊥-elim (y≰join j js (proj₂ (∨≤-inv e)))
  choose (inj₂ e) = select (Any.map⁻ {f = σ} {xs = j ∷ js} e)

-- All members lie above z, so every nonempty meet does too.
z≤meet : ∀ j js → z ≤ʷ ⋀⁺ (σ j) (map σ js)
z≤meet j [] = ∨̇-upperˡ
z≤meet j (k ∷ ks) = ≤∧ ∨̇-upperˡ (z≤meet k ks)

-- Meet primality and w_n ≰ z exclude the lower-bound alternative.
meet≰z : ∀ j js → ¬ (⋀⁺ (σ j) (map σ js) ≤ʷ z)
meet≰z j js h = reject (Any.map⁻ {f = σ} {xs = j ∷ js} (⋀⁺-gen-below h))
  where
  -- Reject the member supplied by meet primality.
  reject : ∀ {is} → Any (λ k → σ k ≤ʷ z) is → ⊥
  reject {is = k ∷ is} (here e) = w≰z (suc k) e
  reject (there e) = reject e

-- The meet condition of Corollary 1.13 for the countable family.
σ-meet-condition : MeetCondition σ
σ-meet-condition {i} {[]} ()
σ-meet-condition {i} {j ∷ js} h =
  choose (W-list (map σ js) (core (suc i) ∷ []) h)
  where
  -- A member below the target has the same index by the antichain theorem.
  select : ∀ {is} → Any (λ k → σ k ≤ʷ σ i) is → i ∈ is
  select {is = k ∷ is} (here e) = here (sym (σ-antichain k i e))
  select (there e) = there (select e)

  -- The other alternatives force the meet below z or force z below d_i ∨ y.
  choose : Any (_≤ʷ σ i) (map σ (j ∷ js))
    ⊎ Any (⋀⁺ (σ j) (map σ js) ≤ʷ_) (z ∷ core (suc i) ∷ []) → i ∈ j ∷ js
  choose (inj₁ e) = select (Any.map⁻ {f = σ} {xs = j ∷ js} e)
  choose (inj₂ (here e)) = ⊥-elim (meet≰z j js e)
  choose (inj₂ (there (here e))) = ⊥-elim
    (z≰descending∨y (suc i) (≤ʷ-trans (z≤meet j js) (proj₂ (≤∧-inv e))))

-- FJN Theorem 1.28, in the form of Corollary 1.13.
σ-free : FreelyGenerates σ
σ-free = σ-join-condition , σ-meet-condition
```

#### The embeddings

`countable-embedding`{.AgdaFunction} packages the injective homomorphism
from `FL(ℕ)` to `FL(Fin 3)` in the library's subalgebra relation.
`finite-embedding`{.AgdaFunction} restricts it to any finite rank.
`finite-rank-embedding`{.AgdaFunction} composes with the inclusion of the
first three generators of `Fin n`.  Its source rank is unrestricted, a
slightly stronger conclusion than requiring both ranks to be at least
three.  Each package also has separately named homomorphism and
injectivity components for consumers that need the underlying map.

```agda
-- Theorem 1.28's homomorphism is substitution by the countable family.
countable-hom : hom (proj₁ (FL ℕ)) (proj₁ (FL (Fin 3)))
countable-hom = subst-hom σ

-- Corollary 1.13 turns free generation into injectivity.
countable-injective : IsInjective (proj₁ countable-hom)
countable-injective = freelyGenerates→injective σ σ-free

-- The countably generated free lattice embeds in FL(3).
countable-embedding : proj₁ (FL ℕ) IsSubalgebraOf proj₁ (FL (Fin 3))
countable-embedding = countable-hom , countable-injective

-- Every finite restriction of the countable family freely generates.
σ-finite-free : (n : ℕ) → FreelyGenerates (σ-finite n)
σ-finite-free n = freelyGenerates-reindex σ toℕ toℕ-injective σ-free

-- The homomorphism from any finite rank into rank three.
finite-hom : (n : ℕ) → hom (proj₁ (FL (Fin n))) (proj₁ (FL (Fin 3)))
finite-hom n = subst-hom (σ-finite n)

-- The finite restriction remains injective, including ranks zero and one.
finite-injective : (n : ℕ) → IsInjective (proj₁ (finite-hom n))
finite-injective n = freelyGenerates→injective (σ-finite n) (σ-finite-free n)

-- Every finite-rank free lattice embeds in FL(3).
finite-embedding : (n : ℕ) → proj₁ (FL (Fin n)) IsSubalgebraOf proj₁ (FL (Fin 3))
finite-embedding n = finite-hom n , finite-injective n

-- Include the first three generators of a larger finite generating set.
three-inclusion : (n : ℕ) → 3 ≤ n → Sub (Fin 3) (Fin n)
three-inclusion n bound i = ℊ (inject≤ i bound)

-- These included generators freely generate by Corollary 1.5.
three-inclusion-free : (n : ℕ) (bound : 3 ≤ n) → FreelyGenerates (three-inclusion n bound)
three-inclusion-free n bound = freelyGenerates-reindex ℊ (λ i → inject≤ i bound)
  (λ {i} {j} → inject≤-injective bound bound i j) generators-free

-- The inclusion induces an injective homomorphism.
three-inclusion-injective : (n : ℕ) (bound : 3 ≤ n)
  → IsInjective (proj₁ (subst-hom (three-inclusion n bound)))
three-inclusion-injective n bound =
  freelyGenerates→injective (three-inclusion n bound) (three-inclusion-free n bound)

-- The composite substitution realizes the embedding between finite ranks.
finite-rank-hom : (m n : ℕ) → 3 ≤ n
  → hom (proj₁ (FL (Fin m))) (proj₁ (FL (Fin n)))
finite-rank-hom m n bound = subst-hom (σ-finite m ⨟ three-inclusion n bound)

-- Both factors are injective, so the composite is injective.
finite-rank-injective : (m n : ℕ) (bound : 3 ≤ n)
  → IsInjective (proj₁ (finite-rank-hom m n bound))
finite-rank-injective m n bound = ⨟-injective (σ-finite m) (three-inclusion n bound)
  (finite-injective m) (three-inclusion-injective n bound)

-- Any finite rank embeds in every finite rank at least three.
finite-rank-embedding : (m n : ℕ) → 3 ≤ n
  → proj₁ (FL (Fin m)) IsSubalgebraOf proj₁ (FL (Fin n))
finite-rank-embedding m n bound = finite-rank-hom m n bound , finite-rank-injective m n bound
```

#### Into a free lattice on any set with three elements

The embeddings need only three distinct generators in the target.  For a set
`Y` and an injection `y : Fin 3 ↣ Y`, the generators of `FL(Y)` at the three
elements `y i` freely generate (Corollary 1.5, as for
`three-inclusion-free`{.AgdaFunction}, which is the case `Y = Fin n`), and
Theorem 1.28's finite family, followed by them, embeds every finite rank in
`FL(Y)` (`finite-rank-into`{.AgdaFunction}).  No decidable equality on `Y` is
needed.

```agda
private variable υ : Level

-- The generators of FL(Y) at three distinct elements of Y.
three-generators : {Y : Type υ} → Fin 3 ↣ Y → Sub (Fin 3) Y
three-generators y i = ℊ (Injection.to y i)

-- They freely generate, by Corollary 1.5.
three-generators-free : {Y : Type υ} (y : Fin 3 ↣ Y) → FreelyGenerates (three-generators y)
three-generators-free y =
  freelyGenerates-reindex ℊ (Injection.to y) (Injection.injective y) generators-free

-- Every finite rank embeds in FL(Y) when Y has three distinct elements.
finite-rank-into : {Y : Type υ} (m : ℕ) → Fin 3 ↣ Y → hom (proj₁ (FL (Fin m))) (proj₁ (FL Y))
finite-rank-into m y = subst-hom (σ-finite m ⨟ three-generators y)

finite-rank-into-injective : {Y : Type υ} (m : ℕ) (y : Fin 3 ↣ Y)
  → IsInjective (proj₁ (finite-rank-into m y))
finite-rank-into-injective m y = ⨟-injective (σ-finite m) (three-generators y) (finite-injective m)
  (freelyGenerates→injective (three-generators y) (three-generators-free y))
```
