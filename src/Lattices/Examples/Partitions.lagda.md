---
layout: default
file: "src/Lattices/Examples/Partitions.lagda.md"
title: "Lattices.Examples.Partitions module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Worked example: the partition lattices `Eq(3)` and `Eq(4)`

This is the [Lattices.Examples.Partitions][] module of the [agda-lattices][] library.

`Eq(n)` is the lattice of equivalence relations on an `n`-element set, ordered
by refinement; agda-algebras builds it order-first as
`EqLattice n`{.AgdaFunction} of [Classical.Structures.Lattice.Partitions][],
whose elements are parent vectors (`ParentVec n`{.AgdaFunction}, a label in
`Fin n` for each point) read through their kernels, so that two vectors are
equal when they induce the same partition.  `Eq(3)` has five elements, the
discrete and the one-block partitions and the three partitions with one pair,
and it is `M₃`: modular and not distributive.  `Eq(4)` has fifteen and is not
modular, which is the first case of the classical fact that `Eq(n)` is modular
only for `n ≤ 3`.  This module establishes the three verdicts by evaluation
and exhibits the failures, as follows:

+  `Eq₃-modular`{.AgdaFunction} and `Eq₃-not-distributive`{.AgdaFunction},
   with the diamond the failure of distributivity gives by Birkhoff's
   construction (`Eq₃-diamond`{.AgdaFunction});
+  `Eq₄-not-modular`{.AgdaFunction}, with the failure
   `x = {01}{2}{3} ≤ z = {01}{23}`, `y = {02}{13}`, at which
   `x ∨ (y ∧ z) = x ∨ 0 = x` but `(x ∨ y) ∧ z = 1 ∧ z = z`
   (`Eq₄-modular-failure`{.AgdaFunction}), and the pentagon
   `0 < x < z < 1`, `0 < y < 1` that Dedekind's construction makes of it
   (`Eq₄-pentagon`{.AgdaFunction}).

Two things stand between `EqLattice n`{.AgdaFunction} and a sweep.  First, it
carries no enumeration, and its raw carrier is too large to sweep: there are
`nⁿ` parent vectors, `256` for `n = 4`, against `15` partitions.  So the module
builds a `FiniteAlgebra`{.AgdaRecord} whose enumeration lists one
representative of each partition, its *restricted growth string* (the labels
in order of first appearance: `0`, then at most one more than the largest label
so far), decides equality of partitions (`_≈ᵖ?_`{.AgdaFunction}, mutual
refinement, which the agda-algebras module does not provide), and proves the
enumeration surjective by checking, for each of the `nⁿ` vectors, that some
representative induces the same partition: `27` vectors against `5`
representatives for `n = 3`, and `256` against `15` for `n = 4`, a check paid
once.  A sweep of `Eq(3)` then runs over `5³ = 125` triples.  A sweep of
`Eq(4)` would run over `15³ = 3375`; it answers no at the 994th, measured at
3.9 seconds on 2026-10-22, enough to make this module heavy, so `Eq(4)`'s
verdict is read off its failure instead, one instance decided by evaluation.
The sweep itself is `isModular-Eq? 4 Eq₄-finite`{.AgdaFunction}, for a reader
who wants to run it.

Second, the join `_∨ᵖ_`{.AgdaFunction} of agda-algebras merges blocks by a fold
over all `n²` pairs of points, each step a function that consults the previous
step's function up to three times, so that evaluating one join at check time
takes time exponential in `n²`.  Measured on 2026-10-22: one sweep of `225`
joins in `Eq(4)` did not finish in 500 seconds.  The module therefore computes
the same fold with the labels stored in a vector after each step
(`_∨ᶠ_`{.AgdaFunction}, the same steps of agda-algebras' `JoinOf`{.AgdaModule}
module, with the same results), proves the two joins equal for every `n`
(`∨ᵖ≈∨ᶠ`{.AgdaFunction}), and decides the predicates through
`isModular-by?`{.AgdaFunction} and `isDistributive-by?`{.AgdaFunction} of
[Lattices.Modular][], which compute each instance with the vector join and
carry the verdict back to `EqLattice n`{.AgdaFunction} itself.  The meet
`_∧ᵖ_`{.AgdaFunction}, a search for the least point of each intersection
block, has no such cost and is used as it stands.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.Partitions where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using ( Bool ; true ; false ; if_then_else_ )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; any? )
open import Data.List.Base                         using ( List ; foldr ; allFin ; cartesianProduct )
import Data.List.Base as List
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; ∃-syntax )
open import Data.Vec.Base                          using ( Vec ; _∷_ ; [] ; lookup ; tabulate )
open import Data.Vec.Properties                    using ( lookup∘tabulate )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; does ; map′ ; _×-dec_ ; _→-dec_
                                                         ; from-yes ; from-no )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice                using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic          using ( module Lattice-Op )
open import Classical.Structures.Lattice.Partitions     using ( EqLattice ; _⊑_ ; _≈ᵖ_ ; _∧ᵖ_ ; _∨ᵖ_
                                                              ; ≈ᵖ-refl ; module JoinOf )
open import Setoid.Algebras.Basic                       using ( 𝔻[_] )
open import Setoid.Algebras.Finite                      using ( FiniteAlgebra )
open import Setoid.Congruences.Certificates.Schema      using ( ParentVec ; parent )

-- Imports from this library ----------------------------------------------------
open import Lattices.Examples.M3         using ( M₃ )
open import Lattices.Examples.N5         using ( N₅ )
open import Lattices.Modular             using ( IsModular ; IsDistributive ; ModularFailure
                                               ; ModularFailure→¬IsModular
                                               ; DistributiveFailure ; isModular-by?
                                               ; isDistributive-by? )
open import Lattices.Modular.Birkhoff    using ( birkhoff )
open import Lattices.Modular.Dedekind    using ( dedekind )
open import Lattices.Nation              using ( Embeds )
```
-->

#### Deciding equality of partitions

One partition refines another, `pu ⊑ pw`, when every pair of points in one
block of `pu` lies in one block of `pw`.  That is a statement about the `n²`
pairs of points, each decided by comparing labels, so `all?`{.AgdaFunction}
decides it, once per point; equality of partitions is refinement both ways.

```agda
module _ {n : ℕ} where
  infix 4 _⊑?_ _≈ᵖ?_

  _⊑?_ : (pu pw : ParentVec n) → Dec (pu ⊑ pw)
  pu ⊑? pw = map′ (λ h {i} {j} → h i j) (λ h i j → h {i} {j})
                  (all? λ i → all? λ j → parent pu i ≟ parent pu j →-dec parent pw i ≟ parent pw j)

  _≈ᵖ?_ : (pu pw : ParentVec n) → Dec (pu ≈ᵖ pw)
  pu ≈ᵖ? pw = pu ⊑? pw ×-dec pw ⊑? pu

  -- Vectors with the same labels induce the same partition.
  same-labels : ∀ (pu pw : ParentVec n) → (∀ k → parent pu k ≡ parent pw k) → pu ≈ᵖ pw
  same-labels _ _ h = (λ {i} {j} e → trans (sym (h i)) (trans e (h j)))
                , (λ {i} {j} e → trans (h i) (trans e (sym (h j))))
```

#### The join, with its labels stored

`JoinOf.joinAcc`{.AgdaFunction} folds the merge steps `step`{.AgdaFunction}
over a list of pairs, starting from the labels of `pu`, and each step is a
function of the previous step's labelling.  `joinVec`{.AgdaFunction} folds the
same steps, but tabulates each step's labelling into a vector before the next
step reads it, so that each label is computed once.  The two agree label by
label (`joinVec-lookup`{.AgdaFunction}), by induction on the list: a step reads
its input only through its values, so it gives equal labels on inputs with
equal values (`step-ext`{.AgdaFunction}).  At the list of all pairs, which is
the one `JoinOf.join-vec`{.AgdaFunction} folds over, `_∨ᶠ_`{.AgdaFunction}
has the labels of `_∨ᵖ_`{.AgdaFunction}, hence the same partition.

```agda
  module FastJoin (pu pw : ParentVec n) where
    open JoinOf pu pw using ( step ; relabel ; joinAcc )

    -- The fold of JoinOf, the labelling stored in a vector after each step.
    joinVec : List (Fin n × Fin n) → ParentVec n
    joinVec = foldr (λ p v → tabulate (step p (lookup v))) pu

    relabel-ext : ∀ {v v' : Fin n → Fin n} → (∀ m → v m ≡ v' m)
      → ∀ i j k → relabel v i j k ≡ relabel v' i j k
    relabel-ext {v} {v'} e i j k =
      trans (cong₂ (λ a b → if does (a ≟ b) then v i else a) (e k) (e j))
            (cong (λ c → if does (v' k ≟ v' j) then c else v' k) (e i))

    step-ext : ∀ {v v' : Fin n → Fin n} → (∀ m → v m ≡ v' m)
      → ∀ p k → step p v k ≡ step p v' k
    step-ext {v} {v'} e (i , j) k = guard (does (parent pw i ≟ parent pw j))
      where
      guard : (b : Bool) → (if b then relabel v i j else v) k ≡ (if b then relabel v' i j else v') k
      guard true   = relabel-ext e i j k
      guard false  = e k

    joinVec-lookup : ∀ ps k → lookup (joinVec ps) k ≡ joinAcc ps k
    joinVec-lookup List.[]        k = refl
    joinVec-lookup (p List.∷ ps)  k = trans (lookup∘tabulate (step p (lookup (joinVec ps))) k)
                                            (step-ext (joinVec-lookup ps) p k)

  private
    allPairs : List (Fin n × Fin n)
    allPairs = cartesianProduct (allFin n) (allFin n)

  infixr 6 _∨ᶠ_

  -- The join of two partitions, computed with stored labels.
  _∨ᶠ_ : ParentVec n → ParentVec n → ParentVec n
  pu ∨ᶠ pw = FastJoin.joinVec pu pw allPairs

  ∨ᵖ≈∨ᶠ : ∀ pu pw → pu ∨ᵖ pw ≈ᵖ pu ∨ᶠ pw
  ∨ᵖ≈∨ᶠ pu pw = same-labels (pu ∨ᵖ pw) (pu ∨ᶠ pw) λ k →
    trans (lookup∘tabulate (JoinOf.joinAcc pu pw allPairs) k)
          (sym (FastJoin.joinVec-lookup pu pw allPairs k))
```

#### Enumerations

`partition-finite`{.AgdaFunction} makes the `FiniteAlgebra`{.AgdaRecord} of
`EqLattice n`{.AgdaFunction} from a vector of representatives and a proof that
every parent vector induces the partition of one of them.  The representatives
of `Eq(3)` and `Eq(4)` are the restricted growth strings of length `3` and `4`,
`5` and `15` of them, the Bell numbers; their surjectivity is decided over all
`3³` and `4⁴` vectors, a vector being given by its entries.

```agda
partition-finite : ∀ {n} (k : ℕ) (reps : Vec (ParentVec n) k)
  → (∀ pv → ∃[ i ] lookup reps i ≈ᵖ pv) → FiniteAlgebra (proj₁ (EqLattice n))
partition-finite k reps sur = record
  { _≟_       = _≈ᵖ?_
  ; card      = k
  ; enum      = lookup reps
  ; enum-sur  = sur
  }

Eq₃-reps : Vec (ParentVec 3) 5
Eq₃-reps = (0F ∷ 0F ∷ 0F ∷ []) ∷ (0F ∷ 0F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 0F ∷ [])
         ∷ (0F ∷ 1F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 2F ∷ []) ∷ []

Eq₄-reps : Vec (ParentVec 4) 15
Eq₄-reps = (0F ∷ 0F ∷ 0F ∷ 0F ∷ []) ∷ (0F ∷ 0F ∷ 0F ∷ 1F ∷ []) ∷ (0F ∷ 0F ∷ 1F ∷ 0F ∷ [])
         ∷ (0F ∷ 0F ∷ 1F ∷ 1F ∷ []) ∷ (0F ∷ 0F ∷ 1F ∷ 2F ∷ []) ∷ (0F ∷ 1F ∷ 0F ∷ 0F ∷ [])
         ∷ (0F ∷ 1F ∷ 0F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 0F ∷ 2F ∷ []) ∷ (0F ∷ 1F ∷ 1F ∷ 0F ∷ [])
         ∷ (0F ∷ 1F ∷ 1F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 1F ∷ 2F ∷ []) ∷ (0F ∷ 1F ∷ 2F ∷ 0F ∷ [])
         ∷ (0F ∷ 1F ∷ 2F ∷ 1F ∷ []) ∷ (0F ∷ 1F ∷ 2F ∷ 2F ∷ []) ∷ (0F ∷ 1F ∷ 2F ∷ 3F ∷ []) ∷ []

private
  Eq₃-sur′ : ∀ a b c → ∃[ i ] lookup Eq₃-reps i ≈ᵖ (a ∷ b ∷ c ∷ [])
  Eq₃-sur′ = from-yes (all? λ a → all? λ b → all? λ c → any? λ i →
                        lookup Eq₃-reps i ≈ᵖ? (a ∷ b ∷ c ∷ []))

  Eq₄-sur′ : ∀ a b c d → ∃[ i ] lookup Eq₄-reps i ≈ᵖ (a ∷ b ∷ c ∷ d ∷ [])
  Eq₄-sur′ = from-yes (all? λ a → all? λ b → all? λ c → all? λ d → any? λ i →
                        lookup Eq₄-reps i ≈ᵖ? (a ∷ b ∷ c ∷ d ∷ []))

Eq₃-sur : ∀ pv → ∃[ i ] lookup Eq₃-reps i ≈ᵖ pv
Eq₃-sur (a ∷ b ∷ c ∷ []) = Eq₃-sur′ a b c

Eq₄-sur : ∀ pv → ∃[ i ] lookup Eq₄-reps i ≈ᵖ pv
Eq₄-sur (a ∷ b ∷ c ∷ d ∷ []) = Eq₄-sur′ a b c d

Eq₃-finite : FiniteAlgebra (proj₁ (EqLattice 3))
Eq₃-finite = partition-finite 5 Eq₃-reps Eq₃-sur

Eq₄-finite : FiniteAlgebra (proj₁ (EqLattice 4))
Eq₄-finite = partition-finite 15 Eq₄-reps Eq₄-sur
```

#### The verdicts

The verdicts on `Eq(3)` are decisions of [Lattices.Modular][] on
`EqLattice 3`, computed with the stored-label join, whose agreement with
`_∨ᵖ_`{.AgdaFunction} is `∨ᵖ≈∨ᶠ`{.AgdaFunction}; the meet is the lattice's own,
which agrees with itself by reflexivity.  The verdict on `Eq(4)` is in the next
section.

```agda
module _ (n : ℕ) where
  private
    ∧-agree : ∀ (x y : ParentVec n) → x ∧ᵖ y ≈ᵖ x ∧ᵖ y
    ∧-agree x y = ≈ᵖ-refl {pv = x ∧ᵖ y}

  isModular-Eq? : FiniteAlgebra (proj₁ (EqLattice n)) → Dec (IsModular (EqLattice n))
  isModular-Eq? 𝑭 = isModular-by? (EqLattice n) 𝑭 _∧ᵖ_ _∨ᶠ_ ∧-agree ∨ᵖ≈∨ᶠ

  isDistributive-Eq? : FiniteAlgebra (proj₁ (EqLattice n)) → Dec (IsDistributive (EqLattice n))
  isDistributive-Eq? 𝑭 = isDistributive-by? (EqLattice n) 𝑭 _∧ᵖ_ _∨ᶠ_ ∧-agree ∨ᵖ≈∨ᶠ

Eq₃-modular : IsModular (EqLattice 3)
Eq₃-modular = from-yes (isModular-Eq? 3 Eq₃-finite)

Eq₃-not-distributive : ¬ IsDistributive (EqLattice 3)
Eq₃-not-distributive = from-no (isDistributive-Eq? 3 Eq₃-finite)
```

#### The failures, and the forbidden sublattices

A failure is checked the same way: the inequality `x ≤ z` is an equation of
meets, decided as it stands; the two sides of the failing law are compared
with the stored-label join, and the comparison is carried back by the
agreement of the joins and the congruence of the operations
(`modularFailure-by-∨ᶠ`{.AgdaFunction},
`distributiveFailure-by-∨ᶠ`{.AgdaFunction}).
Each returns the failure as a whole, proved once for every `n`, so that at a
concrete partition its type is literally the one the criteria take: a type
that names the slow join on concrete vectors, compared with another spelling
of the same type, would make the checker evaluate that join.

In `Eq(3)` the atoms `a = {01}{2}`, `b = {02}{1}` and `c = {0}{12}` give
`a ∧ (b ∨ c) = a ∧ 1 = a` and `(a ∧ b) ∨ (a ∧ c) = 0 ∨ 0 = 0`, and Birkhoff's
construction turns the failure into a diamond, whose five elements are the
whole of `Eq(3)`.  In `Eq(4)` the failure of the introduction refutes the
modular law (`Eq₄-not-modular`{.AgdaFunction}), and gives a pentagon by
Dedekind's construction.

```agda
module _ {n : ℕ} where
  open Lattice-Op (EqLattice n)        using ( _∧_ ; _∨_ ; ∧-cong )
  open Lattice-Order (EqLattice n)     using ( _≤_ )
  open SetoidReasoning 𝔻[ proj₁ (EqLattice n) ]

  private
    -- x ∨ y in an expression may be computed by either join.
    ∨≈ : ∀ x y → x ∨ᵖ y ≈ᵖ x ∨ᶠ y
    ∨≈ = ∨ᵖ≈∨ᶠ {n}

  -- The modular law fails at x ≤ z, y if it fails there with the stored-label join.
  modularFailure-by-∨ᶠ : ∀ (x y z : ParentVec n) → x ≤ z → ¬ (x ∨ᶠ (y ∧ᵖ z) ≈ᵖ (x ∨ᶠ y) ∧ᵖ z)
    → ModularFailure (EqLattice n)
  modularFailure-by-∨ᶠ x y z x≤z fails = x , y , z , x≤z , λ e → fails (begin
    x ∨ᶠ (y ∧ᵖ z)    ≈˘⟨ ∨≈ x (y ∧ᵖ z) ⟩
    x ∨ (y ∧ z)      ≈⟨ e ⟩
    (x ∨ y) ∧ z      ≈⟨ ∧-cong (∨≈ x y) (≈ᵖ-refl {pv = z}) ⟩
    (x ∨ᶠ y) ∧ᵖ z    ∎)

  -- The distributive law fails at x, y, z if it fails there with the stored-label join.
  distributiveFailure-by-∨ᶠ : ∀ (x y z : ParentVec n) → ¬ (x ∧ᵖ (y ∨ᶠ z) ≈ᵖ (x ∧ᵖ y) ∨ᶠ (x ∧ᵖ z))
    → DistributiveFailure (EqLattice n)
  distributiveFailure-by-∨ᶠ x y z fails = x , y , z , λ e → fails (begin
    x ∧ᵖ (y ∨ᶠ z)              ≈˘⟨ ∧-cong (≈ᵖ-refl {pv = x}) (∨≈ y z) ⟩
    x ∧ (y ∨ z)                ≈⟨ e ⟩
    (x ∧ y) ∨ (x ∧ z)          ≈⟨ ∨≈ (x ∧ᵖ y) (x ∧ᵖ z) ⟩
    (x ∧ᵖ y) ∨ᶠ (x ∧ᵖ z)       ∎)

-- The atoms {01}{2}, {02}{1}, {0}{12} of Eq(3).
ε₁ ε₂ ε₃ : ParentVec 3
ε₁ = 0F ∷ 0F ∷ 1F ∷ []
ε₂ = 0F ∷ 1F ∷ 0F ∷ []
ε₃ = 0F ∷ 1F ∷ 1F ∷ []

Eq₃-distributive-failure : DistributiveFailure (EqLattice 3)
Eq₃-distributive-failure =
  distributiveFailure-by-∨ᶠ ε₁ ε₂ ε₃ (from-no ((ε₁ ∧ᵖ (ε₂ ∨ᶠ ε₃)) ≈ᵖ? ((ε₁ ∧ᵖ ε₂) ∨ᶠ (ε₁ ∧ᵖ ε₃))))

-- Eq(3) has a diamond, by Birkhoff's construction.
Eq₃-diamond : Embeds M₃ (EqLattice 3)
Eq₃-diamond = birkhoff (EqLattice 3) Eq₃-modular Eq₃-distributive-failure

-- x = {01}{2}{3}, y = {02}{13}, z = {01}{23} in Eq(4).
πx πy πz : ParentVec 4
πx = 0F ∷ 0F ∷ 1F ∷ 2F ∷ []
πy = 0F ∷ 1F ∷ 0F ∷ 1F ∷ []
πz = 0F ∷ 0F ∷ 1F ∷ 1F ∷ []

private
  -- x ≤ z, an equation of meets.
  πx≤πz : Lattice-Order._≤_ (EqLattice 4) πx πz
  πx≤πz = from-yes ((πx ∧ᵖ πz) ≈ᵖ? πx)

  -- The two sides differ, computed with the stored-label join.
  πxyz-fails : ¬ (πx ∨ᶠ (πy ∧ᵖ πz) ≈ᵖ (πx ∨ᶠ πy) ∧ᵖ πz)
  πxyz-fails = from-no ((πx ∨ᶠ (πy ∧ᵖ πz)) ≈ᵖ? ((πx ∨ᶠ πy) ∧ᵖ πz))

Eq₄-modular-failure : ModularFailure (EqLattice 4)
Eq₄-modular-failure = modularFailure-by-∨ᶠ πx πy πz πx≤πz πxyz-fails

-- Eq(4) is not modular.
Eq₄-not-modular : ¬ IsModular (EqLattice 4)
Eq₄-not-modular = ModularFailure→¬IsModular (EqLattice 4) Eq₄-modular-failure

-- Eq(4) has a pentagon, by Dedekind's construction.
Eq₄-pentagon : Embeds N₅ (EqLattice 4)
Eq₄-pentagon = dedekind (EqLattice 4) Eq₄-modular-failure
```
