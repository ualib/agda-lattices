---
layout: default
file: "src/Lattices/Nation/Cycle.lagda.md"
title: "Lattices.Nation.Cycle module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### C-cycles, minimal C-cycles, and their subsequences

This is the [Lattices.Nation.Cycle][] module of the [agda-lattices][] library.

A *C-cycle* in a finite semidistributive lattice is a sequence `a₀, …, a_{m-1}`
of join irreducible elements with `aᵢ C aᵢ₊₁` for every `i`, the subscripts
read modulo `m` ([Freese, Ježek, and Nation (1995)][], p. 53 and p. 109).  The
proof that an S-lattice contains none (Lemma 5.54) works with a *minimal*
C-cycle, one of least length, and uses its minimality in exactly two ways
(p. 110): two members `p`, `q` of the cycle satisfy `p C q` only when `q` is
the successor of `p`; and, as the *free star principle*, `p B q` fails for
distinct members `p`, `q` with `q` not the successor of `p`, so that
`q ≰ κ(p)` implies `q₋ ≰ κ(p)`.  Its lemmas speak of *subsequences* of a
minimal C-cycle, not necessarily consecutive ones.  This module supplies the
following, on a table lattice with both semidistributive laws and (W), through
the vocabulary of [Lattices.Nation.Kappa][]:

+  **Paths** (`Path`{.AgdaDatatype}): sequences of steps of a relation,
   indexed by their length and their two ends, with their vertices at
   positions counted from the start (`vertex`{.AgdaFunction}), concatenation,
   and splitting at a position (`split`{.AgdaFunction}).  The datatype takes
   the relation as a parameter and is declared outside the lattice's module,
   so that the paths of a lattice and of its dual are instances of one type.
   A C-cycle of length `suc k` is a path of `C`-steps of that length from an
   element to itself; whether one exists is decidable (`cycle?`{.AgdaFunction}),
   by a search over the paths of that length.
+  **Minimal cycles** (`MinimalCycle`{.AgdaRecord}): a cycle of length `suc k`
   together with the fact that no cycle of a smaller length exists; any
   cycle yields one (`minimize`{.AgdaFunction}), by a search for the least
   length, with no classical principle.  Its members are its vertices
   `at i` for positions `i ≤ k`, and the two uses of minimality follow
   by constructing a shorter cycle: a vertex that occurs at two positions
   gives one by cutting, so the members are distinct
   (`distinct`{.AgdaFunction}); and `at i C at j` with `j` not the successor
   of `i` gives one by splicing, so `C` relates members only to their
   successors (`inorder`{.AgdaFunction}), the successor of the last position
   being `0`.
+  **Subsequences** (`Sub`{.AgdaRecord}): a family `x : ℕ → L`, read at the
   indices up to `l`, of members at strictly increasing positions of the cycle.
   Such a family inherits distinctness and the successor property in its own
   indexing (`Sub-distinct`{.AgdaFunction}, `Sub-inorder`{.AgdaFunction}), where
   the wrap from the last index to `0` is possible exactly when the
   subsequence's last member precedes its first in the cycle; the lemmas of
   Section V.3 hypothesize that case away where they must.  A prefix of a
   subsequence is a subsequence (`Sub-prefix`{.AgdaFunction}), and so is any
   strictly increasing reindexing (`Sub-restrict`{.AgdaFunction}), which is how
   the inductive applications of those lemmas pass to a part of a subsequence.
   The free star principle is `Sub-freeStar`{.AgdaFunction}, with
   `Sub-freeStar′`{.AgdaFunction} its form: `q₋ ≤ κ(p)` implies
   `q ≤ κ(p)`.
+  **The lower cover of a member is join irreducible**
   (`₋-irr`{.AgdaFunction}, `Sub-₋irr`{.AgdaFunction}): a member `p` has a
   predecessor `q` with `q C p`, which makes `p₋` a meet of two larger
   elements, and a successor `r` with `p C r`, which makes `p₋` nonzero; (W)
   forbids doubly reducible elements (`W-irreducible`{.AgdaFunction} of
   [Lattices.Semidistributive][]), so `p₋` is join irreducible and `p₋₋`
   exists (p. 110 to 111).
+  **The dual cycle** (`CycleMap`{.AgdaModule}, `CycleDuality`{.AgdaModule}):
   `κ` carries a C-path of the lattice to a Cᵈ-path of the dual lattice of
   the same length, with `A` and `B` exchanged (Lemma 2.63), and a minimal
   cycle to a minimal cycle, since `κᵈ` carries a shorter dual cycle back.
   This is the step Lemma 5.54 takes to apply its lemmas to the dual
   lattice.
  Its decisions are passed to helper functions rather than
scrutinized by `with`: a `with` in a context holding a hypothesis of type
`a C b` abstracts over `κ`, at a cost of tens of seconds per clause.

The module checks in 2.3 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Cycle where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; toℕ )
                                                   renaming ( _<_ to _<ᶠ_ )
open import Data.Fin.Properties                    using ( any? ; toℕ<n ; pigeonhole )
                                                   renaming ( _≟_ to _≟ᶠ_ )
open import Data.List.Relation.Unary.All           using ( All )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _+_ ; _∸_ ; z≤n ; s≤s ; s≤s⁻¹ )
                                                   renaming ( _≤_ to _≤ℕ_ ; _<_ to _<ℕ_ )
open import Data.Nat.Properties                    using ( _≟_ ; <⇒≤ ; ≤∧≢⇒< ; <-cmp ; ≰⇒> ; +-suc
                                                         ; +-identityʳ ; +-comm ; m≤n⇒m<n∨m≡n ; m∸n≤m
                                                         ; m+[n∸m]≡n ; +-∸-assoc ; m∸n+n≡m ; +-monoʳ-< ; +-monoˡ-<
                                                         ; +-assoc ; m+n∸m≡n ; m≤m+n ; m≤n+m ; ∸-monoˡ-< ; ∸-monoˡ-≤ ; n<1+n ; n≤1+n )
                                                   renaming ( ≤-trans to ≤ℕ-trans ; ≤-reflexive to ≤ℕ-reflexive )
                                                   renaming ( _≤?_ to _≤ℕ?_ ; ≤-refl to ≤ℕ-refl
                                                            ; <-trans to <ℕ-trans ; ≤-<-trans to ≤ℕ-<-trans
                                                            ; <-≤-trans to <ℕ-≤-trans ; <-irrefl to <ℕ-irrefl )
open import Data.Nat.DivMod                        using ( _%_ ; m≤n⇒m%n≡m ; [m+n]%n≡m%n ; n%n≡0 ; m%n%n≡m%n
                                                         ; %-distribˡ-+ ; m%n<n )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( _∘_ )
open import Relation.Binary.Definitions            using ( tri< ; tri≈ ; tri> )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; _×-dec_ ; decidable-stable )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Bounded.Finite    using ( dual-laws )
open import Lattices.Nation.Kappa      using ( module Kappa ; module KappaDuality )
open import Lattices.Semidistributive  using ( IsSemidistributive ; SatisfiesW ; W-irreducible )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

#### Paths of a relation

A path of `k` steps of a relation `R` from `a` to `b` is a list of related
pairs; its vertex at position `i` is the `i`-th element it passes through, the
end for every position beyond the end.  Splitting at a position `i ≤ℕ k` gives
the two parts, and the vertices of the second part are those of the whole at
positions shifted by `i` (`vertex-split`{.AgdaFunction}).

```agda
infixr 5 _∷_

-- A path of k steps of R from a to b.
data Path {m : ℕ} (R : Fin m → Fin m → Type) : ℕ → Fin m → Fin m → Type where
  []   : ∀ {a} → Path R 0 a a
  _∷_  : ∀ {k a b c} → R a b → Path R k b c → Path R (suc k) a c

module _ {m : ℕ} {R : Fin m → Fin m → Type} where

  infixr 5 _++_

  -- The vertex at position i, counted from the start; beyond the end, the end.
  vertex : ∀ {k a b} → Path R k a b → ℕ → Fin m
  vertex {a = a} _        zero     = a
  vertex {b = b} []       (suc i)  = b
  vertex         (_ ∷ p)  (suc i)  = vertex p i

  vertex-end : ∀ {k a b} (p : Path R k a b) i → k ≤ℕ i → vertex p i ≡ b
  vertex-end []       zero     _          = refl
  vertex-end []       (suc i)  _          = refl
  vertex-end (_ ∷ p)  (suc i)  (s≤s k≤i)  = vertex-end p i k≤i

  -- Consecutive vertices are related.
  vertex-step : ∀ {k a b} (p : Path R k a b) i → suc i ≤ℕ k → R (vertex p i) (vertex p (suc i))
  vertex-step (s ∷ p)  zero     _           = s
  vertex-step (s ∷ p)  (suc i)  (s≤s si≤k)  = vertex-step p i si≤k

  _++_ : ∀ {k l a b c} → Path R k a b → Path R l b c → Path R (k + l) a c
  []       ++ q = q
  (s ∷ p)  ++ q = s ∷ (p ++ q)

  -- Splitting a path at a position.
  split : ∀ {k a b} (p : Path R k a b) i → i ≤ℕ k
        → Path R i a (vertex p i) × Path R (k ∸ i) (vertex p i) b
  split p        zero     _          = [] , p
  split (s ∷ p)  (suc i)  (s≤s i≤k)  = (s ∷ proj₁ (split p i i≤k)) , proj₂ (split p i i≤k)

  -- The vertices of the second part, at positions counted from the split.
  vertex-split : ∀ {k a b} (p : Path R k a b) i (i≤k : i ≤ℕ k) l
               → vertex (proj₂ (split p i i≤k)) l ≡ vertex p (i + l)
  vertex-split p        zero     _          l = refl
  vertex-split (s ∷ p)  (suc i)  (s≤s i≤k)  l = vertex-split p i i≤k l

  -- Appending a step at the end of a path.
  snoc : ∀ {k a b c} → Path R k a b → R b c → Path R (suc k) a c
  snoc []       s = s ∷ []
  snoc (t ∷ p)  s = t ∷ snoc p s

  vertex-snoc : ∀ {k a b c} (p : Path R k a b) (s : R b c) i → i ≤ℕ k → vertex (snoc p s) i ≡ vertex p i
  vertex-snoc []       s zero     _          = refl
  vertex-snoc []       s (suc i)  ()
  vertex-snoc (t ∷ p)  s zero     _          = refl
  vertex-snoc (t ∷ p)  s (suc i)  (s≤s i≤k)  = vertex-snoc p s i i≤k

  -- A closed path rotated by one step: its first step moved to the end, and by r steps.
  rot : ∀ {k b} → Path R (suc k) b b → Σ (Fin m) λ b′ → Path R (suc k) b′ b′
  rot (s ∷ p) = _ , snoc p s

  vertex-rot : ∀ {k b} (p : Path R (suc k) b b) i → i ≤ℕ k → vertex (proj₂ (rot p)) i ≡ vertex p (suc i)
  vertex-rot (s ∷ p) i i≤k = vertex-snoc p s i i≤k

  rotⁿ : ∀ {k b} → ℕ → Path R (suc k) b b → Σ (Fin m) λ b′ → Path R (suc k) b′ b′
  rotⁿ zero     p = _ , p
  rotⁿ (suc r)  p = rot (proj₂ (rotⁿ r p))

  -- Whether there is a path of k steps from a to b, for a decided relation.
  path? : (∀ a b → Dec (R a b)) → ∀ k a b → Dec (Path R k a b)
  path? R? zero a b with a ≟ᶠ b
  ... | yes refl  = yes []
  ... | no a≢b    = no λ { [] → a≢b refl }
  path? R? (suc k) a b with any? (λ c → R? a c ×-dec path? R? k c b)
  ... | yes (c , aRc , p)  = yes (aRc ∷ p)
  ... | no none            = no λ { (_∷_ {b = c} aRc p) → none (c , aRc , p) }
```

A path of as many steps as there are elements passes through one element
twice, so it contains a cycle: the part between the two occurrences
(`path→cycle`{.AgdaFunction}, by the standard library's pigeonhole principle).

```agda
module _ {m : ℕ} {R : Fin m → Fin m → Type} where

  -- A path of m steps through m elements contains a cycle.
  path→cycle : ∀ {a b} → Path R m a b → Σ (Fin m) λ c → Σ ℕ λ l → Path R (suc l) c c
  path→cycle {a} {b} p = found (pigeonhole (n<1+n m) λ i → vertex p (toℕ i))
    where
    found : Σ (Fin (suc m)) (λ i → Σ (Fin (suc m)) λ j → i <ᶠ j × vertex p (toℕ i) ≡ vertex p (toℕ j))
          → Σ (Fin m) λ c → Σ ℕ λ l → Path R (suc l) c c
    found (i , j , i<j , e) = vertex p (toℕ i) , toℕ j ∸ suc (toℕ i) , q′
      where
      i≤m : toℕ i ≤ℕ m
      i≤m = s≤s⁻¹ (toℕ<n i)

      p₂ : Path R (m ∸ toℕ i) (vertex p (toℕ i)) b
      p₂ = proj₂ (split p (toℕ i) i≤m)

      q : Path R (toℕ j ∸ toℕ i) (vertex p (toℕ i)) (vertex p₂ (toℕ j ∸ toℕ i))
      q = proj₁ (split p₂ (toℕ j ∸ toℕ i) (∸-monoˡ-≤ (toℕ i) (s≤s⁻¹ (toℕ<n j))))

      end≡ : vertex p₂ (toℕ j ∸ toℕ i) ≡ vertex p (toℕ i)
      end≡ = trans (vertex-split p (toℕ i) i≤m (toℕ j ∸ toℕ i))
                   (trans (cong (vertex p) (m+[n∸m]≡n (<⇒≤ i<j))) (sym e))

      q′ : Path R (suc (toℕ j ∸ suc (toℕ i))) (vertex p (toℕ i)) (vertex p (toℕ i))
      q′ = subst (λ l → Path R l (vertex p (toℕ i)) (vertex p (toℕ i))) (+-∸-assoc 1 i<j)
                 (subst (Path R (toℕ j ∸ toℕ i) (vertex p (toℕ i))) end≡ q)
```

A lemma on subtraction that the constructions below use: for `0 <ℕ j ≤ℕ i`, the
difference `i ∸ j` is smaller than `i`.

```agda
private
  m∸n<m : ∀ m n → 0 <ℕ n → 0 <ℕ m → m ∸ n <ℕ m
  m∸n<m (suc m)  (suc n)  _   _   = s≤s (m∸n≤m m n)
  m∸n<m zero     _        _   ()
  m∸n<m (suc m)  zero     ()  _
```

#### Cycles, and the search for a shortest one

The lattice is fixed by its tables, their laws, and the two conditions, as in
[Lattices.Nation.Kappa][].  A cycle of length `suc k` is a path of `C`-steps of
that length from some element to itself.  Whether one exists is decidable, by a
search over the elements and the paths (`cycle?`{.AgdaFunction}).  Given a
cycle of length `suc k`, the least `k′ ≤ℕ k` with a cycle of length `suc k′` is
found by a search upward from `0` (`find`{.AgdaFunction}), which carries the
proof that no smaller length has one.

```agda
module Cycles {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
              (laws : LatticeTableLaws _∧_ _∨_)
              (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
              (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd

  -- A cycle of length suc k.
  Cycle : ℕ → Type
  Cycle k = Σ (Fin (suc n)) λ a → Path _C_ (suc k) a a

  cycle? : ∀ k → Dec (Cycle k)
  cycle? k = any? λ a → path? _C?_ (suc k) a a

  -- A minimal cycle: one of length suc k, with no cycle of a smaller length.
  record MinimalCycle : Type where
    field
      k        : ℕ
      base     : Fin (suc n)
      path     : Path _C_ (suc k) base base
      minimal  : ∀ j → j <ℕ k → ∀ b → ¬ Path _C_ (suc j) b b

  private
    -- The least length from s on at which a cycle exists, given one of length suc (s + d).
    find : ∀ s d → (∀ j → j <ℕ s → ¬ Cycle j) → Cycle (s + d) → MinimalCycle
    find s zero none (b , p) = record
      { k = s ; base = b ; path = subst (λ j → Path _C_ (suc j) b b) (+-identityʳ s) p
      ; minimal = λ j j<s b q → none j j<s (b , q) }
    find s (suc d) none c with cycle? s
    ... | yes (b , p)  = record { k = s ; base = b ; path = p ; minimal = λ j j<s b q → none j j<s (b , q) }
    ... | no ¬cs       = find (suc s) d none′ (subst Cycle (+-suc s d) c)
      where
      none′ : ∀ j → j <ℕ suc s → ¬ Cycle j
      none′ j j<ss cj with m≤n⇒m<n∨m≡n (s≤s⁻¹ j<ss)
      ... | inj₁ j<s   = none j j<s cj
      ... | inj₂ refl  = ¬cs cj

  -- Every cycle yields a minimal one.
  minimize : ∀ {k} → Cycle k → MinimalCycle
  minimize {k} c = find 0 k (λ j ()) c
```

A minimal cycle may be read from any of its members: moving the base `r`
steps along the path gives a minimal cycle of the same length
(`rotate`{.AgdaFunction}), whose member at position `i` is the member of the
original at position `r + i` modulo the length (`at-rotate`{.AgdaFunction}).
The lemmas of Section V.3 that read a window of a cycle across its base are
applied to the rotation that moves the base to the start of the window.

```agda
  -- The cycle with its base moved r steps along the path.
  rotate : MinimalCycle → ℕ → MinimalCycle
  rotate 𝒞 r = record { k = k ; base = proj₁ (rotⁿ r path) ; path = proj₂ (rotⁿ r path) ; minimal = minimal }
    where open MinimalCycle 𝒞
```

#### The members of a minimal cycle

Fix a minimal cycle of length `suc k`.  Its members are `at i`, the vertices at
the positions `i ≤ k`, read with natural numbers for positions so that the
lemmas of Section V.3 can index subsequences by numbers; the vertex at position
`suc k` is the base again.  Every member has a successor and a predecessor in
the cycle (`successor`{.AgdaFunction}, `predecessor`{.AgdaFunction}).  A member
occurring at two positions `i < j` gives a cycle of length `j ∸ i`, the part of
the path between them (`cut`{.AgdaFunction}); and a step `at i C at j` to a
position `j` other than the successor of `i` gives a cycle of length `i ∸ j + 1`
when `j ≤ i`, the part from `j` to `i` closed by the step
(`splice-back`{.AgdaFunction}), and of length `(suc k ∸ j) + i + 1` when
`i + 1 < j`, the part from `j` to the end, the part from the start to `i`, and
the step (`splice-forward`{.AgdaFunction}).  Each is shorter than `suc k`, so
minimality excludes it.

```agda
  module MinimalCycleProperties (𝒞 : MinimalCycle) where
    open MinimalCycle 𝒞 public

    -- The member at position i ≤ k; at position suc k, the base again.
    at : ℕ → Fin (suc n)
    at = vertex path

    at-wrap : at (suc k) ≡ at 0
    at-wrap = vertex-end path (suc k) ≤ℕ-refl

    -- The step out of position i ≤ k.
    step : ∀ i → i ≤ℕ k → at i C at (suc i)
    step i i≤k = vertex-step path i (s≤s i≤k)

    -- Every member has a successor and a predecessor.
    successor : ∀ i → i ≤ℕ k → Σ (Fin (suc n)) λ r → at i C r
    successor i i≤k = _ , step i i≤k

    predecessor : ∀ i → i ≤ℕ k → Σ (Fin (suc n)) λ q → q C at i
    predecessor zero     _     = _ , subst (at k C_) at-wrap (step k ≤ℕ-refl)
    predecessor (suc i)  si≤k  = _ , step i (<⇒≤ si≤k)

    -- Members are join irreducible.
    at-irr : ∀ i → i ≤ℕ k → HasOneLowerCover (at i)
    at-irr i i≤k = proj₁ (C-irr (step i i≤k))

    -- A shorter cycle contradicts minimality.
    shorter : ∀ {j b} → j <ℕ k → Path _C_ (suc j) b b → ⊥
    shorter j<k q = minimal _ j<k _ q

    -- Cutting: a member at two positions i < j ≤ k gives a cycle of length j ∸ i.
    cut : ∀ {i j} → i <ℕ j → j ≤ℕ k → at i ≡ at j → ⊥
    cut {i} {j} i<j j≤k e = shorter d<k q′
      where
      i≤k : i ≤ℕ suc k
      i≤k = <⇒≤ (<ℕ-≤-trans i<j (n≤1+n′ j≤k))
        where
        n≤1+n′ : j ≤ℕ k → j ≤ℕ suc k
        n≤1+n′ j≤k = <⇒≤ (s≤s j≤k)

      -- The path from position i to the end, and its part up to position j.
      p₂ : Path _C_ (suc k ∸ i) (at i) base
      p₂ = proj₂ (split path i i≤k)

      q : Path _C_ (j ∸ i) (at i) (vertex p₂ (j ∸ i))
      q = proj₁ (split p₂ (j ∸ i) (∸-monoˡ-≤ i (<⇒≤ (s≤s j≤k))))

      end≡ : vertex p₂ (j ∸ i) ≡ at i
      end≡ = trans (vertex-split path i i≤k (j ∸ i)) (trans (cong (vertex path) (m+[n∸m]≡n (<⇒≤ i<j))) (sym e))

      q′ : Path _C_ (suc (j ∸ suc i)) (at i) (at i)
      q′ = subst (λ l → Path _C_ l (at i) (at i)) (+-∸-assoc 1 i<j)
                 (subst (Path _C_ (j ∸ i) (at i)) end≡ q)

      d<k : j ∸ suc i <ℕ k
      d<k = <ℕ-≤-trans (m∸n<m j (suc i) (s≤s z≤n) (≤ℕ-<-trans z≤n i<j)) j≤k

    -- The members of a minimal cycle are distinct.
    distinct : ∀ {i j} → i ≤ℕ k → j ≤ℕ k → at i ≡ at j → i ≡ j
    distinct {i} {j} i≤k j≤k e with <-cmp i j
    ... | tri< i<j _ _  = ⊥-elim (cut i<j j≤k e)
    ... | tri≈ _ i≡j _  = i≡j
    ... | tri> _ _ j<i  = ⊥-elim (cut j<i i≤k (sym e))

    -- Splicing when j ≤ i: the part from j to i, closed by the step.
    splice-back : ∀ {i j} → j ≤ℕ i → i ≤ℕ k → at i C at j → ¬ (i ≡ k × j ≡ 0) → ⊥
    splice-back {i} {j} j≤i i≤k c notwrap = shorter d<k q′
      where
      j≤sk : j ≤ℕ suc k
      j≤sk = <⇒≤ (s≤s (≤ℕ-trans j≤i i≤k))

      p₂ : Path _C_ (suc k ∸ j) (at j) base
      p₂ = proj₂ (split path j j≤sk)

      q : Path _C_ (i ∸ j) (at j) (vertex p₂ (i ∸ j))
      q = proj₁ (split p₂ (i ∸ j) (∸-monoˡ-≤ j (<⇒≤ (s≤s i≤k))))

      end≡ : vertex p₂ (i ∸ j) ≡ at i
      end≡ = trans (vertex-split path j j≤sk (i ∸ j)) (cong (vertex path) (m+[n∸m]≡n j≤i))

      q′ : Path _C_ (suc (i ∸ j)) (at j) (at j)
      q′ = subst (λ l → Path _C_ l (at j) (at j)) (+-comm (i ∸ j) 1)
                 (subst (Path _C_ (i ∸ j) (at j)) end≡ q ++ (c ∷ []))

      d<k : i ∸ j <ℕ k
      d<k = decide (i ≟ k)
        where
        decide : Dec (i ≡ k) → i ∸ j <ℕ k
        decide (no i≢k)   = ≤ℕ-<-trans (m∸n≤m i j) (≤∧≢⇒< i≤k i≢k)
        decide (yes i≡k)  = subst (i ∸ j <ℕ_) i≡k (m∸n<m i j 0<j (<ℕ-≤-trans 0<j j≤i))
          where
          0<j : 0 <ℕ j
          0<j = ≤∧≢⇒< z≤n λ 0≡j → notwrap (i≡k , sym 0≡j)

    -- Splicing when i + 1 < j: the part from j to the end, the start to i, and the step.
    splice-forward : ∀ {i j} → suc i <ℕ j → j ≤ℕ k → at i C at j → ⊥
    splice-forward {i} {j} si<j j≤k c = shorter d<k q′
      where
      j≤sk : j ≤ℕ suc k
      j≤sk = <⇒≤ (s≤s j≤k)

      q : Path _C_ ((suc k ∸ j) + (i + 1)) (at j) (at j)
      q = proj₂ (split path j j≤sk)
          ++ (proj₁ (split path i (<⇒≤ (s≤s (<⇒≤ (<ℕ-≤-trans (≤ℕ-<-trans (n≤1+n i) si<j) j≤k))))) ++ (c ∷ []))

      q′ : Path _C_ (suc ((k ∸ j) + (i + 1))) (at j) (at j)
      q′ = subst (λ l → Path _C_ l (at j) (at j)) (cong (_+ (i + 1)) (+-∸-assoc 1 j≤k)) q

      -- (k ∸ j) + (i + 1) < (k ∸ j) + j = k.
      d<k : (k ∸ j) + (i + 1) <ℕ k
      d<k = subst ((k ∸ j) + (i + 1) <ℕ_) (m∸n+n≡m j≤k) (+-monoʳ-< (k ∸ j) (subst (_<ℕ j) (+-comm 1 i) si<j))

    -- A path between two members of fewer steps than their distance shortens the cycle.
    shortcut : ∀ {i j d} → i ≤ℕ j → j ≤ℕ k → i + d <ℕ j → Path _C_ d (at i) (at j) → ⊥
    shortcut {i} {j} {d} i≤j j≤k i+d<j q = shorter d′<k q′
      where
      j≤sk : j ≤ℕ suc k
      j≤sk = <⇒≤ (s≤s j≤k)

      Q : Path _C_ (i + (d + (suc k ∸ j))) base base
      Q = proj₁ (split path i (≤ℕ-trans i≤j j≤sk)) ++ (q ++ proj₂ (split path j j≤sk))

      q′ : Path _C_ (suc ((i + d) + (k ∸ j))) base base
      q′ = subst (λ l → Path _C_ l base base) e Q
        where
        e : i + (d + (suc k ∸ j)) ≡ suc ((i + d) + (k ∸ j))
        e = trans (cong (λ z → i + (d + z)) (+-∸-assoc 1 j≤k))
                  (trans (cong (i +_) (+-suc d (k ∸ j)))
                         (trans (+-suc i (d + (k ∸ j))) (cong suc (sym (+-assoc i d (k ∸ j))))))

      d′<k : (i + d) + (k ∸ j) <ℕ k
      d′<k = subst ((i + d) + (k ∸ j) <ℕ_) (m+[n∸m]≡n j≤k) (+-monoˡ-< (k ∸ j) i+d<j)

    -- C relates a member only to its successor, the successor of the last being 0.
    inorder : ∀ {i j} → i ≤ℕ k → j ≤ℕ k → at i C at j → j ≡ suc i ⊎ (i ≡ k × j ≡ 0)
    inorder {i} {j} i≤k j≤k c = decide (j ≟ suc i) ((i ≟ k) ×-dec (j ≟ 0)) (j ≤ℕ? i)
      where
      -- The decisions are passed as arguments: a `with` here would abstract over the hypothesis c,
      -- whose type unfolds κ, at a cost of tens of seconds.
      decide : Dec (j ≡ suc i) → Dec (i ≡ k × j ≡ 0) → Dec (j ≤ℕ i) → j ≡ suc i ⊎ (i ≡ k × j ≡ 0)
      decide (yes e)     _             _           = inj₁ e
      decide (no _)      (yes wrap)    _           = inj₂ wrap
      decide (no _)      (no notwrap)  (yes j≤i)   = ⊥-elim (splice-back j≤i i≤k c notwrap)
      decide (no j≢si)   (no _)        (no j≰i)    =
        ⊥-elim (splice-forward (≤∧≢⇒< (≰⇒> j≰i) λ si≡j → j≢si (sym si≡j)) j≤k c)
```

#### Subsequences

A subsequence of length `suc l` of the minimal cycle is a family
`x : ℕ → L`, read at the indices `0` to `l`, with a strictly increasing choice
of positions at which the cycle's members are the `x i`.  The whole cycle is
one (`whole`{.AgdaFunction}).  Distinctness and the successor property pass
from the cycle's positions to the family's indices: if `x i C x j`, then the
position of `x j` is the successor of that of `x i`, which forces `j = i + 1`
since the positions increase strictly, or the position of `x i` is the last
and that of `x j` is `0`, which forces `i` to be the last index and `j` the
first.  A prefix of a subsequence is a subsequence
(`Sub-prefix`{.AgdaFunction}), and so is its reindexing by any strictly
increasing map (`Sub-restrict`{.AgdaFunction}), such as a shift.

```agda
    -- A family of members at strictly increasing positions, read at the indices up to l.
    record Sub (l : ℕ) (x : ℕ → Fin (suc n)) : Type where
      field
        pos     : ℕ → ℕ
        pos≤    : ∀ {i} → i ≤ℕ l → pos i ≤ℕ k
        mono    : ∀ {i j} → i <ℕ j → j ≤ℕ l → pos i <ℕ pos j
        at-pos  : ∀ {i} → i ≤ℕ l → at (pos i) ≡ x i

    whole : Sub k at
    whole = record { pos = λ i → i ; pos≤ = λ i≤k → i≤k ; mono = λ i<j _ → i<j ; at-pos = λ _ → refl }

    module _ {l : ℕ} {x : ℕ → Fin (suc n)} (sub : Sub l x) where
      open Sub sub

      -- Members of a subsequence are join irreducible.
      Sub-irr : ∀ {i} → i ≤ℕ l → HasOneLowerCover (x i)
      Sub-irr i≤l = subst HasOneLowerCover (at-pos i≤l) (at-irr _ (pos≤ i≤l))

      -- Equal members sit at equal positions.
      private
        same-pos : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → x i ≡ x j → pos i ≡ pos j
        same-pos i≤l j≤l e = distinct (pos≤ i≤l) (pos≤ j≤l) (trans (at-pos i≤l) (trans e (sym (at-pos j≤l))))

      -- Members of a subsequence are distinct.
      Sub-distinct : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → x i ≡ x j → i ≡ j
      Sub-distinct {i} {j} i≤l j≤l e with <-cmp i j
      ... | tri< i<j _ _  = ⊥-elim (<ℕ-irrefl (same-pos i≤l j≤l e) (mono i<j j≤l))
      ... | tri≈ _ i≡j _  = i≡j
      ... | tri> _ _ j<i  = ⊥-elim (<ℕ-irrefl (same-pos j≤l i≤l (sym e)) (mono j<i i≤l))

      private
        -- The cycle's successor fact, read in the family's indices.
        next→ : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → pos j ≡ suc (pos i) → j ≡ suc i
        next→ {i} {j} i≤l j≤l next with <-cmp j (suc i)
        ... | tri≈ _ j≡si _  = j≡si
        ... | tri< j<si _ _  = ⊥-elim (not-after (m≤n⇒m<n∨m≡n (s≤s⁻¹ j<si)))
          where
          not-after : j <ℕ i ⊎ j ≡ i → ⊥
          not-after (inj₁ j<i)  = <ℕ-irrefl refl (<ℕ-trans (mono j<i i≤l) (subst (pos i <ℕ_) (sym next) ≤ℕ-refl))
          not-after (inj₂ j≡i)  = <ℕ-irrefl refl (subst (pos i <ℕ_) (trans (sym next) (cong pos j≡i)) ≤ℕ-refl)
        ... | tri> _ _ si<j  = ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans (mono (n<1+n i) (<⇒≤ (<ℕ-≤-trans si<j j≤l)))
                                 (s≤s⁻¹ (subst (pos (suc i) <ℕ_) next (mono si<j j≤l)))))

        -- The cycle's wrap, read in the family's indices.
        wrap→ : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → pos i ≡ k → pos j ≡ 0 → i ≡ l × j ≡ 0
        wrap→ {i} {j} i≤l j≤l pi≡k pj≡0 = i≡l , j≡0
          where
          i≡l : i ≡ l
          i≡l with m≤n⇒m<n∨m≡n i≤l
          ... | inj₂ e    = e
          ... | inj₁ i<l  = ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans (subst (_<ℕ pos l) pi≡k (mono i<l ≤ℕ-refl)) (pos≤ ≤ℕ-refl)))

          j≡0 : j ≡ 0
          j≡0 with m≤n⇒m<n∨m≡n (z≤n {j})
          ... | inj₂ e    = sym e
          ... | inj₁ 0<j  = ⊥-elim (<ℕ-irrefl refl (<ℕ-≤-trans (mono 0<j j≤l) (subst (_≤ℕ pos 0) (sym pj≡0) z≤n)))

      -- A step between members of a subsequence goes to the next index, or from the last to 0.
      Sub-inorder : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → x i C x j → j ≡ suc i ⊎ (i ≡ l × j ≡ 0)
      Sub-inorder {i} {j} i≤l j≤l c =
        from (inorder (pos≤ i≤l) (pos≤ j≤l) (subst₂ _C_ (sym (at-pos i≤l)) (sym (at-pos j≤l)) c))
        where
        from : pos j ≡ suc (pos i) ⊎ (pos i ≡ k × pos j ≡ 0) → j ≡ suc i ⊎ (i ≡ l × j ≡ 0)
        from (inj₁ next)           = inj₁ (next→ i≤l j≤l next)
        from (inj₂ (pi≡k , pj≡0))  = inj₂ (wrap→ i≤l j≤l pi≡k pj≡0)

      -- A prefix of a subsequence is a subsequence.
      Sub-prefix : ∀ {l′} → l′ ≤ℕ l → Sub l′ x
      Sub-prefix l′≤l = record { pos = pos ; pos≤ = λ i≤l′ → pos≤ (≤ℕ-trans i≤l′ l′≤l)
                               ; mono = λ i<j j≤l′ → mono i<j (≤ℕ-trans j≤l′ l′≤l)
                               ; at-pos = λ i≤l′ → at-pos (≤ℕ-trans i≤l′ l′≤l) }

      -- A strictly increasing reindexing of a subsequence is a subsequence.
      Sub-restrict : ∀ {l′} (ρ : ℕ → ℕ) → (∀ {i j} → i <ℕ j → j ≤ℕ l′ → ρ i <ℕ ρ j)
                   → (∀ {i} → i ≤ℕ l′ → ρ i ≤ℕ l) → Sub l′ (x ∘ ρ)
      Sub-restrict ρ ρ-mono ρ≤ = record
        { pos = pos ∘ ρ ; pos≤ = λ i≤l′ → pos≤ (ρ≤ i≤l′)
        ; mono = λ i<j j≤l′ → mono (ρ-mono i<j j≤l′) (ρ≤ j≤l′) ; at-pos = λ i≤l′ → at-pos (ρ≤ i≤l′) }

      -- Positions grow at least as fast as indices.
      Sub-stretch : ∀ {i} d → i + d ≤ℕ l → pos i + d ≤ℕ pos (i + d)
      Sub-stretch {i} zero    _     = ≤ℕ-reflexive (trans (+-identityʳ (pos i)) (cong pos (sym (+-identityʳ i))))
      Sub-stretch {i} (suc d) i+sd≤l = subst (λ z → pos i + suc d ≤ℕ pos z) (sym (+-suc i d))
        (≤ℕ-trans (subst (_≤ℕ suc (pos (i + d))) (sym (+-suc (pos i) d)) (s≤s (Sub-stretch d (≤ℕ-trans (n≤1+n (i + d)) (subst (_≤ℕ l) (+-suc i d) i+sd≤l)))))
                  (mono (n<1+n (i + d)) (subst (_≤ℕ l) (+-suc i d) i+sd≤l)))

      -- A path between members of the subsequence, of fewer steps than their distance in it, shortens the cycle.
      Sub-shortcut : ∀ {i j d} → i ≤ℕ j → j ≤ℕ l → i + d <ℕ j → Path _C_ d (x i) (x j) → ⊥
      Sub-shortcut {i} {j} {d} i≤j j≤l i+d<j q =
        shortcut (pos-mono-≤ i≤j j≤l) (pos≤ j≤l) pos-gap (subst₂ (Path _C_ d) (sym (at-pos (≤ℕ-trans i≤j j≤l))) (sym (at-pos j≤l)) q)
        where
        pos-mono-≤ : ∀ {i j} → i ≤ℕ j → j ≤ℕ l → pos i ≤ℕ pos j
        pos-mono-≤ {i} {j} i≤j j≤l = from (m≤n⇒m<n∨m≡n i≤j)
          where
          from : i <ℕ j ⊎ i ≡ j → pos i ≤ℕ pos j
          from (inj₁ i<j) = <⇒≤ (mono i<j j≤l)
          from (inj₂ e)   = ≤ℕ-reflexive (cong pos e)

        -- pos i + d < pos i + (j ∸ i) ≤ pos j.
        pos-gap : pos i + d <ℕ pos j
        pos-gap = <ℕ-≤-trans (+-monoʳ-< (pos i) (subst (_<ℕ j ∸ i) (m+n∸m≡n i d) (∸-monoˡ-<′ i+d<j)))
                             (subst (λ z → pos i + (j ∸ i) ≤ℕ pos z) (m+[n∸m]≡n i≤j) (Sub-stretch (j ∸ i) (subst (_≤ℕ l) (sym (m+[n∸m]≡n i≤j)) j≤l)))
          where
          -- i + d < j gives d < j ∸ i, as (i + d) ∸ i = d.
          ∸-monoˡ-<′ : i + d <ℕ j → (i + d) ∸ i <ℕ j ∸ i
          ∸-monoˡ-<′ h = ∸-monoˡ-< h (m≤m+n i d)

      -- The free star principle: B fails between members at non-successive indices.
      Sub-freeStar : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → j ≢ suc i → ¬ (i ≡ l × j ≡ 0) → ¬ (x i B x j)
      Sub-freeStar i≤l j≤l j≢si ¬wrap xiBxj = from (Sub-inorder i≤l j≤l (inj₂ xiBxj))
        where
        from : _ → ⊥
        from (inj₁ e)   = j≢si e
        from (inj₂ wr)  = ¬wrap wr

      -- Its form in the proofs: for distinct such members, q₋ ≤ κ p implies q ≤ κ p.
      Sub-freeStar′ : ∀ {i j} → i ≤ℕ l → j ≤ℕ l → i ≢ j → j ≢ suc i → ¬ (i ≡ l × j ≡ 0)
                    → x j ₋ ≤ κ (x i) → x j ≤ κ (x i)
      Sub-freeStar′ {i} {j} i≤l j≤l i≢j j≢si ¬wrap q₋≤κ = decidable-stable (x j ≤? κ (x i)) λ q≰κ →
        Sub-freeStar i≤l j≤l j≢si ¬wrap
          (B-from-κ (Sub-irr i≤l) (Sub-irr j≤l) (λ e → i≢j (Sub-distinct i≤l j≤l e)) q₋≤κ q≰κ)
```

#### The lower cover of a member is join irreducible

An element `p` with a predecessor `q C p` and a successor `p C r` has a join
irreducible lower cover (p. 110 to 111).  From `q C p`, `p₋` is the meet of `p`
with a second element strictly above it: `κ p` when `q A p`, since
`p ∧ κ p = p₋` and `κ p = p₋` would put `q ≤ p ∨ κ p = p`; and `κ q` when
`q B p`, since `p₋ ≤ κ q`, `p ≰ κ q`, and `κ q = p₋` would put
`q ≤ q₋ ∨ p ≤ p`.  From `p C r`, `p₋` is not the least element: when `p A r`,
the join irreducible `r` lies below `p₋`, and when `p B r`, `p₋ = 0` would put
`p ≤ r`.  If `p₋` were not join irreducible, it would be the join of the
elements strictly below it, hence of two of them (`two-below`{.AgdaFunction} of
[Lattices.Bounded.Finite][]), and (W) forbids an element that is both such a
join and such a meet.

```agda
  -- An element with a C-predecessor and a C-successor has a join irreducible lower cover.
  ₋-irr : ∀ {p q r} → q C p → p C r → HasOneLowerCover (p ₋)
  ₋-irr {p} {q} {r} qCp pCr = decide (hasOneLowerCover? (p ₋))
    where
    one : HasOneLowerCover p
    one = proj₂ (C-irr qCp)

    -- p₋ is not the least element.
    nonzero : ∀ {r} → p C r → ⊥ᴸ ≢ p ₋
    nonzero {r} (inj₁ (_ , ir , r<p , _)) e = proj₂ ir (≤-antisym (₋≤ r) (≤-trans r≤⊥ (⊥ᴸ-least (r ₋))))
      where
      -- r ≤ p₋ = ⊥, so r₋ ≤ r ≤ ⊥ ≤ r₋.
      r≤⊥ : r ≤ ⊥ᴸ
      r≤⊥ = subst (r ≤_) (sym e) (<→≤₋ r<p)
    nonzero {r} (inj₂ pBr@(_ , _ , _ , p≤ , _)) e =
      B→≰ pBr (≤-trans p≤ (∨-least (subst (_≤ r) e (⊥ᴸ-least r)) ≤-refl))

    -- p₋ is the meet of p with an element other than p₋.
    meet : ∀ {q} → q C p → Σ (Fin (suc n)) λ z → p ₋ ≡ p ∧ z × p ₋ ≢ z
    meet (inj₁ (_ , _ , p<q , q≤)) =
      κ p , sym (a∧κ one)
      , λ e → proj₂ p<q (≤-antisym (proj₁ p<q) (≤-trans q≤ (∨-least ≤-refl (subst (_≤ p) e (₋≤ p)))))
    meet {q} (inj₂ qBp@(_ , _ , _ , q≤ , _)) =
      κ q , ≤-antisym (∧-greatest (₋≤ p) (B→₋≤κ qBp)) (<→≤₋′ ∧-lowerˡ (λ e → B→≰κ qBp e))
          , λ e → B→≰ qBp (≤-trans q≤ (∨-least (≤-trans (subst (q ₋ ≤_) (sym e) (₋≤κ q)) (₋≤ p)) ≤-refl))

    -- (W) forbids p₋ to be both a join of two smaller and a meet of two larger elements.
    doubly : Σ (Fin (suc n)) (λ z → p ₋ ≡ p ∧ z × p ₋ ≢ z)
           → Σ (Fin (suc n)) (λ x → Σ (Fin (suc n)) λ y → x < p ₋ × y < p ₋ × x ∨ y ≡ p ₋) → ⊥
    doubly (z , p₋≡p∧z , p₋≢z) (x , y , x<p₋ , y<p₋ , e) =
      cases (W-irreducible (tableLattice _∧_ _∨_ laws) w (sym e) p₋≡p∧z)
      where
      cases : (p ₋ ≡ p ⊎ p ₋ ≡ z) ⊎ (p ₋ ≡ x ⊎ p ₋ ≡ y) → ⊥
      cases (inj₁ (inj₁ p₋≡p))  = proj₂ one p₋≡p
      cases (inj₁ (inj₂ p₋≡z))  = p₋≢z p₋≡z
      cases (inj₂ (inj₁ p₋≡x))  = proj₂ x<p₋ (sym p₋≡x)
      cases (inj₂ (inj₂ p₋≡y))  = proj₂ y<p₋ (sym p₋≡y)

    decide : Dec (HasOneLowerCover (p ₋)) → HasOneLowerCover (p ₋)
    decide (yes one′)  = one′
    decide (no ¬one′)  = ⊥-elim (doubly (meet qCp) (two-below (below (p ₋)) ⊥ᴸ (All.tabulate ∈below⁻)
                                                               (⊥ᴸ-least (p ₋) , nonzero pCr) (¬one→₋≡ ¬one′)))

  -- So every member of a minimal cycle, and of a subsequence of one, has a join irreducible lower cover.
  module _ (𝒞 : MinimalCycle) where
    open MinimalCycleProperties 𝒞

    at-₋irr : ∀ i → i ≤ℕ k → HasOneLowerCover (at i ₋)
    at-₋irr i i≤k = ₋-irr (proj₂ (predecessor i i≤k)) (proj₂ (successor i i≤k))

    Sub-₋irr : ∀ {l} {x : ℕ → Fin (suc n)} → Sub l x → ∀ {i} → i ≤ℕ l → HasOneLowerCover (x i ₋)
    Sub-₋irr sub i≤l = subst (λ a → HasOneLowerCover (a ₋)) (Sub.at-pos sub i≤l) (at-₋irr _ (Sub.pos≤ sub i≤l))
  -- The members of a rotation, through the positions of the original read modulo its length.
  module Rotation (𝒞 : MinimalCycle) where
    open MinimalCycle 𝒞
    module 𝒫 = MinimalCycleProperties 𝒞

    atᶜ : ℕ → Fin (suc n)
    atᶜ j = 𝒫.at (j % suc k)

    atᶜ-≤ : ∀ {j} → j ≤ℕ k → atᶜ j ≡ 𝒫.at j
    atᶜ-≤ j≤k = cong 𝒫.at (m≤n⇒m%n≡m j≤k)

    atᶜ-wrap : ∀ j → atᶜ (j + suc k) ≡ atᶜ j
    atᶜ-wrap j = cong 𝒫.at ([m+n]%n≡m%n j (suc k))

    at-rotate : ∀ r i → i ≤ℕ k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ atᶜ (r + i)
    at-rotate zero     i i≤k = sym (atᶜ-≤ i≤k)
    at-rotate (suc r)  i i≤k = trans (vertex-rot (proj₂ (rotⁿ r path)) i i≤k) (cases (m≤n⇒m<n∨m≡n i≤k))
      where
      cases : i <ℕ k ⊎ i ≡ k → vertex (proj₂ (rotⁿ r path)) (suc i) ≡ atᶜ (suc r + i)
      cases (inj₁ i<k) = trans (at-rotate r (suc i) i<k) (cong atᶜ (+-suc r i))
      cases (inj₂ e)   =
        trans (vertex-end (proj₂ (rotⁿ r path)) (suc i) (≤ℕ-reflexive (cong suc (sym e))))
              (trans (at-rotate r 0 z≤n)
                     (trans (cong atᶜ (+-identityʳ r))
                            (trans (sym (atᶜ-wrap r)) (cong atᶜ (trans (+-suc r k) (cong (suc r +_) (sym e)))))))

    -- Reading a rotation below the length, at the length (the base again), and across it.
    at-rotate-≤ : ∀ r {i} → r + i ≤ℕ k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ 𝒫.at (r + i)
    at-rotate-≤ r {i} r+i≤k = trans (at-rotate r i (≤ℕ-trans (m≤n+m i r) r+i≤k)) (atᶜ-≤ r+i≤k)

    at-rotate-≤′ : ∀ r {i} → i ≤ℕ k → r + i ≤ℕ suc k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ 𝒫.at (r + i)
    at-rotate-≤′ r {i} i≤k r+i≤sk = cases (m≤n⇒m<n∨m≡n r+i≤sk)
      where
      cases : r + i <ℕ suc k ⊎ r + i ≡ suc k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ 𝒫.at (r + i)
      cases (inj₁ lt) = at-rotate-≤ r (s≤s⁻¹ lt)
      cases (inj₂ eq) = trans (at-rotate r i i≤k)
                              (trans (cong atᶜ eq) (trans (cong 𝒫.at (n%n≡0 (suc k))) (trans (sym 𝒫.at-wrap) (cong 𝒫.at (sym eq)))))

    at-rotate-wrap : ∀ r {i} d → i ≤ℕ k → r + i ≡ d + suc k → d ≤ℕ k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ 𝒫.at d
    at-rotate-wrap r {i} d i≤k eq d≤k = trans (at-rotate r i i≤k) (trans (cong atᶜ eq) (trans (atᶜ-wrap d) (atᶜ-≤ d≤k)))

    -- Reading a rotation at every position up to the length, the base again included.
    at-rotate-all : ∀ r i → i ≤ℕ suc k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ atᶜ (r + i)
    at-rotate-all r i i≤sk = cases (m≤n⇒m<n∨m≡n i≤sk)
      where
      cases : i <ℕ suc k ⊎ i ≡ suc k → MinimalCycleProperties.at (rotate 𝒞 r) i ≡ atᶜ (r + i)
      cases (inj₁ lt)   = at-rotate r i (s≤s⁻¹ lt)
      cases (inj₂ refl) = trans (MinimalCycleProperties.at-wrap (rotate 𝒞 r))
                                (trans (at-rotate r 0 z≤n) (trans (cong atᶜ (+-identityʳ r)) (sym (atᶜ-wrap r))))

    -- Positions equal modulo the length read the same member, and stay equal after a step or a shift.
    atᶜ-cong : ∀ a b → a % suc k ≡ b % suc k → atᶜ a ≡ atᶜ b
    atᶜ-cong a b e = cong 𝒫.at e

    %-suc : ∀ a b → a % suc k ≡ b % suc k → suc a % suc k ≡ suc b % suc k
    %-suc a b e = trans (%-distribˡ-+ 1 a (suc k))
                            (trans (cong (λ z → (1 % suc k + z) % suc k) e) (sym (%-distribˡ-+ 1 b (suc k))))

    %-+ : ∀ a b c → a % suc k ≡ b % suc k → (a + c) % suc k ≡ (b + c) % suc k
    %-+ a b c e = trans (%-distribˡ-+ a c (suc k))
                            (trans (cong (λ z → (z + c % suc k) % suc k) e) (sym (%-distribˡ-+ b c (suc k))))

    %-idem : ∀ a → (a % suc k) % suc k ≡ a % suc k
    %-idem a = m%n%n≡m%n a (suc k)

    %-wrap : ∀ a → (a + suc k) % suc k ≡ a % suc k
    %-wrap a = [m+n]%n≡m%n a (suc k)

    %-≤ : ∀ a → a % suc k ≤ℕ k
    %-≤ a = s≤s⁻¹ (m%n<n a (suc k))
```

#### The dual cycle

`κ` carries a C-step to a Cᵈ-step with `A` and `B` exchanged (Lemma 2.63), hence
a C-path to a Cᵈ-path of the same length (`map-κ`{.AgdaFunction}), where the
dual's paths are those of the relation `C` of the dual tables.  A minimal
C-cycle then gives a minimal Cᵈ-cycle: a shorter Cᵈ-cycle would be carried
back by `κᵈ`, the map of the dual instance, to a shorter C-cycle.  The second
instance's paths are paths of the relation `C` at the dual of the dual tables,
which is the relation `C` itself, since the relations depend on the tables and
not on their laws.

```agda
module CycleMap {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                (laws : LatticeTableLaws _∧_ _∨_)
                (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open KappaDuality laws sd using ( module ᵈ ; A→Bᵈ ; B→Aᵈ )

  -- κ carries a C-step to a Cᵈ-step, A and B exchanged.
  C→Cᵈ : ∀ {a b} → a C b → κ a ᵈ.C κ b
  C→Cᵈ (inj₁ aAb) = inj₂ (A→Bᵈ aAb)
  C→Cᵈ (inj₂ aBb) = inj₁ (B→Aᵈ aBb)

  -- κ carries a C-path to a Cᵈ-path of the same length.
  map-κ : ∀ {k a b} → Path _C_ k a b → Path ᵈ._C_ k (κ a) (κ b)
  map-κ []       = []
  map-κ (s ∷ p)  = C→Cᵈ s ∷ map-κ p

  -- The vertices of the image are the images of the vertices.
  vertex-map-κ : ∀ {k a b} (p : Path _C_ k a b) i → vertex (map-κ p) i ≡ κ (vertex p i)
  vertex-map-κ p        zero     = refl
  vertex-map-κ []       (suc i)  = refl
  vertex-map-κ (s ∷ p)  (suc i)  = vertex-map-κ p i

module CycleDuality {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                    (laws : LatticeTableLaws _∧_ _∨_)
                    (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws))
                    (w : SatisfiesW (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open KappaDuality laws sd using ( module ᵈ )
  open CycleMap laws sd

  module 𝒫  = Cycles laws sd w
  module 𝒫ᵈ = Cycles (dual-laws laws) (swap sd) (W-dual w)
  module ᴹ  = CycleMap (dual-laws laws) (swap sd)

  -- A minimal C-cycle gives a minimal Cᵈ-cycle of the same length, through κ.
  dual-cycle : 𝒫.MinimalCycle → 𝒫ᵈ.MinimalCycle
  dual-cycle 𝒞 = record
    { k = k ; base = κ base ; path = map-κ path
    ; minimal = λ j j<k b q → minimal j j<k (ᵈ.κ b) (ᴹ.map-κ q) }
    where open 𝒫.MinimalCycle 𝒞
```
