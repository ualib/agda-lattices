---
layout: default
file: "src/Lattices/Nation/Bounded.lagda.md"
title: "Lattices.Nation.Bounded module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### A finite semidistributive lattice is bounded exactly when it has no C-cycle

This is the [Lattices.Nation.Bounded][] module of the [agda-lattices][] library.

Lemma 2.62 of [Freese, Ježek, and Nation (1995)][] (p. 53, after Jónsson) says
that a finite semidistributive lattice is lower bounded if and only if it
contains no C-cycle, and Corollary 2.65 (p. 54) adds that it is then bounded.
This module proves both on the table lattices of [Lattices.Table][], with lower
boundedness in the form of [Lattices.Bounded.Finite][], the absence of a D-cycle,
and the relations of [Lattices.Nation.Kappa][].  It supplies the following:

+  **`C ⊆ D`** (`C→D`{.AgdaFunction}, Theorem 2.59 (3), p. 52): for `a A b` the
   witness is `κ b`, for `a B b` it is `a₋`.  So a C-cycle is a D-cycle, and a
   lower bounded lattice has no C-cycle (`lowerBounded→noCCycle`{.AgdaFunction}).
+  **Good and bad elements.**  The book argues with `D(L)`, the elements that
   have a D-rank, and its complement.  Here an element is *good* when it is
   accessible for the converse of `D` (`Good`{.AgdaFunction}), the form in
   which [Lattices.Bounded.Finite][] has well-foundedness; this is decidable,
   since an element is good exactly when every D-path from it has at most
   `n` steps, a path of more steps passing through some element twice
   (`good?`{.AgdaFunction}).  A bad element depends on a bad element
   (`bad-step`{.AgdaFunction}), and the members of a D-cycle are bad.
+  **The finite Lemma 2.52** (`descend`{.AgdaFunction}).  For a bad join
   irreducible `a`, some minimal nontrivial join cover of `a` whose join is
   minimal among the *nontrivial joins* above `a` (the elements `w ≥ a` that are
   the join of the elements below them not above `a`, the book's `M*(a)` read
   through joins) has a bad member.  The proof descends on the join: a cover with
   a bad member whose join is not minimal is beaten by a smaller nontrivial join,
   which refines to a minimal cover; if that cover had only good members, the
   argument of Theorem 2.50 (p. 48) would refine the first cover to one of good
   elements, each good member refining the first cover through its own minimal
   cover, whose members it depends on, and minimality would put the bad member
   among them.
+  **Theorem 2.60** (`theorem-2-60`{.AgdaFunction}, p. 52): for a minimal join
   cover `Q` of `a` with minimal join, `a C q` for every `q ∈ Q`; in fact `a B q₁`
   for one member and `a A q` for the others.  The meet semidistributive law
   finds `q₁` with `a ≤ a₋ ∨ q₁`; the minimality of the join makes
   `a₋ ∨ q₁ = ⋁Q`; Theorem 1.21 ([Lattices.Semidistributive.FiniteJoins][]) and
   the minimality of the cover then put every member below `a₋` or below `q₁`.
+  **Lemma 2.62**, the other direction (`noCCycle→lowerBounded`{.AgdaFunction}):
   a D-cycle has a bad join irreducible member, which starts a C-path of `n + 1`
   steps through bad join irreducible elements, which contains a C-cycle.
+  **Corollary 2.65** (`noCCycle→bounded`{.AgdaFunction}, in
   `BoundedDuality`{.AgdaModule}): with no C-cycle the lattice is lower bounded,
   and also upper bounded, since a Cᵈ-cycle would be carried by `κᵈ` to a
   C-cycle (Lemma 2.63, through [Lattices.Nation.Cycle][]), so the dual lattice
   is lower bounded too.

Nation's paper proves the claim behind Lemma 2.62 directly (p. 314), through
canonical joinands; the book's route through minimal join covers is followed
here, with the correction that in the argument of Theorem 2.50 a good element
below a member of the first cover refines it by itself, not by that member.
Nothing classical is used: every case split is a decision.

The module checks in 2.9 s of its own under `--profile=modules` (measured
2026-10-22, with the interfaces of its imports built).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation.Bounded where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; toℕ )
open import Data.Fin.Properties                    using ( _≟_ ; all? ; any? ; ¬∀⟶∃¬ ; pigeonhole )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; map ; filter ; allFin )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-filter⁺ ; ∈-filter⁻ ; ∈-allFin ; ∈-map⁺ ; ∈-map⁻
                                                         ; ∈-++⁺ˡ ; ∈-++⁺ʳ ; ∈-++⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.All.Properties using ( ¬Any⇒All¬ ; ++⁺ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; z≤n ; s≤s )
open import Data.Nat.Properties                    using ( n<1+n )
open import Data.Product                           using ( Σ ; _×_ ; _,_ ; proj₁ ; proj₂ ; swap )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( flip )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Relation.Binary.Construct.Closure.Transitive
                                                   using ( TransClosure ; [_] ; _∷_ )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; _≢_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; ¬? ; _×-dec_ ; _→-dec_ ; map′
                                                         ; decidable-stable )

import Data.List.Membership.DecPropositional as DecMembership
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Bounded.Finite    using ( dual-laws ; Bounded
                                             ; Short ; short? ; short→acc ; long-step ; point ; point-reach
                                             ; acc→no-cycle )
open import Lattices.Nation.Cycle      using ( Path ; [] ; _∷_ ; path→cycle ; module CycleMap )
open import Lattices.Nation.Kappa      using ( module Kappa ; module KappaDuality )
open import Lattices.Semidistributive  using ( IsSemidistributive )
open import Lattices.Semidistributive.FiniteJoins  using ( ⋁-meets-below )
open import Lattices.Table             using ( LatticeTableLaws ; tableLattice )
```
-->

#### Accessibility along a transitive closure

An element accessible for the converse of a relation stays accessible along
any chain of steps of the relation.

```agda
-- Accessibility passes along a chain of steps.
acc-closure : ∀ {m} {R : Fin m → Fin m → Type} {a b} → Acc (flip R) a → TransClosure R a b → Acc (flip R) b
acc-closure (acc rs) [ aRb ]        = rs aRb
acc-closure (acc rs) (aRb ∷ bR⁺c)   = acc-closure (rs aRb) bR⁺c
```

#### `C ⊆ D`

```agda
module Bounded {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
               (laws : LatticeTableLaws _∧_ _∨_)
               (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open DecMembership (_≟_ {suc n}) using ( _∈?_ )

  -- A C-cycle of length suc k.
  CCycle : ℕ → Type
  CCycle k = Σ (Fin (suc n)) λ a → Path _C_ (suc k) a a

  -- Theorem 2.59 (3): a C b implies a D b, with the witness κ b for A and a₋ for B.
  C→D : ∀ {a b} → a C b → a D b
  C→D {a} {b} (inj₁ aAb@(_ , ib , b<a , a≤)) =
    (λ a≡b → proj₂ b<a (sym a≡b)) , ib , κ b , a≤
    , λ a≤′ → A→≰κ aAb (≤-trans a≤′ (∨-least (₋≤κ b) ≤-refl))
  C→D {a} {b} (inj₂ (ia , ib , a≢b , a≤ , a≰)) =
    a≢b , ib , a ₋ , ≤-trans a≤ (∨-least ∨-upperʳ ∨-upperˡ)
    , λ a≤′ → a≰ (≤-trans a≤′ (∨-least ∨-upperʳ ∨-upperˡ))

  -- A C-path is a D-path.
  C-path→D : ∀ {k a b} → Path _C_ (suc k) a b → TransClosure _D_ a b
  C-path→D {zero}   (s ∷ [])  = [ C→D s ]
  C-path→D {suc k}  (s ∷ p)   = C→D s ∷ C-path→D p

  -- Lemma 2.62, one direction: a lower bounded lattice has no C-cycle.
  lowerBounded→noCCycle : LowerBounded → ∀ {k} → ¬ CCycle k
  lowerBounded→noCCycle lb (a , p) = lb (a , C-path→D p)
```

#### Good and bad elements

An element is *good* when it is accessible for the converse of `D`.  Every
D-path from a good element has at most `n` steps: a path of `n + 1` steps
through the `n + 1` elements passes through one of them twice, closing a
D-cycle at an element reachable from the start, which an accessible element
cannot reach (`acc→short`{.AgdaFunction}); and conversely an element all of
whose paths are short is accessible, which [Lattices.Bounded.Finite][] proves.
So goodness is decided by the decision of the bound on the paths.  A bad
element has a D-path of `n + 2` steps, whose first step reaches an element with
a path of `n + 1` steps, which is bad (`bad-step`{.AgdaFunction}).

```agda
  -- Good: accessible for the converse of D.
  Good : Fin (suc n) → Type
  Good = Acc (flip _D_)

  -- Every D-path from a good element has at most n steps.
  acc→short : ∀ {a} → Good a → Short _D?_ (suc n) a
  acc→short {a} g = decidable-stable (short? _D?_ (suc n) a) contra
    where
    contra : ¬ Short _D?_ (suc n) a → ⊥
    contra ¬s = cycle (pigeonhole (n<1+n (suc n)) (point _D?_ (suc n) a ¬s))
      where
      -- The points of a path of suc n steps, every one of them good.
      good-point : ∀ i → Good (point _D?_ (suc n) a ¬s i)
      good-point zero     = g
      good-point (suc i)  = acc-closure g (point-reach _D?_ (suc n) a ¬s {zero} {suc i} (s≤s z≤n))

      cycle : Σ (Fin (suc (suc n))) (λ i → Σ (Fin (suc (suc n))) λ j → toℕ i Data.Nat.Base.< toℕ j
                × point _D?_ (suc n) a ¬s i ≡ point _D?_ (suc n) a ¬s j) → ⊥
      cycle (i , j , i<j , e) =
        acc→no-cycle _D?_ (good-point i)
          (subst (TransClosure _D_ (point _D?_ (suc n) a ¬s i)) (sym e) (point-reach _D?_ (suc n) a ¬s i<j))

  good? : ∀ a → Dec (Good a)
  good? a = map′ (short→acc _D?_ (suc n)) acc→short (short? _D?_ (suc n) a)

  -- A bad element depends on a bad element.
  bad-step : ∀ {a} → ¬ Good a → Σ (Fin (suc n)) λ q → a D q × ¬ Good q
  bad-step {a} ¬g = next (long-step _D?_ (suc n) a λ s → ¬g (short→acc _D?_ (suc (suc n)) s))
    where
    next : Σ (Fin (suc n)) (λ q → a D q × ¬ Short _D?_ (suc n) q) → Σ (Fin (suc n)) λ q → a D q × ¬ Good q
    next (q , aDq , ¬s) = q , aDq , λ gq → ¬s (acc→short gq)

  -- The members of a D-cycle are bad and join irreducible.
  cycle→bad : ∀ {a} → TransClosure _D_ a a → ¬ Good a
  cycle→bad c g = acc→no-cycle _D?_ g c

  closure-target : ∀ {a b} → TransClosure _D_ a b → HasOneLowerCover b
  closure-target [ aDb ]   = proj₁ (proj₂ aDb)
  closure-target (_ ∷ p)   = closure-target p
```

#### Nontrivial joins above `a`, and joins minimal among them

`notAbove a w`{.AgdaFunction} lists the elements below `w` that are not above
`a`, and `w` is a *nontrivial join* above `a` when `a ≤ w` and `w` is the join
of that list (`NontrivialJoin`{.AgdaFunction}): exactly the joins of the
nontrivial join covers of `a`, since such a cover's members are among the
elements listed (`cover→NJ`{.AgdaFunction}).  The book's `M*(a)` consists of the
minimal nontrivial join covers whose join is minimal among the joins of all
nontrivial join covers, that is, minimal among the nontrivial joins above `a`
(`MinimalIn`{.AgdaFunction}); both notions are decided by sweeps.

```agda
  notAbove? : ∀ a w x → Dec (x ≤ w × ¬ a ≤ x)
  notAbove? a w x = x ≤? w ×-dec ¬? (a ≤? x)

  -- The elements below w and not above a.
  notAbove : Fin (suc n) → Fin (suc n) → List (Fin (suc n))
  notAbove a w = filter (notAbove? a w) (allFin (suc n))

  -- w is a nontrivial join above a: a ≤ w and w is the join of the elements below it not above a.
  NontrivialJoin : Fin (suc n) → Fin (suc n) → Type
  NontrivialJoin a w = a ≤ w × ⋁ (notAbove a w) ≡ w

  nontrivialJoin? : ∀ a w → Dec (NontrivialJoin a w)
  nontrivialJoin? a w = a ≤? w ×-dec ⋁ (notAbove a w) ≟ w

  -- The join of a nontrivial join cover of a is a nontrivial join above a.
  cover→NJ : ∀ {a} R → a ≤ ⋁ R → All (λ r → ¬ a ≤ r) R → NontrivialJoin a (⋁ R)
  cover→NJ {a} R a≤ R≰ = a≤ , ≤-antisym
    (∨*-least {notAbove a (⋁ R)} {⊥ᴸ}
      (All.tabulate λ x∈ → proj₁ (proj₂ (∈-filter⁻ (notAbove? a (⋁ R)) {xs = allFin (suc n)} x∈))) (⊥ᴸ-least _))
    (∨*-least {R} {⊥ᴸ}
      (All.tabulate λ {r} r∈ → ∨*-upper {cs = notAbove a (⋁ R)} {⊥ᴸ}
                                 (∈-filter⁺ (notAbove? a (⋁ R)) (∈-allFin r) (∨*-upper {cs = R} {⊥ᴸ} r∈ , All.lookup R≰ r∈)))
      (⊥ᴸ-least _))

  -- w is minimal among the nontrivial joins above a.
  MinimalIn : Fin (suc n) → Fin (suc n) → Type
  MinimalIn a w = NontrivialJoin a w × ∀ w′ → w′ < w → ¬ NontrivialJoin a w′

  minimalIn? : ∀ a w → Dec (MinimalIn a w)
  minimalIn? a w = nontrivialJoin? a w ×-dec all? λ w′ → w′ <? w →-dec ¬? (nontrivialJoin? a w′)

  -- Joins of concatenated lists.
  ⋁-++ˡ : ∀ xs ys → ⋁ xs ≤ ⋁ (xs ++ ys)
  ⋁-++ˡ xs ys = ∨*-least {xs} {⊥ᴸ} (All.tabulate λ x∈ → ∨*-upper {cs = xs ++ ys} {⊥ᴸ} (∈-++⁺ˡ x∈)) (⊥ᴸ-least _)

  ⋁-++ʳ : ∀ xs ys → ⋁ ys ≤ ⋁ (xs ++ ys)
  ⋁-++ʳ xs ys = ∨*-least {ys} {⊥ᴸ} (All.tabulate λ y∈ → ∨*-upper {cs = xs ++ ys} {⊥ᴸ} (∈-++⁺ʳ xs y∈)) (⊥ᴸ-least _)
```

#### The finite Lemma 2.52

Fix `a`.  A *bad cover* of `a` is a minimal nontrivial join cover whose join is
minimal among the nontrivial joins above `a` and which has a bad member.  The
argument of Theorem 2.50, `good-refine`{.AgdaFunction}: a list of good elements
each below the join of a minimal cover `Q` refines `Q` into good elements, each
member by itself if it lies below a member of `Q`, and otherwise by its own
minimal cover refining `Q`, whose members it depends on and which are therefore
good.  The descent, `descend`{.AgdaFunction}: from a minimal cover with a bad
member, by well-founded induction on the join.  If the join is minimal, done.
Otherwise a smaller nontrivial join refines to a minimal cover with a smaller
join; if it has a bad member the descent continues, and if all its members are
good, `good-refine` turns it into a cover of good elements refining the first
cover, which the first cover's minimality must contain, bad member included.

```agda
  module _ {a : Fin (suc n)} where
    open MinimalJoinCover

    -- A minimal join cover of a with minimal join and a bad member.
    record BadCover : Type where
      field
        R          : List (Fin (suc n))
        Q          : MinimalJoinCover a R
        minimalIn  : MinimalIn a (⋁ (cover Q))
        bad        : Any (λ q → ¬ Good q) (cover Q)

    -- Theorem 2.50's argument: good elements below ⋁ Q refine Q into good elements.
    good-refine : ∀ {R} (Q : MinimalJoinCover a R) rs → All Good rs → All (_≤ ⋁ (cover Q)) rs
                → Σ (List (Fin (suc n))) λ V → V ≪ cover Q × All Good V × All (_≤ ⋁ V) rs
    good-refine Q []        _          _           = [] , [] , [] , []
    good-refine Q (r ∷ rs)  (g ∷ gs)   (r≤ ∷ rs≤)  = combine (good-refine Q rs gs rs≤) (part g r≤ (Any.any? (r ≤?_) (cover Q)))
      where
      -- One element: by itself when below a member of Q, else by its minimal cover refining Q.
      part : Good r → r ≤ ⋁ (cover Q) → Dec (Any (r ≤_) (cover Q))
           → Σ (List (Fin (suc n))) λ S → S ≪ cover Q × All Good S × r ≤ ⋁ S
      part g r≤ (yes below)       = r ∷ [] , below ∷ [] , g ∷ [] , ∨-upperˡ
      part (acc rs′) r≤ (no ¬below) =
        cover C , refines C , All.map (λ rDq → rs′ rDq) (dependencies C) , joins C
        where
        C : MinimalJoinCover r (cover Q)
        C = minimal-cover r (cover Q) r≤ (¬Any⇒All¬ (cover Q) ¬below)

      combine : Σ (List (Fin (suc n))) (λ V → V ≪ cover Q × All Good V × All (_≤ ⋁ V) rs)
              → Σ (List (Fin (suc n))) (λ S → S ≪ cover Q × All Good S × r ≤ ⋁ S)
              → Σ (List (Fin (suc n))) λ V → V ≪ cover Q × All Good V × All (_≤ ⋁ V) (r ∷ rs)
      combine (V , V≪ , Vg , rs≤V) (S , S≪ , Sg , r≤S) =
        S ++ V , ++⁺ S≪ V≪ , ++⁺ Sg Vg
        , ≤-trans r≤S (⋁-++ˡ S V) ∷ All.map (λ x≤V → ≤-trans x≤V (⋁-++ʳ S V)) rs≤V

    -- The descent on the join.
    descend : ∀ {R} (Q : MinimalJoinCover a R) → Any (λ q → ¬ Good q) (cover Q) → BadCover
    descend {R} Q bad = go (⋁ (cover Q)) (<-acc _) Q refl bad
      where
      go : ∀ w → Acc _<_ w → ∀ {R} (Q : MinimalJoinCover a R) → ⋁ (cover Q) ≡ w
         → Any (λ q → ¬ Good q) (cover Q) → BadCover
      go w (acc smaller) {R} Q e bad = decide (minimalIn? a w)
        where
        decide : Dec (MinimalIn a w) → BadCover
        decide (yes mi)  = record { R = R ; Q = Q ; minimalIn = subst (MinimalIn a) (sym e) mi ; bad = bad }
        decide (no ¬mi)  = step (¬∀⟶∃¬ (suc n) _ (λ w′ → w′ <? w →-dec ¬? (nontrivialJoin? a w′)) λ all → ¬mi (NJw , all))
          where
          NJw : NontrivialJoin a w
          NJw = subst (NontrivialJoin a) e (cover→NJ (cover Q) (joins Q) (nontrivial Q))

          -- A smaller nontrivial join above a.
          step : Σ (Fin (suc n)) (λ w′ → ¬ (w′ < w → ¬ NontrivialJoin a w′)) → BadCover
          step (w′ , ¬imp) = decide-bad (Any.any? (λ q → ¬? (good? q)) (cover Q′))
            where
            w′<w : w′ < w
            w′<w = decidable-stable (w′ <? w) λ ¬lt → ¬imp λ lt _ → ¬lt lt

            NJw′ : NontrivialJoin a w′
            NJw′ = decidable-stable (nontrivialJoin? a w′) λ ¬nj → ¬imp λ _ nj → ¬nj nj

            -- Its nontrivial join cover, refined to a minimal one.
            Q′ : MinimalJoinCover a (notAbove a w′)
            Q′ = minimal-cover a (notAbove a w′) (subst (a ≤_) (sym (proj₂ NJw′)) (proj₁ NJw′))
                                (All.tabulate λ r∈ → proj₂ (proj₂ (∈-filter⁻ (notAbove? a w′) r∈)))

            ⋁Q′≤w′ : ⋁ (cover Q′) ≤ w′
            ⋁Q′≤w′ = subst (⋁ (cover Q′) ≤_) (proj₂ NJw′)
                       (∨*-least {cover Q′} {⊥ᴸ} (All.tabulate λ q∈ → any≤→≤∨* (All.lookup (refines Q′) q∈)) (⊥ᴸ-least _))

            decide-bad : Dec (Any (λ q → ¬ Good q) (cover Q′)) → BadCover
            decide-bad (yes bad′)  = go (⋁ (cover Q′)) (smaller (≤-<-trans ⋁Q′≤w′ w′<w)) Q′ refl bad′
            decide-bad (no ¬bad′)  = ⊥-elim (proj₂ (proj₂ (find bad)) (All.lookup Vg q∈V))
              where
              goods : All Good (cover Q′)
              goods = All.map (λ ¬¬g → decidable-stable (good? _) ¬¬g) (¬Any⇒All¬ (cover Q′) ¬bad′)

              refined : Σ (List (Fin (suc n))) λ V → V ≪ cover Q × All Good V × All (_≤ ⋁ V) (cover Q′)
              refined = good-refine Q (cover Q′) goods
                          (All.tabulate λ q∈ → ≤-trans (∨*-upper q∈) (≤-trans ⋁Q′≤w′ (subst (w′ ≤_) (sym e) (proj₁ w′<w))))

              V : List (Fin (suc n))
              V = proj₁ refined

              Vg : All Good V
              Vg = proj₁ (proj₂ (proj₂ refined))

              a≤V : a ≤ ⋁ V
              a≤V = ≤-trans (joins Q′) (∨*-least (proj₂ (proj₂ (proj₂ refined))) (⊥ᴸ-least _))

              q∈V : proj₁ (find bad) ∈ V
              q∈V = All.lookup (minimality Q V (proj₁ (proj₂ refined)) a≤V) (proj₁ (proj₂ (find bad)))
```

#### Theorem 2.60

Fix a join irreducible `a` and a minimal join cover `Q` of `a` whose join is
minimal among the nontrivial joins above `a`.  The meet semidistributive law,
folded along the members, gives a member `q₁` with `a ≤ a₋ ∨ q₁`: otherwise `a`
would meet each `a₋ ∨ q` in `a₋`, hence their join, which is above `a`.  The
minimality of `⋁Q` makes `a₋ ∨ q₁ = ⋁Q`, since `a₋ ∨ q₁` is a nontrivial join
above `a` below it.  Theorem 1.21 and the minimality of `Q` then put every
member of `Q` below `a₋` or below `q₁` (`split-cover`{.AgdaFunction}: the
pairwise meets of the members with `a₋` and `q₁` form a cover refining `Q`, so
`Q` is among them); a member below `q₁` is `q₁`, since `Q` without it would
still cover `a`; and the members below `a₋` lie strictly below `a`.  Then
`a B q₁`: `a ≰ a₋ ∨ q₁₋`, for otherwise `a₋ ∨ q₁₋`, a nontrivial join above `a`
below `⋁Q`, would equal `⋁Q`, and `split-cover` would put `q₁` below `a₋` or below
`q₁₋`.  And `a A q` for a member `q` below `a₋`: every other member `q′` lies
below `κ q`, since `q ≤ q₋ ∨ q′` would let `q₋` replace `q` in the cover; so
`a ≤ ⋁Q ≤ q ∨ κ q`.

```agda
  module Theorem2-60 {a : Fin (suc n)} (one : HasOneLowerCover a)
                     {R : List (Fin (suc n))} (Q : MinimalJoinCover a R)
                     (mi : MinimalIn a (⋁ (MinimalJoinCover.cover Q))) where
    open MinimalJoinCover Q

    private
      -- A minimal cover's minimality, read for a member that a refining cover omits.
      omitted : ∀ {q} → q ∈ cover → ∀ Bs → Bs ≪ cover → a ≤ ⋁ Bs → ¬ q ∈ Bs → ⊥
      omitted q∈ Bs B≪ a≤B q∉B = q∉B (All.lookup (minimality Bs B≪ a≤B) q∈)

      -- The cover without one element still refines it and lies in it.
      without : Fin (suc n) → List (Fin (suc n))
      without q = filter (λ x → ¬? (x ≟ q)) cover

      without≪ : ∀ q → without q ≪ cover
      without≪ q = All.tabulate λ x∈ → lose (proj₁ (∈-filter⁻ (λ x → ¬? (x ≟ q)) {xs = cover} x∈)) ≤-refl

      ∉without : ∀ q → ¬ q ∈ without q
      ∉without q q∈ = proj₂ (∈-filter⁻ (λ x → ¬? (x ≟ q)) {xs = cover} q∈) refl

      ∈without : ∀ {x} q → x ∈ cover → x ≢ q → x ∈ without q
      ∈without q x∈ x≢q = ∈-filter⁺ (λ x → ¬? (x ≟ q)) x∈ x≢q

    -- Step 1: some member q₁ has a ≤ a₋ ∨ q₁, by (SD∧) folded along the members.
    q₁-exists : Any (λ q → a ≤ (a ₋) ∨ q) cover
    q₁-exists = decidable-stable (Any.any? (λ q → a ≤? (a ₋) ∨ q) cover) λ none →
      proj₂ one (sym (trans (sym (a≤U none)) (meet-fold one U (All.tabulate (U-meet none))
                                                       (≤-antisym ∧-lowerʳ (∧-greatest (₋≤ a) ≤-refl)))))
      where
      U : List (Fin (suc n))
      U = map ((a ₋) ∨_) cover

      -- a lies below the join of the a₋ ∨ q over a₋.
      a≤U : ¬ Any (λ q → a ≤ (a ₋) ∨ q) cover → a ≤ U ∨* (a ₋)
      a≤U _ = ≤-trans joins (∨*-least {cover} {⊥ᴸ}
                               (All.tabulate λ q∈ → ≤-trans ∨-upperʳ (∨*-upper {cs = U} {a ₋} (∈-map⁺ ((a ₋) ∨_) q∈)))
                               (⊥ᴸ-least _))

      -- Each a₋ ∨ q meets a in a₋ when a ≰ a₋ ∨ q.
      U-meet : ¬ Any (λ q → a ≤ (a ₋) ∨ q) cover → ∀ {u} → u ∈ U → a ∧ u ≡ a ₋
      U-meet none {u} u∈ = at (∈-map⁻ ((a ₋) ∨_) u∈)
        where
        at : Σ (Fin (suc n)) (λ q → q ∈ cover × u ≡ (a ₋) ∨ q) → a ∧ u ≡ a ₋
        at (q , q∈ , refl) = ≤-antisym (<→≤₋′ ∧-lowerˡ λ e → none (lose q∈ e)) (∧-greatest (₋≤ a) ∨-upperˡ)

    q₁ : Fin (suc n)
    q₁ = proj₁ (find q₁-exists)

    q₁∈ : q₁ ∈ cover
    q₁∈ = proj₁ (proj₂ (find q₁-exists))

    a≤a₋∨q₁ : a ≤ (a ₋) ∨ q₁
    a≤a₋∨q₁ = proj₂ (proj₂ (find q₁-exists))

    -- A nontrivial join above a that lies below ⋁ Q equals ⋁ Q.
    private
      nj-below : ∀ {w} → NontrivialJoin a w → w ≤ ⋁ cover → w ≡ ⋁ cover
      nj-below {w} nj w≤ = decidable-stable (w ≟ ⋁ cover) λ w≢ → proj₂ mi w (w≤ , w≢) nj

      -- a₋ ∨ y is a nontrivial join above a, when a ≤ a₋ ∨ y and a ≰ y.
      nj-pair : ∀ {y} → a ≤ (a ₋) ∨ y → ¬ a ≤ y → NontrivialJoin a ((a ₋) ∨ y)
      nj-pair {y} a≤ a≰y = subst (NontrivialJoin a) (cong ((a ₋) ∨_) (∨-absorbʳ (⊥ᴸ-least y)))
        (cover→NJ ((a ₋) ∷ y ∷ []) (subst (a ≤_) (cong ((a ₋) ∨_) (sym (∨-absorbʳ (⊥ᴸ-least y)))) a≤)
                  ((λ a≤a₋ → proj₂ one (≤-antisym (₋≤ a) a≤a₋)) ∷ a≰y ∷ []))

    -- Step 2: a₋ ∨ q₁ = ⋁ Q.
    a₋∨q₁≡ : (a ₋) ∨ q₁ ≡ ⋁ cover
    a₋∨q₁≡ = nj-below (nj-pair a≤a₋∨q₁ (All.lookup nontrivial q₁∈)) (∨-least (≤-trans (₋≤ a) joins) (∨*-upper q₁∈))

    -- Step 3: if ⋁ Q = x ∨ y, every member lies below x or below y (Theorem 1.21 and minimality).
    split-cover : ∀ x y → ⋁ cover ≡ x ∨ y → All (λ q → q ≤ x ⊎ q ≤ y) cover
    split-cover x y e = All.tabulate λ q∈ → member (All.lookup (minimality Bs B≪ a≤B) q∈)
      where
      Bs : List (Fin (suc n))
      Bs = map (_∧ x) cover ++ map (_∧ y) cover

      B≪ : Bs ≪ cover
      B≪ = All.tabulate λ m∈ → from (∈-++⁻ (map (_∧ x) cover) m∈)
        where
        from : ∀ {m} → m ∈ map (_∧ x) cover ⊎ m ∈ map (_∧ y) cover → Any (m ≤_) cover
        from (inj₁ m∈x) with ∈-map⁻ (_∧ x) m∈x
        ... | q , q∈ , refl = lose q∈ ∧-lowerˡ
        from (inj₂ m∈y) with ∈-map⁻ (_∧ y) m∈y
        ... | q , q∈ , refl = lose q∈ ∧-lowerˡ

      -- Theorem 1.21: ⋁ Q = ⋁ [x, y] lies below the join of the pairwise meets.
      a≤B : a ≤ ⋁ Bs
      a≤B = ≤-trans joins (⋁-meets-below (tableLattice _∧_ _∨_ laws) sd∨ cover (x ∷ y ∷ []) {⊥ᴸ} {⋁ Bs}
              (trans e (cong (x ∨_) (sym (∨-absorbʳ (⊥ᴸ-least y))))) (⊥ᴸ-least _) meets≤)
        where
        meets≤ : ∀ {q b} → q ∈ cover → b ∈ x ∷ y ∷ [] → q ∧ b ≤ ⋁ Bs
        meets≤ q∈ (here refl)          = ∨*-upper {cs = Bs} {⊥ᴸ} (∈-++⁺ˡ (∈-map⁺ (_∧ x) q∈))
        meets≤ q∈ (there (here refl))  = ∨*-upper {cs = Bs} {⊥ᴸ} (∈-++⁺ʳ (map (_∧ x) cover) (∈-map⁺ (_∧ y) q∈))

      member : ∀ {q} → q ∈ Bs → q ≤ x ⊎ q ≤ y
      member {q} q∈B = from (∈-++⁻ (map (_∧ x) cover) q∈B)
        where
        from : q ∈ map (_∧ x) cover ⊎ q ∈ map (_∧ y) cover → q ≤ x ⊎ q ≤ y
        from (inj₁ q∈x) with ∈-map⁻ (_∧ x) q∈x
        ... | _ , _ , refl = inj₁ ∧-lowerʳ
        from (inj₂ q∈y) with ∈-map⁻ (_∧ y) q∈y
        ... | _ , _ , refl = inj₂ ∧-lowerʳ

    -- Step 4: a member below q₁ is q₁.
    below-q₁ : ∀ {q} → q ∈ cover → q ≤ q₁ → q ≡ q₁
    below-q₁ {q} q∈ q≤q₁ = decidable-stable (q ≟ q₁) λ q≢q₁ →
      omitted q∈ (without q) (without≪ q) (≤-trans joins (∨*-least {cover} {⊥ᴸ} (All.tabulate (member q≢q₁)) (⊥ᴸ-least _))) (∉without q)
      where
      member : q ≢ q₁ → ∀ {x} → x ∈ cover → x ≤ ⋁ (without q)
      member q≢q₁ {x} x∈ = decide (x ≟ q)
        where
        decide : Dec (x ≡ q) → x ≤ ⋁ (without q)
        decide (yes refl)  = ≤-trans q≤q₁ (∨*-upper {cs = without q} {⊥ᴸ} (∈without q q₁∈ λ q₁≡q → q≢q₁ (sym q₁≡q)))
        decide (no x≢q)    = ∨*-upper {cs = without q} {⊥ᴸ} (∈without q x∈ x≢q)

    -- Step 5: a B q₁.
    aBq₁ : a B q₁
    aBq₁ = one , All.lookup irreducibles q₁∈ , (λ a≡q₁ → All.lookup nontrivial q₁∈ (≤-reflexive′ a≡q₁))
         , a≤a₋∨q₁ , ¬a≤a₋∨q₁₋
      where
      ¬a≤a₋∨q₁₋ : ¬ a ≤ (a ₋) ∨ (q₁ ₋)
      ¬a≤a₋∨q₁₋ a≤ = cases (All.lookup (split-cover (a ₋) (q₁ ₋) (sym e)) q₁∈)
        where
        e : (a ₋) ∨ (q₁ ₋) ≡ ⋁ cover
        e = nj-below (nj-pair a≤ λ a≤q₁₋ → All.lookup nontrivial q₁∈ (≤-trans a≤q₁₋ (₋≤ q₁)))
                     (≤-trans (∨-mono ≤-refl (₋≤ q₁)) (≤-reflexive′ a₋∨q₁≡))

        cases : q₁ ≤ a ₋ ⊎ q₁ ≤ q₁ ₋ → ⊥
        cases (inj₁ q₁≤a₋)   = proj₂ one (≤-antisym (₋≤ a) (≤-trans a≤a₋∨q₁ (∨-least ≤-refl q₁≤a₋)))
        cases (inj₂ q₁≤q₁₋)  = proj₂ (All.lookup irreducibles q₁∈) (≤-antisym (₋≤ q₁) q₁≤q₁₋)

    -- Step 6: a A q for a member q below a₋.
    aAq : ∀ {q} → q ∈ cover → q ≤ a ₋ → a A q
    aAq {q} q∈ q≤a₋ = one , iq , (≤-trans q≤a₋ (₋≤ a) , λ q≡a → All.lookup nontrivial q∈ (≤-reflexive′ (sym q≡a)))
                    , ≤-trans joins (∨*-least {cover} {⊥ᴸ} (All.tabulate member≤) (⊥ᴸ-least _))
      where
      iq : HasOneLowerCover q
      iq = All.lookup irreducibles q∈

      -- Every other member lies below κ q: else q₋ could replace q in the cover.
      other≤κ : ∀ {q′} → q′ ∈ cover → q′ ≢ q → q′ ≤ κ q
      other≤κ {q′} q′∈ q′≢q = →≤κ iq λ q≤ →
        omitted q∈ Bs (lose q∈ (₋≤ q) ∷ without≪ q) (≤-trans joins (∨*-least {cover} {⊥ᴸ} (All.tabulate (member q≤)) (⊥ᴸ-least _)))
                (λ { (here q≡q₋) → proj₂ iq (sym q≡q₋) ; (there q∈w) → ∉without q q∈w })
        where
        Bs : List (Fin (suc n))
        Bs = (q ₋) ∷ without q

        member : q ≤ (q ₋) ∨ q′ → ∀ {x} → x ∈ cover → x ≤ ⋁ Bs
        member q≤ {x} x∈ = decide (x ≟ q)
          where
          decide : Dec (x ≡ q) → x ≤ ⋁ Bs
          decide (yes refl)  = ≤-trans q≤ (∨-least ∨-upperˡ (≤-trans (∨*-upper {cs = without q} {⊥ᴸ} (∈without q q′∈ q′≢q)) ∨-upperʳ))
          decide (no x≢q)    = ≤-trans (∨*-upper {cs = without q} {⊥ᴸ} (∈without q x∈ x≢q)) ∨-upperʳ

      member≤ : ∀ {q′} → q′ ∈ cover → q′ ≤ q ∨ κ q
      member≤ {q′} q′∈ = decide (q′ ≟ q)
        where
        decide : Dec (q′ ≡ q) → q′ ≤ q ∨ κ q
        decide (yes refl)   = ∨-upperˡ
        decide (no q′≢q)    = ≤-trans (other≤κ q′∈ q′≢q) ∨-upperʳ

    -- Theorem 2.60: a C q for every member q of Q.
    theorem-2-60 : ∀ {q} → q ∈ cover → a C q
    theorem-2-60 {q} q∈ = cases (All.lookup (split-cover (a ₋) q₁ (sym a₋∨q₁≡)) q∈)
      where
      cases : q ≤ a ₋ ⊎ q ≤ q₁ → a C q
      cases (inj₁ q≤a₋)  = inj₁ (aAq q∈ q≤a₋)
      cases (inj₂ q≤q₁)  = subst (a C_) (sym (below-q₁ q∈ q≤q₁)) (inj₂ aBq₁)
```

#### Lemma 2.62, the other direction

A bad join irreducible element `a` depends on a bad element `q`, which lies in
the minimal cover refining `{q, x}` for the witness `x` of the dependency; the
descent gives a bad cover of `a`, and Theorem 2.60 relates `a` by `C` to its
bad member, which is join irreducible (`bad→C`{.AgdaFunction}).  Iterated
`n + 1` times from a member of a D-cycle, this gives a C-path of `n + 1` steps,
which contains a C-cycle.

```agda
  -- A bad join irreducible element is C-related to a bad join irreducible element.
  bad→C : ∀ {a} → HasOneLowerCover a → ¬ Good a → Σ (Fin (suc n)) λ q → HasOneLowerCover q × ¬ Good q × a C q
  bad→C {a} one ¬g = from-step (bad-step ¬g)
    where
    open MinimalJoinCover

    from-step : Σ (Fin (suc n)) (λ q → a D q × ¬ Good q) → Σ (Fin (suc n)) λ q → HasOneLowerCover q × ¬ Good q × a C q
    from-step (q , (a≢q , iq , x , a≤ , a≰) , ¬gq) = result (find (BadCover.bad bc))
      where
      a≰q : ¬ a ≤ q
      a≰q a≤q = a≰ (≤∨ˡ (<→≤₋′ a≤q a≢q))

      a≰x : ¬ a ≤ x
      a≰x a≤x = a≰ (≤∨ʳ a≤x)

      Q : MinimalJoinCover a (q ∷ x ∷ [])
      Q = minimal-cover a (q ∷ x ∷ []) (≤-trans a≤ (∨-least ∨-upperˡ (≤∨ʳ ∨-upperˡ))) (a≰q ∷ a≰x ∷ [])

      -- q lies in the refined cover: a cover omitting it lies below q₋ ∨ x.
      q∈ : q ∈ cover Q
      q∈ = decidable-stable (q ∈? cover Q) λ q∉ →
        a≰ (≤-trans (joins Q) (∨*-least {cover Q} {⊥ᴸ} (All.tabulate λ y∈ → member y∈ (All.lookup (refines Q) y∈) q∉) (⊥ᴸ-least _)))
        where
        member : ∀ {y} → y ∈ cover Q → Any (y ≤_) (q ∷ x ∷ []) → ¬ q ∈ cover Q → y ≤ (q ₋) ∨ x
        member y∈ (here y≤q)          q∉ = ≤∨ˡ (<→≤₋′ y≤q λ y≡q → q∉ (subst (_∈ cover Q) y≡q y∈))
        member y∈ (there (here y≤x))  q∉ = ≤∨ʳ y≤x

      bc : BadCover
      bc = descend Q (lose q∈ ¬gq)

      result : Σ (Fin (suc n)) (λ q′ → q′ ∈ cover (BadCover.Q bc) × ¬ Good q′)
             → Σ (Fin (suc n)) λ q′ → HasOneLowerCover q′ × ¬ Good q′ × a C q′
      result (q′ , q′∈ , ¬gq′) =
        q′ , All.lookup (irreducibles (BadCover.Q bc)) q′∈ , ¬gq′
        , Theorem2-60.theorem-2-60 one (BadCover.Q bc) (BadCover.minimalIn bc) q′∈

  -- A bad join irreducible element starts a C-path of any length.
  bad-path : ∀ k {a} → HasOneLowerCover a → ¬ Good a → Σ (Fin (suc n)) λ c → Path _C_ k a c
  bad-path zero     one ¬g = _ , []
  bad-path (suc k)  one ¬g = extend (bad→C one ¬g)
    where
    extend : Σ (Fin (suc n)) (λ q → HasOneLowerCover q × ¬ Good q × _ C q) → Σ (Fin (suc n)) λ c → Path _C_ (suc k) _ c
    extend (q , iq , ¬gq , aCq) = proj₁ (bad-path k iq ¬gq) , aCq ∷ proj₂ (bad-path k iq ¬gq)

  -- Lemma 2.62, the other direction: with no C-cycle, the lattice is lower bounded.
  noCCycle→lowerBounded : (∀ {k} → ¬ CCycle k) → LowerBounded
  noCCycle→lowerBounded noC (a , cyc) = close (path→cycle (proj₂ (bad-path (suc n) (closure-target cyc) (cycle→bad cyc))))
    where
    close : Σ (Fin (suc n)) (λ c → Σ ℕ λ l → Path _C_ (suc l) c c) → ⊥
    close (c , l , q) = noC (c , q)
```

#### Corollary 2.65

A Cᵈ-cycle, a C-cycle of the dual tables, is carried by `κᵈ` to a C-cycle of the
original (Lemma 2.63, as [Lattices.Nation.Cycle][] maps paths), so a lattice
with no C-cycle has none in its dual either, and is lower bounded on both
sides: bounded, in the sense of [Lattices.Bounded.Finite][].

```agda
module BoundedDuality {n : ℕ} {_∧_ _∨_ : Fin (suc n) → Fin (suc n) → Fin (suc n)}
                      (laws : LatticeTableLaws _∧_ _∨_)
                      (sd : IsSemidistributive (tableLattice _∧_ _∨_ laws)) where

  open Kappa laws sd
  open KappaDuality laws sd using ( module ᵈ )
  module ℬ   = Bounded laws sd
  module ℬᵈ  = Bounded (dual-laws laws) (swap sd)
  module ᴹ   = CycleMap (dual-laws laws) (swap sd)

  -- No C-cycle gives no Cᵈ-cycle.
  noC→noCᵈ : (∀ {k} → ¬ ℬ.CCycle k) → ∀ {k} → ¬ ℬᵈ.CCycle k
  noC→noCᵈ noC (b , q) = noC (ᵈ.κ b , ᴹ.map-κ q)

  -- Corollary 2.65: a finite semidistributive lattice with no C-cycle is bounded.
  noCCycle→bounded : (∀ {k} → ¬ ℬ.CCycle k) → Bounded laws
  noCCycle→bounded noC = ℬ.noCCycle→lowerBounded noC , ℬᵈ.noCCycle→lowerBounded (noC→noCᵈ noC)
```
