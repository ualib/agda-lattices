---
layout: default
file: "src/Lattices/Free/Canonical/Joinands.lagda.md"
title: "Lattices.Free.Canonical.Joinands module"
date: "2026-10-11"
author: "the agda-algebras development team"
---

### Canonical joinands

This is the [Lattices.Free.Canonical.Joinands][] module of the [agda-lattices][] library.

Let `w` be an element of the free lattice.  If the canonical form of `w` is a join
`t₁ ∨ ⋯ ∨ tₙ`, the elements the `tᵢ` represent are the *canonical joinands* of
`w`; otherwise (`w` is join irreducible) its only canonical joinand is `w` itself
([Freese, Ježek, and Nation (1995)][], Section I.3).  The canonical meetands are
dual.  Theorem 1.19 says that the canonical joinands refine every join
representation of `w`: if `w = u₁ ∨ ⋯ ∨ uₘ`, then every canonical joinand of `w`
lies below some `uⱼ`.  In this sense the canonical join representation is the
best way to write `w` as a join, and the theorem is the form in which canonical
forms are used: semidistributivity of free lattices is a short consequence, and
so are the later arithmetic of free lattices and the theory of their
sublattices.

Here `canonicalJoinands w`{.AgdaFunction} is the list of the lattice terms
embedded from the joinands of the canonical form computed by
[Lattices.Free.Canonical.Algorithm][], and Theorem 1.19
(`canonicalJoinands-refine`{.AgdaFunction}) is Lemma 1.16 of
[Lattices.Free.Canonical.Uniqueness][] read for that list.  The module closes
with Theorem 1.17 read through the same lists: equal elements have the same
canonical joinands, up to order and equality in the free lattice
(`canonicalJoinands-≈ˡ`{.AgdaFunction}), so that "`u` is a canonical joinand
of `w`", read up to equality, depends only on the elements `u` and `w`
(`canonicalJoinand-resp`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical.Joinands where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Binary.Permutation.Propositional
                                                   using ( _↭_ ; ↭-refl ; ↭-sym ; ↭-trans )
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
                                                   using ( Any-resp-↭ )
                                                   renaming ( map⁺ to ↭-map⁺ )
open import Data.List.Relation.Binary.Pointwise    using ( Pointwise ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( refl ; sym ; subst )

import Data.List.Relation.Binary.Pointwise as Pointwise

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm
  using  ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; CMand ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ≈ʷ-refl
         ; ≈ʷ-sym ; ≈ʷ-trans ; ⋁⁺ ; ⋀⁺ ; gen-⋁⁺-prime ; ⋀⁺-gen-below ; ⋁ᴶ-upper ; ⋁ᴶ-least
         ; ⋀ᴹ-lower ; ⋀ᴹ-greatest ; W-list-ᴹ⁺ ; W-list-⁺ᴶ ; IsCanonical ; cjoin ; cmeet
         ; asListJ ; asListM ; joinandsOf ; meetandsOf ; joinandsOf-sound ; meetandsOf-sound )
open import Lattices.Free.Canonical.Uniqueness
  using  ( ⋁ᴶ-refines ; ⋀ᴹ-refines ; module Antichains ; _≈ᶜ_ ; gen≈ ; join≈ ; meet≈
         ; ≈ᶜ⇒≈ʷ ; ≈ᶜᴶs⇒≈ʷ ; ≈ᶜᴹs⇒≈ʷ ; ≈ʷ⇒≈ᶜ ; PW-↭ )
open import Lattices.Free.Term     using ( LatTerm )
open import Lattices.Free.Whitman  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans )

private variable
  χ : Level
  X : Type χ
```
-->

#### Refinement for a canonical term

Theorem 1.19 is first proved for an arbitrary canonical term `C` and a join
representation of the element it represents (`joinands-refine`{.AgdaFunction}),
by cases on the shape of `C`.  The joinand of a generator is the generator, which
is join prime.  The joinands of a canonical join are covered by Lemma 1.16.  The
joinand of a canonical meet `⋀ⱼ tⱼ` is the meet itself: by Whitman's condition it
lies below some `uⱼ`, or some meetand `tⱼ` lies below the join of the `uⱼ`,
which is the meet itself, hence below every meetand; and no member of an
antichain of two or more lies below all the others.  `meetands-refine`{.AgdaFunction}
is the dual.

```agda
module _ {X : Type χ} where
  open Antichains {A = CJand X} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand X} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  joinands-refine : (C : CTerm X) → IsCanonical C → {u : LatTerm X} {us : List (LatTerm X)}
                  → ⌊ C ⌋ ≈ʷ ⋁⁺ u us
                  → ∀ {a} → a ∈ asListJ (joinandsOf C) → Any (⌊ a ⌋ᴶ ≤ʷ_) (u ∷ us)
  joinands-refine (genᶜ _)     _                  (p , _)  (here refl)  = gen-⋁⁺-prime p
  joinands-refine (joinᶜ _ _)  (cjoin _ _ _ c4)   e        a∈           = ⋁ᴶ-refines c4 e a∈
  joinands-refine (meetᶜ _ _)  (cmeet ne _ ac _)  (p , q)  (here refl)  with W-list-ᴹ⁺ p
  ... | inj₁ r = let (_ , m∈ , m≤) = find r
                 in ⊥-elim (no-minᴹ ac ne m∈ (λ v∈ → ≤ʷ-trans m≤ (≤ʷ-trans q (⋀ᴹ-lower v∈))))
  ... | inj₂ r = r

  meetands-refine : (C : CTerm X) → IsCanonical C → {u : LatTerm X} {us : List (LatTerm X)}
                  → ⌊ C ⌋ ≈ʷ ⋀⁺ u us
                  → ∀ {a} → a ∈ asListM (meetandsOf C) → Any (_≤ʷ ⌊ a ⌋ᴹ) (u ∷ us)
  meetands-refine (genᶜ _)     _                  (_ , q)  (here refl)  = ⋀⁺-gen-below q
  meetands-refine (meetᶜ _ _)  (cmeet _ _ _ c4)   e        a∈           = ⋀ᴹ-refines c4 e a∈
  meetands-refine (joinᶜ _ _)  (cjoin ne _ ac _)  (p , q)  (here refl)  with W-list-⁺ᴶ q
  ... | inj₁ r = r
  ... | inj₂ r = let (_ , j∈ , ≤j) = find r
                 in ⊥-elim (no-maxᴶ ac ne j∈ (λ v∈ → ≤ʷ-trans (⋁ᴶ-upper v∈) (≤ʷ-trans p ≤j)))
```

#### Theorem 1.19

`canonicalJoinands w`{.AgdaFunction} and `canonicalMeetands w`{.AgdaFunction} are the
lattice terms of the joinands and meetands of the canonical form of `w`.  Each
canonical joinand lies below `w` (`canonicalJoinands-upper`{.AgdaFunction}), and
`w` lies below every common upper bound of them
(`canonicalJoinands-least`{.AgdaFunction}), so `w` is their join; dually for the
canonical meetands.  Theorem 1.19 (`canonicalJoinands-refine`{.AgdaFunction}) and
its dual (`canonicalMeetands-refine`{.AgdaFunction}) are the refinement lemmas
above, applied to the canonical form of `w`, which is canonical and represents `w`.

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  canonicalJoinands : LatTerm X → List (LatTerm X)
  canonicalJoinands w = map ⌊_⌋ᴶ (asListJ (joinandsOf (canonical w)))

  canonicalMeetands : LatTerm X → List (LatTerm X)
  canonicalMeetands w = map ⌊_⌋ᴹ (asListM (meetandsOf (canonical w)))

  canonicalJoinands-upper : {w c : LatTerm X} → c ∈ canonicalJoinands w → c ≤ʷ w
  canonicalJoinands-upper {w} c∈ with ∈-map⁻ ⌊_⌋ᴶ c∈
  ... | _ , a∈ , refl =
    ≤ʷ-trans (⋁ᴶ-upper a∈)
             (subst (_≤ʷ w) (sym (joinandsOf-sound (canonical w))) (proj₁ (canonical-sound w)))

  canonicalJoinands-least : {w z : LatTerm X} → (∀ {c} → c ∈ canonicalJoinands w → c ≤ʷ z) → w ≤ʷ z
  canonicalJoinands-least {w} f =
    ≤ʷ-trans (proj₂ (canonical-sound w))
             (subst (_≤ʷ _) (joinandsOf-sound (canonical w)) (⋁ᴶ-least λ a∈ → f (∈-map⁺ ⌊_⌋ᴶ a∈)))

  canonicalMeetands-lower : {w c : LatTerm X} → c ∈ canonicalMeetands w → w ≤ʷ c
  canonicalMeetands-lower {w} c∈ with ∈-map⁻ ⌊_⌋ᴹ c∈
  ... | _ , a∈ , refl =
    ≤ʷ-trans (proj₂ (canonical-sound w))
             (subst (_≤ʷ _) (meetandsOf-sound (canonical w)) (⋀ᴹ-lower a∈))

  canonicalMeetands-greatest : {w z : LatTerm X} → (∀ {c} → c ∈ canonicalMeetands w → z ≤ʷ c)
                             → z ≤ʷ w
  canonicalMeetands-greatest {w} f =
    ≤ʷ-trans (subst (_ ≤ʷ_) (meetandsOf-sound (canonical w)) (⋀ᴹ-greatest λ a∈ → f (∈-map⁺ ⌊_⌋ᴹ a∈)))
             (proj₁ (canonical-sound w))

  canonicalJoinands-refine : {w u : LatTerm X} {us : List (LatTerm X)} → w ≈ʷ ⋁⁺ u us
                           → ∀ {c} → c ∈ canonicalJoinands w → Any (c ≤ʷ_) (u ∷ us)
  canonicalJoinands-refine {w} e c∈ with ∈-map⁻ ⌊_⌋ᴶ c∈
  ... | _ , a∈ , refl =
    joinands-refine (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e) a∈

  canonicalMeetands-refine : {w u : LatTerm X} {us : List (LatTerm X)} → w ≈ʷ ⋀⁺ u us
                           → ∀ {c} → c ∈ canonicalMeetands w → Any (_≤ʷ c) (u ∷ us)
  canonicalMeetands-refine {w} e c∈ with ∈-map⁻ ⌊_⌋ᴹ c∈
  ... | _ , a∈ , refl =
    meetands-refine (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e) a∈
```

#### Theorem 1.17, read through the lists

Theorem 1.17 (`≈ʷ⇒≈ᶜ`{.AgdaFunction} of [Lattices.Free.Canonical.Uniqueness][])
says that two canonical terms of one element differ only in the order of
children, at every level.  Read for the lists of canonical joinands, it says
that two equal elements have the same canonical joinands up to order and
equality in the free lattice.  The relation is `_≈ˡ_`{.AgdaFunction}, built as
`_≈ᶜ_`{.AgdaDatatype} is: some permutation (`_↭_`{.AgdaDatatype}) of the first
list is pointwise equal (`Pointwise`{.AgdaDatatype} `_≈ʷ_`) to the second.  It
is an equivalence (`≈ˡ-refl`{.AgdaFunction}, `≈ˡ-sym`{.AgdaFunction},
`≈ˡ-trans`{.AgdaFunction}), the symmetry and transitivity moving a permutation
across a pointwise relation with `PW-↭`{.AgdaFunction}.

```agda
-- Two lists of lattice terms that agree up to order and equality in the free lattice.
infix 4 _≈ˡ_

_≈ˡ_ : {X : Type χ} → List (LatTerm X) → List (LatTerm X) → Type χ
us ≈ˡ vs = Σ[ zs ∈ List _ ] us ↭ zs × Pointwise _≈ʷ_ zs vs

module _ {X : Type χ} where
  private
    PW-≈ʷ-refl : (us : List (LatTerm X)) → Pointwise _≈ʷ_ us us
    PW-≈ʷ-refl []        = []
    PW-≈ʷ-refl (_ ∷ us)  = ≈ʷ-refl ∷ PW-≈ʷ-refl us

  -- The relation is an equivalence.
  ≈ˡ-refl : {us : List (LatTerm X)} → us ≈ˡ us
  ≈ˡ-refl {us} = us , ↭-refl , PW-≈ʷ-refl us

  ≈ˡ-sym : {us vs : List (LatTerm X)} → us ≈ˡ vs → vs ≈ˡ us
  ≈ˡ-sym (_ , p , q) = PW-↭ (Pointwise.symmetric ≈ʷ-sym q) (↭-sym p)

  ≈ˡ-trans : {us vs ws : List (LatTerm X)} → us ≈ˡ vs → vs ≈ˡ ws → us ≈ˡ ws
  ≈ˡ-trans (_ , p , q) (_ , p' , q') =
    let (ys , p'' , q'') = PW-↭ q p'
    in ys , ↭-trans p p'' , Pointwise.transitive ≈ʷ-trans q'' q'
```

Membership up to equality is invariant under the relation
(`Any-resp-≈ˡ`{.AgdaFunction}): a witness moves along the permutation, and then
across the pointwise equality.

```agda
  -- A member up to equality of one list is a member up to equality of the other.
  Any-resp-≈ˡ : {u : LatTerm X} {us vs : List (LatTerm X)} → us ≈ˡ vs
              → Any (u ≈ʷ_) us → Any (u ≈ʷ_) vs
  Any-resp-≈ˡ (_ , p , q) i = across q (Any-resp-↭ p i)
    where
    across : {u : LatTerm X} {zs vs : List (LatTerm X)} → Pointwise _≈ʷ_ zs vs
           → Any (u ≈ʷ_) zs → Any (u ≈ʷ_) vs
    across (r ∷ _)  (here e)   = here (≈ʷ-trans e r)
    across (_ ∷ q)  (there i)  = there (across q i)
```

Two canonical terms related by `_≈ᶜ_`{.AgdaDatatype} have related lists of
joinands (`≈ᶜ⇒joinands-≈ˡ`{.AgdaFunction}), by cases on the relation: two
generators are equal; two joins have permuted, pointwise related children, and
`≈ᶜᴶs⇒≈ʷ`{.AgdaFunction} turns the pointwise relation into pointwise equality
of the embedded children; and two meets are each their own only joinand, equal
by `≈ᶜ⇒≈ʷ`{.AgdaFunction}.  Meetands are dual
(`≈ᶜ⇒meetands-≈ˡ`{.AgdaFunction}).

```agda
  -- Related canonical terms have related joinands, and related meetands.
  ≈ᶜ⇒joinands-≈ˡ : {C D : CTerm X} → C ≈ᶜ D
                 → map ⌊_⌋ᴶ (asListJ (joinandsOf C)) ≈ˡ map ⌊_⌋ᴶ (asListJ (joinandsOf D))
  ≈ᶜ⇒joinands-≈ˡ (gen≈ refl)     = ≈ˡ-refl
  ≈ᶜ⇒joinands-≈ˡ (join≈ p q)     = _ , ↭-map⁺ ⌊_⌋ᴶ p , Pointwise.map⁺ ⌊_⌋ᴶ ⌊_⌋ᴶ (≈ᶜᴶs⇒≈ʷ q)
  ≈ᶜ⇒joinands-≈ˡ e@(meet≈ _ _)   = _ , ↭-refl , ≈ᶜ⇒≈ʷ e ∷ []

  ≈ᶜ⇒meetands-≈ˡ : {C D : CTerm X} → C ≈ᶜ D
                 → map ⌊_⌋ᴹ (asListM (meetandsOf C)) ≈ˡ map ⌊_⌋ᴹ (asListM (meetandsOf D))
  ≈ᶜ⇒meetands-≈ˡ (gen≈ refl)     = ≈ˡ-refl
  ≈ᶜ⇒meetands-≈ˡ e@(join≈ _ _)   = _ , ↭-refl , ≈ᶜ⇒≈ʷ e ∷ []
  ≈ᶜ⇒meetands-≈ˡ (meet≈ p q)     = _ , ↭-map⁺ ⌊_⌋ᴹ p , Pointwise.map⁺ ⌊_⌋ᴹ ⌊_⌋ᴹ (≈ᶜᴹs⇒≈ʷ q)
```

So the joinands of any canonical term of `w` are the canonical joinands of `w`
up to order and equality (`joinands-≈ˡ`{.AgdaFunction}), by Theorem 1.17 applied
to that term and the computed canonical form.  This is the list form of
Theorem 1.17: if `w ≈ʷ w'`, then `canonicalJoinands w ≈ˡ canonicalJoinands w'`
(`canonicalJoinands-≈ˡ`{.AgdaFunction}), and dually for meetands
(`canonicalMeetands-≈ˡ`{.AgdaFunction}).  Its corollary
(`canonicalJoinand-resp`{.AgdaFunction}, `canonicalMeetand-resp`{.AgdaFunction})
is the reading of "`u` is a canonical joinand of `w`" that the rest of the
development uses, `Any (u ≈ʷ_) (canonicalJoinands w)`: it holds of `w` exactly
when it holds of any element equal to `w`.

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- The joinands of any canonical term of w are the canonical joinands of w.
  joinands-≈ˡ : (C : CTerm X) → IsCanonical C → {w : LatTerm X} → ⌊ C ⌋ ≈ʷ w
              → map ⌊_⌋ᴶ (asListJ (joinandsOf C)) ≈ˡ canonicalJoinands _≟_ w
  joinands-≈ˡ C cC {w} e =
    ≈ᶜ⇒joinands-≈ˡ (≈ʷ⇒≈ᶜ C (canonical w) cC (canonical-isCanonical w)
                           (≈ʷ-trans e (≈ʷ-sym (canonical-sound w))))

  meetands-≈ˡ : (C : CTerm X) → IsCanonical C → {w : LatTerm X} → ⌊ C ⌋ ≈ʷ w
              → map ⌊_⌋ᴹ (asListM (meetandsOf C)) ≈ˡ canonicalMeetands _≟_ w
  meetands-≈ˡ C cC {w} e =
    ≈ᶜ⇒meetands-≈ˡ (≈ʷ⇒≈ᶜ C (canonical w) cC (canonical-isCanonical w)
                           (≈ʷ-trans e (≈ʷ-sym (canonical-sound w))))

  -- Theorem 1.17, list form: equal elements have the same canonical joinands.
  canonicalJoinands-≈ˡ : {w w' : LatTerm X} → w ≈ʷ w'
                       → canonicalJoinands _≟_ w ≈ˡ canonicalJoinands _≟_ w'
  canonicalJoinands-≈ˡ {w} e =
    joinands-≈ˡ (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e)

  canonicalMeetands-≈ˡ : {w w' : LatTerm X} → w ≈ʷ w'
                       → canonicalMeetands _≟_ w ≈ˡ canonicalMeetands _≟_ w'
  canonicalMeetands-≈ˡ {w} e =
    meetands-≈ˡ (canonical w) (canonical-isCanonical w) (≈ʷ-trans (canonical-sound w) e)

  -- Being a canonical joinand, up to equality, depends only on the element.
  canonicalJoinand-resp : {w w' u : LatTerm X} → w ≈ʷ w'
                        → Any (u ≈ʷ_) (canonicalJoinands _≟_ w) → Any (u ≈ʷ_) (canonicalJoinands _≟_ w')
  canonicalJoinand-resp e = Any-resp-≈ˡ (canonicalJoinands-≈ˡ e)

  canonicalMeetand-resp : {w w' u : LatTerm X} → w ≈ʷ w'
                        → Any (u ≈ʷ_) (canonicalMeetands _≟_ w) → Any (u ≈ʷ_) (canonicalMeetands _≟_ w')
  canonicalMeetand-resp e = Any-resp-≈ˡ (canonicalMeetands-≈ˡ e)
```
