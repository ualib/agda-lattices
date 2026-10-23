---
layout: default
file: "src/Lattices/Free/Canonical/JoinIrreducible.lagda.md"
title: "Lattices.Free.Canonical.JoinIrreducible module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Join irreducible elements and Theorem 1.20

This is the [Lattices.Free.Canonical.JoinIrreducible][] module of the [agda-lattices][] library.

An element `u` of a lattice is *join irreducible* when `u = a ∨ b` implies `u = a`
or `u = b` ([Freese, Ježek, and Nation (1995)][], Section I.1).  In a free
lattice the join irreducible elements are exactly those whose canonical form is
a generator or a meet, and Theorem 1.20 characterizes the canonical joinands of
an element `w` among them lattice theoretically, with no mention of terms: a join
irreducible `u` is a canonical joinand of `w` if and only if there is an `a` with
`w = u ∨ a` and `v ∨ a < w` for every `v < u`.  This is the form in which the
book's Chapters VI to X use canonical forms, and this module proves it.

The book's proof passes over two corners, which the statements here make
explicit.  Its forward direction takes `a` to be the join of the canonical
joinands other than `u`, which is empty when `w` is join irreducible; then any
`a` strictly below `w` serves, and when nothing lies strictly below `w` the
element `w` itself serves, vacuously.  Its backward direction takes `v` to be the
join of the canonical joinands below `u`, which is empty when there is none;
then `w = a`, and the condition on the elements strictly below `u` says nothing
when there is none.  That second corner is a genuine exception: in `FL(X)` for a
finite `X` the least element `⋀ X` is join irreducible in the sense of the
definition, the book's convention that the least element of a *finite* lattice
is not join irreducible does not reach the infinite `FL(X)`, and the theorem
fails for it, as [Lattices.Examples.FreeLattice3][] certifies
(`⊥₃-witness`{.AgdaFunction}, `⊥₃-not-joinand`{.AgdaFunction}).  So the
theorem is stated with the hypothesis that some element lies strictly below
`u` (`canonicalJoinand⇔witness`{.AgdaFunction}), which holds for every join
irreducible `u` other than the least element when `X` is finite and for every
`u` when `X` is infinite; the backward direction is also stated exactly, as a
dichotomy (`witness⇒joinand-or-minimal`{.AgdaFunction}); and the forward
direction for a join reducible `w` needs no hypothesis at all
(`joinand-witness-join`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical.JoinIrreducible where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; filter )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ ; ∈-filter⁺ ; ∈-filter⁻ )
open import Data.List.Relation.Unary.All           using ( head ; lookup )
open import Data.List.Relation.Unary.AllPairs      using ( _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
                                                   renaming ( map to ⊎-map )
open import Function                               using ( _⇔_ ; mk⇔ ; id ; _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; subst )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; map′ ; ¬? )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm
  using  ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; CMand ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⋁ᴶ ; ⋁⁺ ; ⋁⁺-upper
         ; ⋁⁺-least ; ⋁ᴶ-upper ; ⋁ᴶ-least ; _≰ʷ_ ; IsCanonical ; cjoin ; asListJ
         ; joinandsOf ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans )
open import Lattices.Free.Canonical.Joinands
  using  ( joinands-refine ; canonicalJoinands ; canonicalJoinands-least
         ; canonicalJoinands-refine )
open import Lattices.Free.Canonical.Uniqueness
  using  ( ⋁ᴶ-refines ; ⋁ᴶ-refinesᴶ ; antichain-≤ )
open import Lattices.Free.Term     using ( LatTerm ; _∨̇_ )
open import Lattices.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨̇-upperˡ ; ∨̇-upperʳ ; module Decision )

private variable
  χ : Level
  X : Type χ
  x : X
  s t u v w a : LatTerm X
  mh : CMand X
  mt : List (CMand X)
```
-->

#### The strict order and join irreducibility

`s <ʷ t`{.AgdaFunction} says that `s` lies strictly below `t` in the free
lattice: below it, and not above it.  The strict order moves along equality on
the right (`<ʷ-≈ʷ`{.AgdaFunction}).  `IsJoinIrreducible u`{.AgdaFunction} is the
book's definition, read in `FL X`: whenever `u` equals a join of two elements, it
equals one of them.  It depends only on the element
(`IsJoinIrreducible-resp`{.AgdaFunction}), and it extends to joins of lists
(`joinIrreducible-⋁⁺`{.AgdaFunction}): a join irreducible element equal to the
join of a nonempty list equals a member of the list.

```agda
infix 4 _<ʷ_

_<ʷ_ : {X : Type χ} → LatTerm X → LatTerm X → Type χ
s <ʷ t = (s ≤ʷ t) × (t ≰ʷ s)

<ʷ-≈ʷ : s <ʷ t → t ≈ʷ u → s <ʷ u
<ʷ-≈ʷ (s≤t , t≰s) (t≤u , u≤t) = ≤ʷ-trans s≤t t≤u , λ u≤s → t≰s (≤ʷ-trans t≤u u≤s)

-- An element is join irreducible when it equals a joinand of every join it equals.
IsJoinIrreducible : {X : Type χ} → LatTerm X → Type χ
IsJoinIrreducible u = ∀ a b → u ≈ʷ a ∨̇ b → (u ≈ʷ a) ⊎ (u ≈ʷ b)

IsJoinIrreducible-resp : u ≈ʷ v → IsJoinIrreducible u → IsJoinIrreducible v
IsJoinIrreducible-resp e ji a b e' =
  ⊎-map (≈ʷ-trans (≈ʷ-sym e)) (≈ʷ-trans (≈ʷ-sym e)) (ji a b (≈ʷ-trans e e'))

joinIrreducible-⋁⁺ : IsJoinIrreducible u → {v : LatTerm X} {vs : List (LatTerm X)}
                   → u ≈ʷ ⋁⁺ v vs → Any (u ≈ʷ_) (v ∷ vs)
joinIrreducible-⋁⁺ ji {vs = []}     e = here e
joinIrreducible-⋁⁺ ji {vs = _ ∷ _}  e = [ here , there ∘ joinIrreducible-⋁⁺ ji ]′ (ji _ _ e)
```

#### Join irreducibility and the shape of the canonical form

A canonical term that is a generator or a meet (`NotJoinᶜ`{.AgdaDatatype})
represents a join irreducible element (`notJoin-irreducible`{.AgdaFunction}): it
is its own only joinand, so by Theorem 1.19 (`joinands-refine`{.AgdaFunction}) it
lies below one side of any join it equals, and it lies above both sides.  A
canonical join represents a join reducible element
(`join-reducible`{.AgdaFunction}): it is the join of its first child and the join
of the rest, and if it equaled either, Lemma 1.16 (`⋁ᴶ-refinesᴶ`{.AgdaFunction})
would put one child below another, against condition 3.

```agda
data NotJoinᶜ {X : Type χ} : CTerm X → Type χ where
  notJoin-genᶜ   : NotJoinᶜ (genᶜ x)
  notJoin-meetᶜ  : NotJoinᶜ (meetᶜ mh mt)

notJoinᶜ? : (C : CTerm X) → Dec (NotJoinᶜ C)
notJoinᶜ? (genᶜ _)     = yes notJoin-genᶜ
notJoinᶜ? (meetᶜ _ _)  = yes notJoin-meetᶜ
notJoinᶜ? (joinᶜ _ _)  = no λ ()

private
  -- An element below one of two joinands it is the join of equals that joinand.
  joinand-equal : w ≈ʷ a ∨̇ t → Any (w ≤ʷ_) (a ∷ t ∷ []) → (w ≈ʷ a) ⊎ (w ≈ʷ t)
  joinand-equal e (here p)          = inj₁ (p , ≤ʷ-trans ∨̇-upperˡ (proj₂ e))
  joinand-equal e (there (here p))  = inj₂ (p , ≤ʷ-trans ∨̇-upperʳ (proj₂ e))
  joinand-equal e (there (there ()))

  -- A witness in a one-element list is about that element.
  only : {A : Type χ} {P : A → Type χ} {y : A} → Any P (y ∷ []) → P y
  only (here p)   = p
  only (there ())

-- A generator or a canonical meet is join irreducible.
notJoin-irreducible : (C : CTerm X) → IsCanonical C → NotJoinᶜ C → IsJoinIrreducible ⌊ C ⌋
notJoin-irreducible (genᶜ _)     cC notJoin-genᶜ   a b e =
  joinand-equal e (joinands-refine (genᶜ _) cC e (here refl))
notJoin-irreducible (meetᶜ _ _)  cC notJoin-meetᶜ  a b e =
  joinand-equal e (joinands-refine (meetᶜ _ _) cC e (here refl))

-- A canonical join is join reducible.
join-reducible : {h : CJand X} {t : List (CJand X)} → IsCanonical (joinᶜ h t)
               → ¬ IsJoinIrreducible (⋁ᴶ h t)
join-reducible         (cjoin {jt = []}      ne _ _         _)   _  = ne refl
join-reducible {h = h} (cjoin {jt = a ∷ as}  _  _ (Ih ∷ _)  c4)  ji
  with ji ⌊ h ⌋ᴶ (⋁ᴶ a as) ≈ʷ-refl
... | inj₁ e = ⊥-elim (proj₂ (head Ih) (only (⋁ᴶ-refinesᴶ {h' = h} {t' = []} c4 e (there (here refl)))))
... | inj₂ e = let (_ , b∈ , h≤b) = find (⋁ᴶ-refinesᴶ {h' = a} {t' = as} c4 e (here refl))
               in ⊥-elim (proj₁ (lookup Ih b∈) h≤b)
```

For the computed canonical form the two facts combine into a characterization
(`joinIrreducible⇔notJoin`{.AgdaFunction}): an element is join irreducible exactly
when its canonical form is a generator or a meet.  Since the shape of a term is
decidable, so is join irreducibility (`isJoinIrreducible?`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  joinIrreducible⇒notJoin : (u : LatTerm X) → IsJoinIrreducible u → NotJoinᶜ (canonical u)
  joinIrreducible⇒notJoin u ji with canonical u | canonical-isCanonical u | canonical-sound u
  ... | genᶜ _     | _   | _ = notJoin-genᶜ
  ... | meetᶜ _ _  | _   | _ = notJoin-meetᶜ
  ... | joinᶜ _ _  | cC  | e = ⊥-elim (join-reducible cC (IsJoinIrreducible-resp (≈ʷ-sym e) ji))

  notJoin⇒joinIrreducible : (u : LatTerm X) → NotJoinᶜ (canonical u) → IsJoinIrreducible u
  notJoin⇒joinIrreducible u nj =
    IsJoinIrreducible-resp (canonical-sound u)
                           (notJoin-irreducible (canonical u) (canonical-isCanonical u) nj)

  -- An element is join irreducible exactly when its canonical form is a generator or a meet.
  joinIrreducible⇔notJoin : (u : LatTerm X) → IsJoinIrreducible u ⇔ NotJoinᶜ (canonical u)
  joinIrreducible⇔notJoin u = mk⇔ (joinIrreducible⇒notJoin u) (notJoin⇒joinIrreducible u)

  isJoinIrreducible? : (u : LatTerm X) → Dec (IsJoinIrreducible u)
  isJoinIrreducible? u =
    map′ (notJoin⇒joinIrreducible u) (joinIrreducible⇒notJoin u) (notJoinᶜ? (canonical u))
```

#### The condition of Theorem 1.20

`JoinandWitness w u a`{.AgdaFunction} is the condition of the theorem on the
element `a`: `w` is the join of `u` and `a`, and `v ∨ a` lies strictly below `w`
for every `v` strictly below `u`.  Theorem 1.20 says that, for `u` join
irreducible, some `a` witnesses `u` in this sense exactly when `u` is a canonical
joinand of `w`, read up to equality as `Any (u ≈ʷ_) (canonicalJoinands w)`
(the reading of [Lattices.Free.Canonical.Joinands][]).

```agda
JoinandWitness : {X : Type χ} → LatTerm X → LatTerm X → LatTerm X → Type χ
JoinandWitness w u a = (w ≈ʷ u ∨̇ a) × (∀ v → v <ʷ u → v ∨̇ a <ʷ w)
```

#### The forward direction

Three lemmas cover the three cases of the forward direction.  The first is the
book's: for a canonical join `w = ⋁ (h ∷ t)` and a canonical joinand `u` of it,
the join of the *other* canonical joinands is a witness
(`joinand-witness-join`{.AgdaFunction}).  Here the others are the joinands not
equal to `u`, selected with the decision procedure for equality; since the
joinands form an antichain, that is every joinand but the one `u` equals, and
the list is not empty, because of the first two joinands at most one equals
`u`.  Then `w` is the join of `u` and the others, since every joinand is `u`
or among the others, and all lie below `w`.  And for `v` strictly below `u`,
if `w` lay below `v ∨ a`, Theorem 1.19 (`⋁ᴶ-refines`{.AgdaFunction}) would put
the joinand `u` equals below `v`, against `v < u`, or below another joinand,
which `antichain-≤`{.AgdaFunction} turns into equality with it, against the
choice of the others.

```agda
private
  -- Case on a list, keeping the equation.
  caseList : {A B : Type χ} (xs : List A) → (xs ≡ [] → B) → (∀ y ys → xs ≡ y ∷ ys → B) → B
  caseList []        n c = n refl
  caseList (y ∷ ys)  n c = c y ys refl

  -- Nothing is a member of the empty list.
  ∉[] : {A : Type χ} {c : A} → ¬ (c ∈ [])
  ∉[] ()

module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Decision _≟_ using ( _≤ʷ?_ ; _≈ʷ?_ )

  -- Theorem 1.20, forward, for a canonical join: the join of the other joinands is a witness.
  joinand-witness-join : (h : CJand X) (t : List (CJand X)) → IsCanonical (joinᶜ h t)
                       → ⋁ᴶ h t ≈ʷ w → Any (u ≈ʷ_) (map ⌊_⌋ᴶ (h ∷ t))
                       → Σ[ a ∈ LatTerm X ] JoinandWitness w u a
  joinand-witness-join h [] (cjoin ne _ _ _) _ _ = ⊥-elim (ne refl)
  joinand-witness-join {w = w} {u = u} h t@(a ∷ as) (cjoin _ _ ac@(Ih ∷ _) c4) e u∈ =
    caseList (filter P? us) (λ eq → ⊥-elim (none eq)) witness
    where
    us : List (LatTerm X)
    us = map ⌊_⌋ᴶ (h ∷ t)

    P? : (c : LatTerm X) → Dec (¬ (u ≈ʷ c))
    P? c = ¬? (u ≈ʷ? c)

    -- Every joinand lies below w, and u does.
    member-≤ : {c : LatTerm X} → c ∈ us → c ≤ʷ w
    member-≤ c∈ = let (_ , x∈ , eq) = ∈-map⁻ ⌊_⌋ᴶ {xs = h ∷ t} c∈
                  in subst (_≤ʷ w) (sym eq) (≤ʷ-trans (⋁ᴶ-upper x∈) (proj₁ e))

    u≤w : u ≤ʷ w
    u≤w = let (_ , c∈ , u≈c) = find u∈ in ≤ʷ-trans (proj₁ u≈c) (member-≤ c∈)

    -- Of the first two joinands, one is not u.
    other : Σ[ m ∈ LatTerm X ] m ∈ us × ¬ (u ≈ʷ m)
    other with u ≈ʷ? ⌊ h ⌋ᴶ
    ... | yes u≈h  = ⌊ a ⌋ᴶ , there (here refl)
                   , λ u≈a → proj₂ (head Ih) (≤ʷ-trans (proj₂ u≈a) (proj₁ u≈h))
    ... | no  u≉h  = ⌊ h ⌋ᴶ , here refl , u≉h

    none : ¬ (filter P? us ≡ [])
    none eq = ∉[] (subst (proj₁ other ∈_) eq (∈-filter⁺ P? (proj₁ (proj₂ other)) (proj₂ (proj₂ other))))

    witness : ∀ o os → filter P? us ≡ o ∷ os → Σ[ a ∈ LatTerm X ] JoinandWitness w u a
    witness o os eq = ⋁⁺ o os , (w≤ , ∨≤ u≤w a≤w) , strict
      where
      -- The others are joinands, none of them u; every joinand is u or one of the others.
      others-∈ : {c : LatTerm X} → c ∈ (o ∷ os) → c ∈ us × ¬ (u ≈ʷ c)
      others-∈ {c} c∈ = ∈-filter⁻ P? (subst (c ∈_) (sym eq) c∈)

      ∈-others : {c : LatTerm X} → c ∈ us → (u ≈ʷ c) ⊎ (c ∈ (o ∷ os))
      ∈-others {c} c∈ with u ≈ʷ? c
      ... | yes u≈c  = inj₁ u≈c
      ... | no  u≉c  = inj₂ (subst (c ∈_) eq (∈-filter⁺ P? c∈ u≉c))

      a≤w : ⋁⁺ o os ≤ʷ w
      a≤w = ⋁⁺-least λ c∈ → member-≤ (proj₁ (others-∈ c∈))

      w≤ : w ≤ʷ u ∨̇ ⋁⁺ o os
      w≤ = ≤ʷ-trans (proj₂ e) (⋁ᴶ-least {h = h} {t = t} λ x∈ →
             [ (λ u≈c → ≤ʷ-trans (proj₂ u≈c) ∨̇-upperˡ)
             , (λ c∈ → ≤ʷ-trans (⋁⁺-upper c∈) ∨̇-upperʳ) ]′ (∈-others (∈-map⁺ ⌊_⌋ᴶ x∈)))

      -- The joinand u equals, and its position among the children.
      c₀ : LatTerm X
      c₀ = proj₁ (find u∈)

      c₀∈ : c₀ ∈ us
      c₀∈ = proj₁ (proj₂ (find u∈))

      u≈c₀ : u ≈ʷ c₀
      u≈c₀ = proj₂ (proj₂ (find u∈))

      x₀ : CJand X
      x₀ = proj₁ (∈-map⁻ ⌊_⌋ᴶ {xs = h ∷ t} c₀∈)

      x₀∈ : x₀ ∈ (h ∷ t)
      x₀∈ = proj₁ (proj₂ (∈-map⁻ ⌊_⌋ᴶ {xs = h ∷ t} c₀∈))

      c₀≡ : c₀ ≡ ⌊ x₀ ⌋ᴶ
      c₀≡ = proj₂ (proj₂ (∈-map⁻ ⌊_⌋ᴶ {xs = h ∷ t} c₀∈))

      -- If x₀ lay below one of the others, u would equal it.
      not-below-other : {c : LatTerm X} → c ∈ (o ∷ os) → ¬ (⌊ x₀ ⌋ᴶ ≤ʷ c)
      not-below-other c∈ x₀≤c =
        let (c∈us , u≉c)   = others-∈ c∈
            (y , y∈ , c≡)  = ∈-map⁻ ⌊_⌋ᴶ {xs = h ∷ t} c∈us
            x₀≤y           = subst (⌊ x₀ ⌋ᴶ ≤ʷ_) c≡ x₀≤c
            y≤x₀           = antichain-≤ ≤ʷ-refl ac x₀∈ y∈ x₀≤y
        in u≉c (subst (u ≈ʷ_) (sym c≡)
                  ( ≤ʷ-trans (proj₁ u≈c₀) (subst (_≤ʷ ⌊ y ⌋ᴶ) (sym c₀≡) x₀≤y)
                  , ≤ʷ-trans y≤x₀ (subst (_≤ʷ u) c₀≡ (proj₂ u≈c₀)) ))

      strict : ∀ v → v <ʷ u → v ∨̇ ⋁⁺ o os <ʷ w
      strict v (v≤u , u≰v) = ∨≤ (≤ʷ-trans v≤u u≤w) a≤w , below
        where
        below : ¬ (w ≤ʷ v ∨̇ ⋁⁺ o os)
        below w≤va =
          [ (λ x₀≤v → u≰v (≤ʷ-trans (proj₁ u≈c₀) (subst (_≤ʷ v) (sym c₀≡) x₀≤v)))
          , (λ i → let (_ , c∈ , x₀≤c) = find i in not-below-other c∈ x₀≤c)
          ]′ (split (⋁ᴶ-refines c4 e' x₀∈))
          where
          e' : ⋁ᴶ h t ≈ʷ ⋁⁺ v (o ∷ os)
          e' = ≤ʷ-trans (proj₁ e) w≤va , ≤ʷ-trans (∨≤ (≤ʷ-trans v≤u u≤w) a≤w) (proj₂ e)

          split : {P : LatTerm X → Type χ} → Any P (v ∷ o ∷ os) → P v ⊎ Any P (o ∷ os)
          split (here p)   = inj₁ p
          split (there i)  = inj₂ i
```

The second lemma is the corner the book passes over: when `w` is join irreducible
and `u` equals `w`, any `a` strictly below `w` is a witness
(`joinand-witness-irreducible`{.AgdaFunction}), since for `v` strictly below `u`
the join `v ∨ a` is below `w` and, if `w` were below it, join irreducibility
would make `w` equal to `v` or to `a`, against the two strict inequalities.  The
third is the corner of that corner: when nothing lies strictly below `w`, the
element `w` itself is a witness, vacuously
(`joinand-witness-minimal`{.AgdaFunction}).

```agda
  -- Theorem 1.20, forward, for a join irreducible w: any element strictly below w is a witness.
  joinand-witness-irreducible : IsJoinIrreducible w → u ≈ʷ w → a <ʷ w → JoinandWitness w u a
  joinand-witness-irreducible {w = w} {u} {a} ji u≈w (a≤w , w≰a) =
    (≤ʷ-trans (proj₂ u≈w) ∨̇-upperˡ , ∨≤ (proj₁ u≈w) a≤w) , strict
    where
    strict : ∀ v → v <ʷ u → v ∨̇ a <ʷ w
    strict v (v≤u , u≰v) = ∨≤ (≤ʷ-trans v≤u (proj₁ u≈w)) a≤w , λ w≤va →
      [ (λ w≈v → u≰v (≤ʷ-trans (proj₁ u≈w) (proj₁ w≈v)))
      , (λ w≈a → w≰a (proj₁ w≈a)) ]′ (ji v a (w≤va , ∨≤ (≤ʷ-trans v≤u (proj₁ u≈w)) a≤w))

  -- When nothing lies strictly below w, w itself is a witness for u = w.
  joinand-witness-minimal : u ≈ʷ w → (∀ v → ¬ (v <ʷ w)) → JoinandWitness w u w
  joinand-witness-minimal u≈w minimal =
    (∨̇-upperʳ , ∨≤ (proj₁ u≈w) ≤ʷ-refl) , λ v v<u → ⊥-elim (minimal v (<ʷ-≈ʷ v<u u≈w))
```

Put together, the forward direction holds for every `u` with something strictly
below it (`joinand⇒witness`{.AgdaFunction}): if the canonical form of `w` is a
join, the first lemma applies; otherwise `w` is join irreducible, `u` equals
`w`, and the element below `u` is below `w`.  The case analysis is on the
computed canonical form of `w`, through a helper stated for any canonical term
`C` of `w`, whose joinand list is `canonicalJoinands w` when `C` is the computed
form.

```agda
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- Theorem 1.20, forward: a canonical joinand with something strictly below it has a witness.
  joinand⇒witness : v <ʷ u → Any (u ≈ʷ_) (canonicalJoinands _≟_ w) → Σ[ a ∈ LatTerm X ] JoinandWitness w u a
  joinand⇒witness {v = v} {u} {w} v<u = go (canonical w) (canonical-isCanonical w) (canonical-sound w)
    where
    go : (C : CTerm X) → IsCanonical C → ⌊ C ⌋ ≈ʷ w
       → Any (u ≈ʷ_) (map ⌊_⌋ᴶ (asListJ (joinandsOf C))) → Σ[ a ∈ LatTerm X ] JoinandWitness w u a
    go (joinᶜ h t)  cC e u∈          = joinand-witness-join h t cC e u∈
    go (genᶜ x)     cC e (here u≈c)  =
      v , joinand-witness-irreducible
            (IsJoinIrreducible-resp e (notJoin-irreducible (genᶜ x) cC notJoin-genᶜ))
            (≈ʷ-trans u≈c e) (<ʷ-≈ʷ v<u (≈ʷ-trans u≈c e))
    go (genᶜ x)     cC e (there ())
    go (meetᶜ h t)  cC e (here u≈c)  =
      v , joinand-witness-irreducible
            (IsJoinIrreducible-resp e (notJoin-irreducible (meetᶜ h t) cC notJoin-meetᶜ))
            (≈ʷ-trans u≈c e) (<ʷ-≈ʷ v<u (≈ʷ-trans u≈c e))
    go (meetᶜ h t)  cC e (there ())
```

#### The backward direction

The backward direction is proved exactly (`witness⇒joinand-or-minimal`{.AgdaFunction}):
for `u` join irreducible and `a` a witness, either `u` is a canonical joinand of
`w`, or `w` equals `a` and nothing lies strictly below `u`.  The proof is the
book's, with the empty join made explicit.  By Theorem 1.19
(`canonicalJoinands-refine`{.AgdaFunction}) every canonical joinand of `w` lies
below `u` or below `a`.  If none lies below `u`, then `w` lies below `a`, so `w`
equals `a`; and then an element `v` strictly below `u` would give `v ∨ a`
strictly below `w = a`, which is absurd, so there is none.  Otherwise let `v` be
the join of the canonical joinands below `u`, selected with the decision
procedure for the order.  Then `w = v ∨ a`, because every canonical joinand lies
below `v` or below `a`, and `v` and `a` lie below `w`.  So `v ∨ a` is not strictly
below `w`, so `v` is not strictly below `u`; since `v` lies below `u`, this
says `u` lies below `v` (the decision procedure settles the double negation), so
`u` equals `v`, and join irreducibility picks the canonical joinand that `u`
equals.

```agda
  -- Theorem 1.20, backward, exactly: a witness makes u a canonical joinand of w,
  -- unless w equals a and nothing lies strictly below u.
  witness⇒joinand-or-minimal : IsJoinIrreducible u → JoinandWitness w u a
                             → Any (u ≈ʷ_) (canonicalJoinands _≟_ w) ⊎ ((w ≈ʷ a) × (∀ v → ¬ (v <ʷ u)))
  witness⇒joinand-or-minimal {u = u} {w} {a} ji (e , cond) =
    caseList (filter P? cj) minimal joinand
    where
    cj : List (LatTerm X)
    cj = canonicalJoinands _≟_ w

    P? : (c : LatTerm X) → Dec (c ≤ʷ u)
    P? c = c ≤ʷ? u

    -- Theorem 1.19: every canonical joinand lies below u or below a.
    refine : {c : LatTerm X} → c ∈ cj → (c ≤ʷ u) ⊎ (c ≤ʷ a)
    refine c∈ = split (canonicalJoinands-refine _≟_ e c∈)
      where
      split : {P : LatTerm X → Type χ} → Any P (u ∷ a ∷ []) → P u ⊎ P a
      split (here p)          = inj₁ p
      split (there (here p))  = inj₂ p
      split (there (there ()))

    a≤w : a ≤ʷ w
    a≤w = ≤ʷ-trans ∨̇-upperʳ (proj₂ e)

    minimal : filter P? cj ≡ [] → Any (u ≈ʷ_) cj ⊎ ((w ≈ʷ a) × (∀ v → ¬ (v <ʷ u)))
    minimal eq = inj₂ (w≈a , λ v v<u → proj₂ (cond v v<u) (≤ʷ-trans (proj₁ w≈a) ∨̇-upperʳ))
      where
      none : {c : LatTerm X} → c ∈ cj → ¬ (c ≤ʷ u)
      none {c} c∈ c≤u = ∉[] (subst (c ∈_) eq (∈-filter⁺ P? c∈ c≤u))

      w≈a : w ≈ʷ a
      w≈a = canonicalJoinands-least _≟_ (λ c∈ → [ (λ c≤u → ⊥-elim (none c∈ c≤u)) , id ]′ (refine c∈))
          , a≤w

    joinand : ∀ o os → filter P? cj ≡ o ∷ os → Any (u ≈ʷ_) cj ⊎ ((w ≈ʷ a) × (∀ v → ¬ (v <ʷ u)))
    joinand o os eq =
      let (c , c∈ , u≈c) = find (joinIrreducible-⋁⁺ ji (u≤v , v≤u))
      in inj₁ (lose (proj₁ (below-∈ c∈)) u≈c)
      where
      below-∈ : {c : LatTerm X} → c ∈ (o ∷ os) → c ∈ cj × (c ≤ʷ u)
      below-∈ {c} c∈ = ∈-filter⁻ P? (subst (c ∈_) (sym eq) c∈)

      v≤u : ⋁⁺ o os ≤ʷ u
      v≤u = ⋁⁺-least λ c∈ → proj₂ (below-∈ c∈)

      w≤va : w ≤ʷ ⋁⁺ o os ∨̇ a
      w≤va = canonicalJoinands-least _≟_ λ {c} c∈ →
        [ (λ c≤u → ≤ʷ-trans (⋁⁺-upper (subst (c ∈_) eq (∈-filter⁺ P? c∈ c≤u))) ∨̇-upperˡ)
        , (λ c≤a → ≤ʷ-trans c≤a ∨̇-upperʳ) ]′ (refine c∈)

      u≤v : u ≤ʷ ⋁⁺ o os
      u≤v with u ≤ʷ? ⋁⁺ o os
      ... | yes p  = p
      ... | no  ¬p = ⊥-elim (proj₂ (cond (⋁⁺ o os) (v≤u , ¬p)) w≤va)

  -- Theorem 1.20, backward: for u with something strictly below it, a witness makes u a canonical joinand.
  witness⇒joinand : IsJoinIrreducible u → v <ʷ u → JoinandWitness w u a
                  → Any (u ≈ʷ_) (canonicalJoinands _≟_ w)
  witness⇒joinand {v = v} ji v<u wit =
    [ id , (λ (_ , minimal) → ⊥-elim (minimal v v<u)) ]′ (witness⇒joinand-or-minimal ji wit)
```

#### Theorem 1.20

For a join irreducible `u` with some element strictly below it, `u` is a
canonical joinand of `w` if and only if some `a` witnesses it
(`canonicalJoinand⇔witness`{.AgdaFunction}).  The hypothesis on `u` is what the
book's convention on join irreducible elements supplies in a finite lattice,
and what the free lattice on a finite set of generators, which is infinite,
does not: there the least element is join irreducible and has no witness
theory, as the corner above says.  For `X = Fin n` the element strictly below
any `u` other than the least element is the meet of the generators; for an
infinite `X` it is `u ∧ x` for a generator `x` not occurring in `u`.

```agda
  -- Theorem 1.20.
  canonicalJoinand⇔witness : IsJoinIrreducible u → v <ʷ u
                           → Any (u ≈ʷ_) (canonicalJoinands _≟_ w) ⇔ (Σ[ a ∈ LatTerm X ] JoinandWitness w u a)
  canonicalJoinand⇔witness ji v<u =
    mk⇔ (joinand⇒witness v<u) (λ (_ , wit) → witness⇒joinand ji v<u wit)
```
