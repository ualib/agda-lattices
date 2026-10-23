---
layout: default
file: "src/Lattices/Free/Canonical/Recognition.lagda.md"
title: "Lattices.Free.Canonical.Recognition module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### Recognizing canonical terms

This is the [Lattices.Free.Canonical.Recognition][] module of the [agda-lattices][] library.

Theorem 1.18 of [Freese, Ježek, and Nation (1995)][] characterizes the canonical
terms by four syntactic conditions, and [Lattices.Free.Canonical.Basic][] states
them as the predicate `IsCanonical`{.AgdaDatatype}.  Each condition is a finite
conjunction of instances of Whitman's order, so the predicate is decidable, and
this module decides it (`isCanonical?`{.AgdaFunction}).  The decision is what
certifies a canonical form written out by hand, or computed by another program:
[Lattices.Free.Canonical.Algorithm][] computes canonical forms, but on large
terms the computation is too slow to repeat at every build, while checking a
given term against the four conditions is cheap.  At each join or meet with
`n` children it costs `n(n - 1)` Whitman decisions for condition 3 (two per
pair of children, one in each direction) and one for condition 4 per meetand
of each child that is a meet (dually, per joinand of each child that is a
join), and then the same inside each child.

Condition 1 holds by the type of canonical terms; condition 2 is the recursion
into the children; condition 3, the antichain, is decided pairwise with
`allPairs?`{.AgdaFunction}; and condition 4, as `Cond4J`{.AgdaFunction} states it,
quantifies over memberships, so it is decided through an equivalent form that
quantifies over the list of children (`Cond4ᴶ-all`{.AgdaFunction}): every child
that is a meet has no meetand below the whole join.  The recursion runs over the
children as the comparison of canonical terms in
[Lattices.Free.Canonical.Uniqueness][] does, so that every call is on a subterm.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical.Recognition where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional     using ( _∈_ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; all? ; lookup
                                                         ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( allPairs? )
open import Data.Product                           using ( _×_ ; _,_ ; uncurry )
open import Data.Unit.Polymorphic                  using ( ⊤ ; tt )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≢_ ; refl )
open import Relation.Nullary.Decidable.Core        using ( Dec ; yes ; no ; map′ ; ¬? ; _×-dec_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋ᴶ
         ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; _≰ʷ_ ; AntichainJ ; AntichainM ; Cond4J ; Cond4M ; IsCanonical ; cgen
         ; cjoin ; cmeet ; IsCanonicalJ ; cjgen ; cjmeet ; IsCanonicalM ; cmgen ; cmjoin )
open import Lattices.Free.Term                     using ( LatTerm )
open import Lattices.Free.Whitman                  using ( module Decision )

private variable
  ℓ χ : Level
  A : Type ℓ
```
-->

#### Condition 4, read over the children

`Cond4J h t`{.AgdaFunction} says that no meetand of a child of the join that is a
meet lies below the join.  `Cond4ᴶ-at W a`{.AgdaFunction} says it of one child
`a`, for the join `W`: nothing for a generator, and for a meet, that all of its
meetands fail to lie below `W`.  The condition is that every child satisfies
this (`Cond4ᴶ-all`{.AgdaFunction}), in both directions; dually for meets.

```agda
module _ {X : Type χ} where
  -- Condition 4 at one child of a join, and at one child of a meet.
  Cond4ᴶ-at : LatTerm X → CJand X → Type χ
  Cond4ᴶ-at W (jgen _)       = ⊤
  Cond4ᴶ-at W (jmeet mh mt)  = All (λ m → ⌊ m ⌋ᴹ ≰ʷ W) (mh ∷ mt)

  Cond4ᴹ-at : LatTerm X → CMand X → Type χ
  Cond4ᴹ-at W (mgen _)       = ⊤
  Cond4ᴹ-at W (mjoin jh jt)  = All (λ j → W ≰ʷ ⌊ j ⌋ᴶ) (jh ∷ jt)

  -- Condition 4 is condition 4 at every child.
  Cond4ᴶ-all : {h : CJand X} {t : List (CJand X)} → All (Cond4ᴶ-at (⋁ᴶ h t)) (h ∷ t) → Cond4J h t
  Cond4ᴶ-all c4 a∈ m∈ = lookup (lookup c4 a∈) m∈

  all-Cond4ᴶ : {h : CJand X} {t : List (CJand X)} → Cond4J h t → All (Cond4ᴶ-at (⋁ᴶ h t)) (h ∷ t)
  all-Cond4ᴶ {h} {t} c4 = tabulate at
    where
    at : ∀ {a} → a ∈ (h ∷ t) → Cond4ᴶ-at (⋁ᴶ h t) a
    at {jgen _}       _   = tt
    at {jmeet mh mt}  a∈  = tabulate λ m∈ → c4 a∈ m∈

  Cond4ᴹ-all : {h : CMand X} {t : List (CMand X)} → All (Cond4ᴹ-at (⋀ᴹ h t)) (h ∷ t) → Cond4M h t
  Cond4ᴹ-all c4 a∈ j∈ = lookup (lookup c4 a∈) j∈

  all-Cond4ᴹ : {h : CMand X} {t : List (CMand X)} → Cond4M h t → All (Cond4ᴹ-at (⋀ᴹ h t)) (h ∷ t)
  all-Cond4ᴹ {h} {t} c4 = tabulate at
    where
    at : ∀ {a} → a ∈ (h ∷ t) → Cond4ᴹ-at (⋀ᴹ h t) a
    at {mgen _}       _   = tt
    at {mjoin jh jt}  a∈  = tabulate λ j∈ → c4 a∈ j∈
```

#### The decision

Fix a decision procedure for equality of generators (the module
`Recognize`{.AgdaModule}).  Conditions 3 and 4 and the nonemptiness of the tail
are decided directly; the recursion collects the decisions for the children.

```agda
module Recognize {X : Type χ} (_≟_ : DecidableEquality X) where
  open Decision _≟_ using ( _≤ʷ?_ )

  -- A join or meet has at least two children.
  nonempty? : (t : List A) → Dec (t ≢ [])
  nonempty? []       = no λ ne → ne refl
  nonempty? (_ ∷ _)  = yes λ ()

  -- Condition 3: the children form an antichain.
  antichainJ? : (as : List (CJand X)) → Dec (AntichainJ as)
  antichainJ? = allPairs? λ a b → ¬? (⌊ a ⌋ᴶ ≤ʷ? ⌊ b ⌋ᴶ) ×-dec ¬? (⌊ b ⌋ᴶ ≤ʷ? ⌊ a ⌋ᴶ)

  antichainM? : (as : List (CMand X)) → Dec (AntichainM as)
  antichainM? = allPairs? λ a b → ¬? (⌊ a ⌋ᴹ ≤ʷ? ⌊ b ⌋ᴹ) ×-dec ¬? (⌊ b ⌋ᴹ ≤ʷ? ⌊ a ⌋ᴹ)

  -- Condition 4.
  cond4ᴶ-at? : (W : LatTerm X) (a : CJand X) → Dec (Cond4ᴶ-at W a)
  cond4ᴶ-at? W (jgen _)       = yes tt
  cond4ᴶ-at? W (jmeet mh mt)  = all? (λ m → ¬? (⌊ m ⌋ᴹ ≤ʷ? W)) (mh ∷ mt)

  cond4ᴹ-at? : (W : LatTerm X) (a : CMand X) → Dec (Cond4ᴹ-at W a)
  cond4ᴹ-at? W (mgen _)       = yes tt
  cond4ᴹ-at? W (mjoin jh jt)  = all? (λ j → ¬? (W ≤ʷ? ⌊ j ⌋ᴶ)) (jh ∷ jt)

  cond4J? : (h : CJand X) (t : List (CJand X)) → Dec (Cond4J h t)
  cond4J? h t = map′ Cond4ᴶ-all all-Cond4ᴶ (all? (cond4ᴶ-at? (⋁ᴶ h t)) (h ∷ t))

  cond4M? : (h : CMand X) (t : List (CMand X)) → Dec (Cond4M h t)
  cond4M? h t = map′ Cond4ᴹ-all all-Cond4ᴹ (all? (cond4ᴹ-at? (⋀ᴹ h t)) (h ∷ t))
```

The decision of `IsCanonical`{.AgdaDatatype} (`isCanonical?`{.AgdaFunction})
conjoins the four decisions at a join or a meet, and answers yes at once for a
generator.

```agda
  isCanonical?       : (C : CTerm X) → Dec (IsCanonical C)
  isCanonical-join?  : (h : CJand X) (t : List (CJand X)) → Dec (IsCanonical (joinᶜ h t))
  isCanonical-meet?  : (h : CMand X) (t : List (CMand X)) → Dec (IsCanonical (meetᶜ h t))
  isCanonicalJ?      : (a : CJand X) → Dec (IsCanonicalJ a)
  isCanonicalM?      : (a : CMand X) → Dec (IsCanonicalM a)
  allCanonicalJ?     : (as : List (CJand X)) → Dec (All IsCanonicalJ as)
  allCanonicalM?     : (as : List (CMand X)) → Dec (All IsCanonicalM as)

  isCanonical? (genᶜ _)     = yes cgen
  isCanonical? (joinᶜ h t)  = isCanonical-join? h t
  isCanonical? (meetᶜ h t)  = isCanonical-meet? h t

  isCanonical-join? h t =
    map′ to from (nonempty? t ×-dec children ×-dec antichainJ? (h ∷ t) ×-dec cond4J? h t)
    where
    children : Dec (All IsCanonicalJ (h ∷ t))
    children = map′ (uncurry _∷_) (λ { (c ∷ cs) → c , cs }) (isCanonicalJ? h ×-dec allCanonicalJ? t)

    to : t ≢ [] × All IsCanonicalJ (h ∷ t) × AntichainJ (h ∷ t) × Cond4J h t → IsCanonical (joinᶜ h t)
    to (ne , cs , ac , c4) = cjoin ne cs ac c4

    from : IsCanonical (joinᶜ h t) → t ≢ [] × All IsCanonicalJ (h ∷ t) × AntichainJ (h ∷ t) × Cond4J h t
    from (cjoin ne cs ac c4) = ne , cs , ac , c4

  isCanonical-meet? h t =
    map′ to from (nonempty? t ×-dec children ×-dec antichainM? (h ∷ t) ×-dec cond4M? h t)
    where
    children : Dec (All IsCanonicalM (h ∷ t))
    children = map′ (uncurry _∷_) (λ { (c ∷ cs) → c , cs }) (isCanonicalM? h ×-dec allCanonicalM? t)

    to : t ≢ [] × All IsCanonicalM (h ∷ t) × AntichainM (h ∷ t) × Cond4M h t → IsCanonical (meetᶜ h t)
    to (ne , cs , ac , c4) = cmeet ne cs ac c4

    from : IsCanonical (meetᶜ h t) → t ≢ [] × All IsCanonicalM (h ∷ t) × AntichainM (h ∷ t) × Cond4M h t
    from (cmeet ne cs ac c4) = ne , cs , ac , c4

  isCanonicalJ? (jgen _)       = yes cjgen
  isCanonicalJ? (jmeet mh mt)  = map′ cjmeet (λ { (cjmeet c) → c }) (isCanonical-meet? mh mt)

  isCanonicalM? (mgen _)       = yes cmgen
  isCanonicalM? (mjoin jh jt)  = map′ cmjoin (λ { (cmjoin c) → c }) (isCanonical-join? jh jt)

  allCanonicalJ? []        = yes []
  allCanonicalJ? (a ∷ as)  = map′ (uncurry _∷_) (λ { (c ∷ cs) → c , cs })
                                  (isCanonicalJ? a ×-dec allCanonicalJ? as)

  allCanonicalM? []        = yes []
  allCanonicalM? (a ∷ as)  = map′ (uncurry _∷_) (λ { (c ∷ cs) → c , cs })
                                  (isCanonicalM? a ×-dec allCanonicalM? as)
```
