---
layout: default
file: "src/Lattices/Free/FixedPointFree.lagda.md"
title: "Lattices.Free.FixedPointFree module"
date: "2026-10-17"
author: "William DeMeo"
---

### Theorem 1.23: a fixed point free polynomial

Freese, Ježek, and Nation, *Free Lattices* (1995), Theorem 1.23,
extract a smaller fixed point from a canonical joinand of a hypothetical
fixed point.  We use well-founded induction on the rank of the canonical
term, simultaneously for the three cyclic positions.  Duality turns the
smaller fixed point of a dual polynomial into one of the original
polynomials.  This needs only structural rank bounds and preservation of
rank by duality; it does not assume that canonical rank is minimal among
all representations.

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.FixedPointFree where

open import Data.Empty using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base using ( Fin )
open import Data.Fin.Properties using ( _≟_ )
open import Data.List.Base using ( List ; [] ; _∷_ )
open import Data.List.Membership.Propositional using ( _∈_ ; find )
open import Data.List.Relation.Unary.All using ( lookup )
open import Data.List.Relation.Unary.Any using ( Any ; here ; there )
open import Data.Nat.Base using ( suc ; _+_ ; _≤_ ; _<_ ; s≤s )
open import Data.Nat.Induction using ( <-wellFounded )
open import Data.Nat.Properties using ( ≤-trans ; m≤m+n ; m≤n+m )
open import Data.Product using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base using ( _⊎_ ; inj₁ ; inj₂ ; [_,_]′ )
open import Induction.WellFounded using ( Acc ; acc )
open import Relation.Binary.PropositionalEquality
  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst )
open import Relation.Nullary using ( ¬_ )

open import Lattices.Free.Canonical.Basic
  using ( CTerm ; CJand ; CMand ; genᶜ ; joinᶜ ; meetᶜ ; jgen ; jmeet
        ; mgen ; mjoin ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⋁ᴶ ; crank ; crankJ ; crankM
        ; crankΣJ ; crankΣM ; IsCanonical ; IsCanonicalJ ; cgen ; cjoin
        ; cjgen ; cjmeet ; ≈ʷ-sym ; ≈ʷ-trans
        ; W-list-⁺ᴶ ; dualᶜ ; dualᴶ ; dualᴹ ; dualᴶs ; dualᴹs
        ; ⌊dualᶜ⌋ ; dualᶜ-canonical )
open import Lattices.Free.Canonical.Algorithm using ( module Canonicalization )
open import Lattices.Free.Canonical.Joinands using ( joinands-refine )
open import Lattices.Free.Duality using ( dual ; dual-cong )
open import Lattices.Free.Term using ( _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman
  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-refl ; ≤ʷ-trans ; ∨≤ ; ∨̇-upperˡ
        ; ∨̇-upperʳ ; ∧̇-lowerʳ )
open import Lattices.Free.WhitmanPolynomials
  using ( Term₃ ; rot ; a ; b ; c ; r ; p ; q ; r-step ; r-cong ; p-mono
        ; p-cong ; q-cong ; a≰c ; b≰p ; c≰p ; p-a≰a )
```

The rank calculation is structural.  A joinand is strictly smaller than
the join containing it, and taking its dual leaves that rank unchanged.

```agda
-- Regard a joinand as a canonical term in its own right.
termJ : CJand (Fin 3) → CTerm (Fin 3)
termJ (jgen k) = genᶜ k
termJ (jmeet h t) = meetᶜ h t

-- This conversion leaves the represented term unchanged.
termJ-sound : (j : CJand (Fin 3)) → ⌊ termJ j ⌋ ≡ ⌊ j ⌋ᴶ
termJ-sound (jgen k) = refl
termJ-sound (jmeet h t) = refl

-- Canonicality passes from a joinand to the term.
termJ-canonical : {j : CJand (Fin 3)} → IsCanonicalJ j → IsCanonical (termJ j)
termJ-canonical cjgen = cgen
termJ-canonical (cjmeet h) = h

-- The two views of a joinand have the same rank.
termJ-rank : (j : CJand (Fin 3)) → crank (termJ j) ≡ crankJ j
termJ-rank (jgen k) = refl
termJ-rank (jmeet h t) = refl

-- A member's rank is bounded by the sum over its list.
member-rank : {j : CJand (Fin 3)} {js : List (CJand (Fin 3))}
  → j ∈ js → crankJ j ≤ crankΣJ js
member-rank {js = j ∷ js} (here refl) = m≤m+n (crankJ j) (crankΣJ js)
member-rank {js = h ∷ js} (there i) =
  ≤-trans (member-rank i) (m≤n+m (crankΣJ js) (crankJ h))

mutual
  -- Duality preserves the rank of a canonical term.
  dual-rank : (C : CTerm (Fin 3)) → crank (dualᶜ C) ≡ crank C
  dual-rank (genᶜ k) = refl
  dual-rank (joinᶜ h t) = cong suc (cong₂ _+_ (dual-rankJ h) (dual-rankJs t))
  dual-rank (meetᶜ h t) = cong suc (cong₂ _+_ (dual-rankM h) (dual-rankMs t))

  -- The same calculation for a joinand.
  dual-rankJ : (j : CJand (Fin 3)) → crankM (dualᴶ j) ≡ crankJ j
  dual-rankJ (jgen k) = refl
  dual-rankJ (jmeet h t) = cong suc (cong₂ _+_ (dual-rankM h) (dual-rankMs t))

  -- The same calculation for a meetand.
  dual-rankM : (m : CMand (Fin 3)) → crankJ (dualᴹ m) ≡ crankM m
  dual-rankM (mgen k) = refl
  dual-rankM (mjoin h t) = cong suc (cong₂ _+_ (dual-rankJ h) (dual-rankJs t))

  -- The sums over dual lists agree.
  dual-rankJs : (js : List (CJand (Fin 3))) → crankΣM (dualᴶs js) ≡ crankΣJ js
  dual-rankJs [] = refl
  dual-rankJs (j ∷ js) = cong₂ _+_ (dual-rankJ j) (dual-rankJs js)

  -- The dual sum calculation for meetands.
  dual-rankMs : (ms : List (CMand (Fin 3))) → crankΣJ (dualᴹs ms) ≡ crankΣM ms
  dual-rankMs [] = refl
  dual-rankMs (m ∷ ms) = cong₂ _+_ (dual-rankM m) (dual-rankMs ms)
```

Fix a hypothetical fixed point `s`.  Its representation `r ∨ a` is a
proper join: neither `r` nor `a` can contain `s`.  Equation (6) makes
`r` a fixed point of the rotated dual polynomial.

```agda
module Consequences (k : Fin 3) (s : Term₃) (fixed : p k s ≈ʷ s) where
  -- Every value of p lies above its final generator.
  a≤s : a k ≤ʷ s
  a≤s = ≤ʷ-trans ∨̇-upperʳ (proj₁ fixed)

  -- The fixed point cannot lie below its meet part.
  s≰r : ¬ (s ≤ʷ r k s)
  s≰r h = a≰c k (≤ʷ-trans a≤s (≤ʷ-trans h ∧̇-lowerʳ))

  -- Nor can it equal its final generator.
  s≰a : ¬ (s ≤ʷ a k)
  s≰a h = p-a≰a k (≤ʷ-trans (p-mono k a≤s) (≤ʷ-trans (proj₁ fixed) h))

  -- The meet part is not absorbed by the final generator.
  r≰a : ¬ (r k s ≤ʷ a k)
  r≰a h = s≰a (≤ʷ-trans (proj₂ fixed) (∨≤ h ≤ʷ-refl))

  -- The two excluded generators remain excluded at a fixed point.
  b≰s : ¬ (b k ≤ʷ s)
  b≰s h = b≰p k s (≤ʷ-trans h (proj₂ fixed))

  -- The last generator is excluded as well.
  c≰s : ¬ (c k ≤ʷ s)
  c≰s h = c≰p k s (≤ʷ-trans h (proj₂ fixed))

  -- Equation (6), transported through equality of the argument.
  r-fixed : q (rot (rot k)) (r k s) ≈ʷ r k s
  r-fixed = subst (_≈ʷ r k s) (sym (r-step k s)) (r-cong k fixed)

  -- A singleton canonical join representation would collapse the proper join.
  no-singleton : Any (s ≤ʷ_) (r k s ∷ a k ∷ []) → ⊥
  no-singleton (here h) = s≰r h
  no-singleton (there (here h)) = s≰a h
```

Theorem 1.19 and Whitman's condition identify the meet part with an actual
canonical joinand.  Refinement puts that joinand below `r` or `a`; the
second possibility contradicts `r ≰ a`.

```agda
-- A fixed point of one of the three cyclic polynomials.
Fixed : CTerm (Fin 3) → Set
Fixed C = Σ[ k ∈ Fin 3 ] p k ⌊ C ⌋ ≈ʷ ⌊ C ⌋

-- Every hypothetical canonical fixed point yields one of smaller rank.
descent : (C : CTerm (Fin 3)) → IsCanonical C → Fixed C
  → Σ[ D ∈ CTerm (Fin 3) ] IsCanonical D × (crank D < crank C) × Fixed D
descent C@(genᶜ _) can (k , fixed) =
  ⊥-elim (Consequences.no-singleton k ⌊ C ⌋ fixed
    (joinands-refine C can (≈ʷ-sym fixed) (here refl)))
descent C@(meetᶜ _ _) can (k , fixed) =
  ⊥-elim (Consequences.no-singleton k ⌊ C ⌋ fixed
    (joinands-refine C can (≈ʷ-sym fixed) (here refl)))
descent C@(joinᶜ h t) can@(cjoin ne cs ac c4) (k , fixed) =
  choose (W-list-⁺ᴶ {w = arm} {ws = c k ∷ []}
    (≤ʷ-trans ∨̇-upperˡ (proj₁ fixed)))
  where
  open Consequences k (⋁ᴶ h t) fixed

  -- The other meetand of r contains the excluded middle generator.
  arm : Term₃
  arm = (((⋁ᴶ h t ∧̇ b k) ∨̇ c k) ∧̇ a k) ∨̇ b k

  -- The result required by the descent.
  Smaller : Set
  Smaller = Σ[ D ∈ CTerm (Fin 3) ] IsCanonical D × (crank D < crank C) × Fixed D

  -- Neither meetand of r can lie below the fixed point.
  excluded : Any (_≤ʷ ⋁ᴶ h t) (arm ∷ c k ∷ []) → ⊥
  excluded (here e) = b≰s (≤ʷ-trans ∨̇-upperʳ e)
  excluded (there (here e)) = c≰s e

  -- Equality with r supplies the smaller fixed point after duality.
  smaller : {j : CJand (Fin 3)} → j ∈ (h ∷ t) → ⌊ j ⌋ᴶ ≈ʷ r k (⋁ᴶ h t) → Smaller
  smaller {j} j∈ e = D , dualᶜ-canonical (termJ-canonical (lookup cs j∈)) , small ,
    rot (rot k) , fixedD
    where
    -- The new canonical representative is the dual joinand.
    D : CTerm (Fin 3)
    D = dualᶜ (termJ j)

    -- Read the equality through the term view of the child.
    eJ : ⌊ termJ j ⌋ ≈ʷ r k (⋁ᴶ h t)
    eJ = subst (_≈ʷ r k (⋁ᴶ h t)) (sym (termJ-sound j)) e

    -- The child is fixed by the rotated dual polynomial.
    fixedJ : q (rot (rot k)) ⌊ termJ j ⌋ ≈ʷ ⌊ termJ j ⌋
    fixedJ = ≈ʷ-trans (q-cong (rot (rot k)) eJ) (≈ʷ-trans r-fixed (≈ʷ-sym eJ))

    -- Duality gives a fixed point of p with the new index.
    fixedD : p (rot (rot k)) ⌊ D ⌋ ≈ʷ ⌊ D ⌋
    fixedD = subst (λ u → p (rot (rot k)) u ≈ʷ u)
      (sym (⌊dualᶜ⌋ (termJ j))) (dual-cong fixedJ)

    -- The added join node makes the decrease strict.
    small : crank D < crank C
    small = subst (_< crank C) (sym (trans (dual-rank (termJ j)) (termJ-rank j)))
      (s≤s (member-rank j∈))

  -- Refinement rules out the final generator and identifies the joinand.
  identify : {j : CJand (Fin 3)} → j ∈ (h ∷ t) → r k (⋁ᴶ h t) ≤ʷ ⌊ j ⌋ᴶ
    → Any (⌊ j ⌋ᴶ ≤ʷ_) (r k (⋁ᴶ h t) ∷ a k ∷ []) → Smaller
  identify j∈ lower (here upper) = smaller j∈ (upper , lower)
  identify j∈ lower (there (here upper)) = ⊥-elim (r≰a (≤ʷ-trans lower upper))

  -- Whitman's surviving disjunct supplies the joinand to refine.
  choose : Any (_≤ʷ ⋁ᴶ h t) (arm ∷ c k ∷ [])
    ⊎ Any (λ j → r k (⋁ᴶ h t) ≤ʷ ⌊ j ⌋ᴶ) (h ∷ t) → Smaller
  choose (inj₁ e) = ⊥-elim (excluded e)
  choose (inj₂ e) = let (j , j∈ , lower) = find e in
    identify j∈ lower (joinands-refine C can (≈ʷ-sym fixed) j∈)
```

Well-foundedness rules out an infinite sequence of these strict decreases.
Canonicalization then gives Theorem 1.23 for every lattice term, and
duality gives the other three polynomials at the same time.

```agda
-- A canonical fixed point cannot have an accessible rank.
no-fixed-accessible : (C : CTerm (Fin 3)) → Acc _<_ (crank C)
  → IsCanonical C → ¬ (Fixed C)
no-fixed-accessible C (acc smaller) can fixed =
  let (D , canD , decrease , fixedD) = descent C can fixed in
  no-fixed-accessible D (smaller decrease) canD fixedD

-- Theorem 1.23, simultaneously for the three cyclic instances of p.
p-fixed-point-free : (k : Fin 3) (u : Term₃) → ¬ (p k u ≈ʷ u)
p-fixed-point-free k u fixed =
  no-fixed-accessible (canonical u) (<-wellFounded (crank (canonical u)))
    (canonical-isCanonical u)
    (k , ≈ʷ-trans (p-cong k (canonical-sound u))
      (≈ʷ-trans fixed (≈ʷ-sym (canonical-sound u))))
  where
  open Canonicalization (_≟_ {3})
    using ( canonical ; canonical-sound ; canonical-isCanonical )

-- The three dual polynomials have no fixed points either.
q-fixed-point-free : (k : Fin 3) (u : Term₃) → ¬ (q k u ≈ʷ u)
q-fixed-point-free k u fixed = p-fixed-point-free k (dual u) (dual-cong fixed)
```
