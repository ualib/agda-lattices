---
layout: default
file: "src/Lattices/Free/Canonical/Minimality.lagda.md"
title: "Lattices.Free.Canonical.Minimality module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Minimality of the rank of a canonical form

This is the [Lattices.Free.Canonical.Minimality][] module of the [agda-lattices][] library.

Theorem 1.17 of [Freese, Ježek, and Nation (1995)][] says that every element of a
free lattice has a term of *minimal rank* representing it, unique up to
commutativity.  [Lattices.Free.Canonical.Uniqueness][] proves the uniqueness
half: two canonical terms, in the sense of Theorem 1.18, that represent the same
element are related by `_≈ᶜ_`{.AgdaDatatype}.  This module proves the
minimality half: a canonical term has the least rank among *all* the terms
representing its element, canonical or not, however they are written.

The rank of the book (Section I.2) counts the occurrences of generators plus the
pairs of parentheses, and the book's terms are `n`-ary: `x ∨ y ∨ z` has rank 4,
`x ∨ (y ∨ z)` rank 5.  Two ranks already live in the library.
`crank`{.AgdaFunction} of [Lattices.Free.Canonical.Basic][] is the book's rank on
canonical terms, whose joins and meets are flat; `rank`{.AgdaFunction} of
[Lattices.Free.Term][] is the book's rank of a binary term read with every
parenthesis in place, so that it charges `x ∨̇ (y ∨̇ z)` one more than the book
does.  The theorem must compare a canonical term with an arbitrary binary term,
so it needs the book's rank of a binary term read as the flat term it
abbreviates: a chain of joins `s₁ ∨̇ (s₂ ∨̇ ⋯)` counts one plus the ranks of its
maximal non-join subterms, however the chain is associated, and dually for meets.
That is the *flattened rank* `rankᶠ`{.AgdaFunction} defined here.  It agrees
with `crank`{.AgdaFunction} on the embedding of every canonical term, and it is
never larger than `rank`{.AgdaFunction}, with equality exactly when no join has a
join as a child and no meet a meet.

The proof of minimality does not follow the book's minimal-counterexample
argument.  It uses the invariants of the canonicalization algorithm of
[Lattices.Free.Canonical.Algorithm][] instead: canonicalization never raises
the flattened rank (`canonical-rank-bound`{.AgdaFunction}), because its deletion
step lowers the rank sum of the joinands and its replacement step replaces a
joinand by a proper part of it; the relation `_≈ᶜ_`{.AgdaDatatype} preserves the
rank (`crank-≈ᶜ`{.AgdaFunction}), since a permutation and a pointwise relation of
the children preserve the sum of their ranks; and two canonical terms of one
element are related, by Theorem 1.17.  So for a canonical term `C` and any term
`u` of the same element, `crank C` is the rank of `canonical u`, which is at most
`rankᶠ u` (`crank-minimal`{.AgdaFunction}).  The claim is Theorem 1.17's, over
every representation of the element, not a comparison among canonical terms.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical.Minimality where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ )
open import Data.List.Relation.Binary.Permutation.Propositional
                                                   using ( _↭_ )
open import Data.List.Relation.Binary.Pointwise    using ( Pointwise ; [] ; _∷_ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.Nat.Base                          using ( ℕ ; suc ; _+_ ; _≤_ ; _<_ ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-reflexive ; ≤-trans
                                                         ; <-irrefl ; +-mono-≤ ; +-mono-<-≤
                                                         ; +-mono-≤-< ; +-assoc ; +-comm
                                                         ; +-identityʳ ; m≤m+n ; n≤1+n )
open import Data.Product                           using ( _×_ ; _,_ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong
                                                         ; cong₂ )

import Data.List.Relation.Binary.Permutation.Propositional  as Perm

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm
  using  ( module Canonicalization ; module ReducedJoin ; crankΣJ-++ᴶ )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin
         ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; crank ; crankJ ; crankM ; crankΣJ ; crankΣM
         ; IsCanonical ; cgen ; cjoin ; cmeet ; IsCanonicalJ ; cjgen ; cjmeet ; IsCanonicalM
         ; cmgen ; cmjoin ; asListJ ; asListM ; joinandsOf ; meetandsOf ; dualᶜ ; dualᴶ
         ; dualᴹ ; dualᴶs ; dualᴹs ; ≈ʷ-sym ; ≈ʷ-trans )
open import Lattices.Free.Canonical.Uniqueness
  using  ( _≈ᶜ_ ; gen≈ ; join≈ ; meet≈ ; _≈ᶜᴶ_ ; jgen≈ ; jmeet≈ ; _≈ᶜᴹ_ ; mgen≈ ; mjoin≈
         ; ≈ʷ⇒≈ᶜ )
open import Lattices.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ ; rank )
open import Lattices.Free.Whitman  using ( _≈ʷ_ )

private variable
  χ : Level
  X : Type χ
  x : X
  s t : LatTerm X
```
-->

#### The flattened rank

`rankᶠ t`{.AgdaFunction} is the rank of the flat term that the binary term `t`
abbreviates.  A generator has rank 1.  A join `s ∨̇ t` is a node of the flat
term whose children are the maximal non-join subterms of `s` and of `t`, so its
rank is one plus the sum of their ranks; `rank∨ᶠ`{.AgdaFunction} computes that
sum for a term that may itself be a join, by passing through every join at the
top without charging for it, and `rank∧ᶠ`{.AgdaFunction} does the same for
meets.  The two helpers are mutually recursive, and `rankᶠ`{.AgdaFunction} is
defined from them: on a term that is not a join, `rank∨ᶠ`{.AgdaFunction} is
`rankᶠ`{.AgdaFunction}, by definition, and dually.

```agda
rank∨ᶠ : LatTerm X → ℕ
rank∧ᶠ : LatTerm X → ℕ

rank∨ᶠ (ℊ x)    = 1
rank∨ᶠ (s ∨̇ t)  = rank∨ᶠ s + rank∨ᶠ t
rank∨ᶠ (s ∧̇ t)  = suc (rank∧ᶠ s + rank∧ᶠ t)
rank∧ᶠ (ℊ x)    = 1
rank∧ᶠ (s ∧̇ t)  = rank∧ᶠ s + rank∧ᶠ t
rank∧ᶠ (s ∨̇ t)  = suc (rank∨ᶠ s + rank∨ᶠ t)

-- The book's rank of a binary term, read as the flat term it abbreviates.
rankᶠ : LatTerm X → ℕ
rankᶠ (ℊ x)    = 1
rankᶠ (s ∨̇ t)  = suc (rank∨ᶠ s + rank∨ᶠ t)
rankᶠ (s ∧̇ t)  = suc (rank∧ᶠ s + rank∧ᶠ t)
```

#### Comparison with the binary rank

The binary rank `rank`{.AgdaFunction} charges every node, so the flattened rank
is never larger (`rankᶠ≤rank`{.AgdaFunction}), and each helper is bounded by the
binary rank too.

```agda
rank∨ᶠ≤rank  : (t : LatTerm X) → rank∨ᶠ t ≤ rank t
rank∧ᶠ≤rank  : (t : LatTerm X) → rank∧ᶠ t ≤ rank t

rank∨ᶠ≤rank (ℊ x)    = ≤-refl
rank∨ᶠ≤rank (s ∨̇ t)  = ≤-trans (+-mono-≤ (rank∨ᶠ≤rank s) (rank∨ᶠ≤rank t)) (n≤1+n _)
rank∨ᶠ≤rank (s ∧̇ t)  = s≤s (+-mono-≤ (rank∧ᶠ≤rank s) (rank∧ᶠ≤rank t))
rank∧ᶠ≤rank (ℊ x)    = ≤-refl
rank∧ᶠ≤rank (s ∧̇ t)  = ≤-trans (+-mono-≤ (rank∧ᶠ≤rank s) (rank∧ᶠ≤rank t)) (n≤1+n _)
rank∧ᶠ≤rank (s ∨̇ t)  = s≤s (+-mono-≤ (rank∨ᶠ≤rank s) (rank∨ᶠ≤rank t))

-- The flattened rank is never larger than the binary rank.
rankᶠ≤rank : (t : LatTerm X) → rankᶠ t ≤ rank t
rankᶠ≤rank (ℊ x)    = ≤-refl
rankᶠ≤rank (s ∨̇ t)  = s≤s (+-mono-≤ (rank∨ᶠ≤rank s) (rank∨ᶠ≤rank t))
rankᶠ≤rank (s ∧̇ t)  = s≤s (+-mono-≤ (rank∧ᶠ≤rank s) (rank∧ᶠ≤rank t))
```

The two ranks agree exactly on the *unnested* terms, those in which no join has
a join as a child and no meet a meet (`Unnested`{.AgdaDatatype}, with
`NotJoin`{.AgdaDatatype} and `NotMeet`{.AgdaDatatype} for the children).  The
proof is a dichotomy (`rank-dichotomy`{.AgdaFunction}): either a term is unnested
and the ranks agree, or the flattened rank is strictly smaller; for a helper,
either the term is unnested and not a join (or not a meet) and the helper is the
binary rank, or the helper is strictly smaller.  A nested join is where the
strict inequality enters, since a join child contributes its children's ranks
without the one it is charged by the binary rank.

```agda
data NotJoin {X : Type χ} : LatTerm X → Type χ where
  notJoin-ℊ  : NotJoin (ℊ x)
  notJoin-∧̇  : NotJoin (s ∧̇ t)

data NotMeet {X : Type χ} : LatTerm X → Type χ where
  notMeet-ℊ  : NotMeet (ℊ x)
  notMeet-∨̇  : NotMeet (s ∨̇ t)

-- No join has a join as a child, and no meet a meet.
data Unnested {X : Type χ} : LatTerm X → Type χ where
  unnested-ℊ  : Unnested (ℊ x)
  unnested-∨̇  : NotJoin s → NotJoin t → Unnested s → Unnested t → Unnested (s ∨̇ t)
  unnested-∧̇  : NotMeet s → NotMeet t → Unnested s → Unnested t → Unnested (s ∧̇ t)

rank-dichotomy    : (t : LatTerm X) → (Unnested t × rankᶠ t ≡ rank t) ⊎ (rankᶠ t < rank t)
rank∨ᶠ-dichotomy  : (t : LatTerm X)
                  → (NotJoin t × Unnested t × rank∨ᶠ t ≡ rank t) ⊎ (rank∨ᶠ t < rank t)
rank∧ᶠ-dichotomy  : (t : LatTerm X)
                  → (NotMeet t × Unnested t × rank∧ᶠ t ≡ rank t) ⊎ (rank∧ᶠ t < rank t)

rank-dichotomy (ℊ x)    = inj₁ (unnested-ℊ , refl)
rank-dichotomy (s ∨̇ t)  with rank∨ᶠ-dichotomy s | rank∨ᶠ-dichotomy t
... | inj₁ (ns , us , es)  | inj₁ (nt , ut , et)  = inj₁ (unnested-∨̇ ns nt us ut , cong suc (cong₂ _+_ es et))
... | inj₁ (_ , _ , es)    | inj₂ lt              = inj₂ (s≤s (+-mono-≤-< (≤-reflexive es) lt))
... | inj₂ ls              | _                    = inj₂ (s≤s (+-mono-<-≤ ls (rank∨ᶠ≤rank t)))
rank-dichotomy (s ∧̇ t)  with rank∧ᶠ-dichotomy s | rank∧ᶠ-dichotomy t
... | inj₁ (ns , us , es)  | inj₁ (nt , ut , et)  = inj₁ (unnested-∧̇ ns nt us ut , cong suc (cong₂ _+_ es et))
... | inj₁ (_ , _ , es)    | inj₂ lt              = inj₂ (s≤s (+-mono-≤-< (≤-reflexive es) lt))
... | inj₂ ls              | _                    = inj₂ (s≤s (+-mono-<-≤ ls (rank∧ᶠ≤rank t)))

rank∨ᶠ-dichotomy (ℊ x)    = inj₁ (notJoin-ℊ , unnested-ℊ , refl)
rank∨ᶠ-dichotomy (s ∨̇ t)  = inj₂ (s≤s (+-mono-≤ (rank∨ᶠ≤rank s) (rank∨ᶠ≤rank t)))
rank∨ᶠ-dichotomy (s ∧̇ t)  with rank-dichotomy (s ∧̇ t)
... | inj₁ (u , e)  = inj₁ (notJoin-∧̇ , u , e)
... | inj₂ lt       = inj₂ lt

rank∧ᶠ-dichotomy (ℊ x)    = inj₁ (notMeet-ℊ , unnested-ℊ , refl)
rank∧ᶠ-dichotomy (s ∧̇ t)  = inj₂ (s≤s (+-mono-≤ (rank∧ᶠ≤rank s) (rank∧ᶠ≤rank t)))
rank∧ᶠ-dichotomy (s ∨̇ t)  with rank-dichotomy (s ∨̇ t)
... | inj₁ (u , e)  = inj₁ (notMeet-∨̇ , u , e)
... | inj₂ lt       = inj₂ lt
```

So the flattened rank equals the binary rank exactly when the term is unnested
(`rankᶠ≡rank⇔unnested`{.AgdaFunction}).  One direction is the dichotomy, the
other an induction on `Unnested`{.AgdaDatatype}, where a child that is not a
join has `rank∨ᶠ`{.AgdaFunction} equal to `rankᶠ`{.AgdaFunction} by definition.

```agda
notJoin-rank∨ᶠ : NotJoin t → rank∨ᶠ t ≡ rankᶠ t
notJoin-rank∨ᶠ notJoin-ℊ  = refl
notJoin-rank∨ᶠ notJoin-∧̇  = refl

notMeet-rank∧ᶠ : NotMeet t → rank∧ᶠ t ≡ rankᶠ t
notMeet-rank∧ᶠ notMeet-ℊ  = refl
notMeet-rank∧ᶠ notMeet-∨̇  = refl

unnested⇒rankᶠ≡rank : Unnested t → rankᶠ t ≡ rank t
unnested⇒rankᶠ≡rank unnested-ℊ = refl
unnested⇒rankᶠ≡rank (unnested-∨̇ ns nt us ut) =
  cong suc (cong₂ _+_ (trans (notJoin-rank∨ᶠ ns) (unnested⇒rankᶠ≡rank us))
                      (trans (notJoin-rank∨ᶠ nt) (unnested⇒rankᶠ≡rank ut)))
unnested⇒rankᶠ≡rank (unnested-∧̇ ns nt us ut) =
  cong suc (cong₂ _+_ (trans (notMeet-rank∧ᶠ ns) (unnested⇒rankᶠ≡rank us))
                      (trans (notMeet-rank∧ᶠ nt) (unnested⇒rankᶠ≡rank ut)))

-- The two ranks agree exactly on the unnested terms.
rankᶠ≡rank⇔unnested : (t : LatTerm X) → (rankᶠ t ≡ rank t) ⇔ Unnested t
rankᶠ≡rank⇔unnested t = mk⇔ to unnested⇒rankᶠ≡rank
  where
  to : rankᶠ t ≡ rank t → Unnested t
  to e with rank-dichotomy t
  ... | inj₁ (u , _)  = u
  ... | inj₂ lt       = ⊥-elim (<-irrefl e lt)
```

#### The flattened rank of a canonical term

On the embedding of a canonical term the flattened rank is the rank of the
canonical term (`rankᶠ-⌊⌋`{.AgdaFunction}).  The children of a canonical join are
generators or meets, so the embedding `⋁ᴶ h t`{.AgdaFunction} flattens back to
the list `h ∷ t`, and the sum of the helpers over the fold is the sum of the
children's ranks (`rank∨ᶠ-⋁ᴶ`{.AgdaFunction}); dually for meets.  The induction
runs on the canonicity proof, which supplies the nonemptiness of every tail: a
join of a single child would embed as that child, and a meet of a single child
that is a join would be flattened through, so the equation needs the canonical
shape, not the type `CTerm`{.AgdaDatatype} alone.

```agda
rankᶠ-⌊⌋     : {c : CTerm X} → IsCanonical c → rankᶠ ⌊ c ⌋ ≡ crank c
rank∨ᶠ-⌊⌋ᴶ   : {a : CJand X} → IsCanonicalJ a → rank∨ᶠ ⌊ a ⌋ᴶ ≡ crankJ a
rank∧ᶠ-⌊⌋ᴹ   : {a : CMand X} → IsCanonicalM a → rank∧ᶠ ⌊ a ⌋ᴹ ≡ crankM a
rank∨ᶠ-⋁ᴶ    : {h : CJand X} {t : List (CJand X)} → All IsCanonicalJ (h ∷ t)
             → rank∨ᶠ (⋁ᴶ h t) ≡ crankJ h + crankΣJ t
rank∧ᶠ-⋀ᴹ    : {h : CMand X} {t : List (CMand X)} → All IsCanonicalM (h ∷ t)
             → rank∧ᶠ (⋀ᴹ h t) ≡ crankM h + crankΣM t

rankᶠ-⌊⌋ cgen                                   = refl
rankᶠ-⌊⌋ (cjoin {jt = []}      ne _          _ _) = ⊥-elim (ne refl)
rankᶠ-⌊⌋ (cjoin {jt = _ ∷ _}   _  (ch ∷ cs)  _ _) = cong suc (cong₂ _+_ (rank∨ᶠ-⌊⌋ᴶ ch) (rank∨ᶠ-⋁ᴶ cs))
rankᶠ-⌊⌋ (cmeet {mt = []}      ne _          _ _) = ⊥-elim (ne refl)
rankᶠ-⌊⌋ (cmeet {mt = _ ∷ _}   _  (ch ∷ cs)  _ _) = cong suc (cong₂ _+_ (rank∧ᶠ-⌊⌋ᴹ ch) (rank∧ᶠ-⋀ᴹ cs))

rank∨ᶠ-⌊⌋ᴶ cjgen                                           = refl
rank∨ᶠ-⌊⌋ᴶ (cjmeet (cmeet {mt = []}     ne _         _ _)) = ⊥-elim (ne refl)
rank∨ᶠ-⌊⌋ᴶ (cjmeet (cmeet {mt = _ ∷ _}  _  (ch ∷ cs) _ _)) =
  cong suc (cong₂ _+_ (rank∧ᶠ-⌊⌋ᴹ ch) (rank∧ᶠ-⋀ᴹ cs))

rank∧ᶠ-⌊⌋ᴹ cmgen                                           = refl
rank∧ᶠ-⌊⌋ᴹ (cmjoin (cjoin {jt = []}     ne _         _ _)) = ⊥-elim (ne refl)
rank∧ᶠ-⌊⌋ᴹ (cmjoin (cjoin {jt = _ ∷ _}  _  (ch ∷ cs) _ _)) =
  cong suc (cong₂ _+_ (rank∨ᶠ-⌊⌋ᴶ ch) (rank∨ᶠ-⋁ᴶ cs))

rank∨ᶠ-⋁ᴶ {t = []}     (ch ∷ [])  = trans (rank∨ᶠ-⌊⌋ᴶ ch) (sym (+-identityʳ _))
rank∨ᶠ-⋁ᴶ {t = _ ∷ _}  (ch ∷ cs)  = cong₂ _+_ (rank∨ᶠ-⌊⌋ᴶ ch) (rank∨ᶠ-⋁ᴶ cs)

rank∧ᶠ-⋀ᴹ {t = []}     (ch ∷ [])  = trans (rank∧ᶠ-⌊⌋ᴹ ch) (sym (+-identityʳ _))
rank∧ᶠ-⋀ᴹ {t = _ ∷ _}  (ch ∷ cs)  = cong₂ _+_ (rank∧ᶠ-⌊⌋ᴹ ch) (rank∧ᶠ-⋀ᴹ cs)
```

#### The rank is invariant under equality up to commutativity

Two canonical terms related by `_≈ᶜ_`{.AgdaDatatype} have the same rank
(`crank-≈ᶜ`{.AgdaFunction}): a permutation of the children preserves the sum of
their ranks (`crankΣJ-↭`{.AgdaFunction}, by induction on the permutation), and so
does a pointwise relation, by the mutual induction the relation is defined by.
Combined with Theorem 1.17, two canonical terms of one element have the same
rank (`crank-≈ʷ`{.AgdaFunction}).

```agda
private
  +-swap : (a b n : ℕ) → a + (b + n) ≡ b + (a + n)
  +-swap a b n = trans (sym (+-assoc a b n)) (trans (cong (_+ n) (+-comm a b)) (+-assoc b a n))

crankΣJ-↭ : {us vs : List (CJand X)} → us ↭ vs → crankΣJ us ≡ crankΣJ vs
crankΣJ-↭ Perm.refl          = refl
crankΣJ-↭ (Perm.prep a p)    = cong (crankJ a +_) (crankΣJ-↭ p)
crankΣJ-↭ (Perm.swap a b p)  = trans (cong (λ n → crankJ a + (crankJ b + n)) (crankΣJ-↭ p))
                                     (+-swap (crankJ a) (crankJ b) _)
crankΣJ-↭ (Perm.trans p q)   = trans (crankΣJ-↭ p) (crankΣJ-↭ q)

crankΣM-↭ : {us vs : List (CMand X)} → us ↭ vs → crankΣM us ≡ crankΣM vs
crankΣM-↭ Perm.refl          = refl
crankΣM-↭ (Perm.prep a p)    = cong (crankM a +_) (crankΣM-↭ p)
crankΣM-↭ (Perm.swap a b p)  = trans (cong (λ n → crankM a + (crankM b + n)) (crankΣM-↭ p))
                                     (+-swap (crankM a) (crankM b) _)
crankΣM-↭ (Perm.trans p q)   = trans (crankΣM-↭ p) (crankΣM-↭ q)

crank-≈ᶜ      : {s t : CTerm X} → s ≈ᶜ t → crank s ≡ crank t
crankJ-≈ᶜᴶ    : {u v : CJand X} → u ≈ᶜᴶ v → crankJ u ≡ crankJ v
crankM-≈ᶜᴹ    : {u v : CMand X} → u ≈ᶜᴹ v → crankM u ≡ crankM v
crankΣJ-≈ᶜᴶs  : {us vs : List (CJand X)} → Pointwise _≈ᶜᴶ_ us vs → crankΣJ us ≡ crankΣJ vs
crankΣM-≈ᶜᴹs  : {us vs : List (CMand X)} → Pointwise _≈ᶜᴹ_ us vs → crankΣM us ≡ crankΣM vs

crank-≈ᶜ (gen≈ _)        = refl
crank-≈ᶜ (join≈ p q)     = cong suc (trans (crankΣJ-↭ p) (crankΣJ-≈ᶜᴶs q))
crank-≈ᶜ (meet≈ p q)     = cong suc (trans (crankΣM-↭ p) (crankΣM-≈ᶜᴹs q))
crankJ-≈ᶜᴶ (jgen≈ _)     = refl
crankJ-≈ᶜᴶ (jmeet≈ e)    = crank-≈ᶜ e
crankM-≈ᶜᴹ (mgen≈ _)     = refl
crankM-≈ᶜᴹ (mjoin≈ e)    = crank-≈ᶜ e
crankΣJ-≈ᶜᴶs []          = refl
crankΣJ-≈ᶜᴶs (r ∷ q)     = cong₂ _+_ (crankJ-≈ᶜᴶ r) (crankΣJ-≈ᶜᴶs q)
crankΣM-≈ᶜᴹs []          = refl
crankΣM-≈ᶜᴹs (r ∷ q)     = cong₂ _+_ (crankM-≈ᶜᴹ r) (crankΣM-≈ᶜᴹs q)

-- Two canonical terms of one element have the same rank.
crank-≈ʷ : (s t : CTerm X) → IsCanonical s → IsCanonical t → ⌊ s ⌋ ≈ʷ ⌊ t ⌋ → crank s ≡ crank t
crank-≈ʷ s t cs ct e = crank-≈ᶜ (≈ʷ⇒≈ᶜ s t cs ct e)
```

#### Duality and the ranks of the joinands and meetands

The canonical form of a meet is computed by duality, so the bound on the rank of
a canonical meet is read off the bound on a canonical join through the dual,
which preserves the rank (`crank-dualᶜ`{.AgdaFunction}).  The bound itself is
stated in terms of the *joinand rank* `jrank`{.AgdaFunction}, the sum of the
ranks of the joinands of a canonical term, and its dual `mrank`{.AgdaFunction}:
the joinands of a join are its children, whose ranks sum to one less than its
rank, and a generator or a meet is its own only joinand.  The joinand rank is
at most the rank (`jrank≤crank`{.AgdaFunction}), and duality exchanges the two
(`jrank-dualᶜ`{.AgdaFunction}, `mrank-dualᶜ`{.AgdaFunction}).

```agda
crank-dualᶜ     : (c : CTerm X) → crank (dualᶜ c) ≡ crank c
crankM-dualᴶ    : (a : CJand X) → crankM (dualᴶ a) ≡ crankJ a
crankJ-dualᴹ    : (a : CMand X) → crankJ (dualᴹ a) ≡ crankM a
crankΣM-dualᴶs  : (as : List (CJand X)) → crankΣM (dualᴶs as) ≡ crankΣJ as
crankΣJ-dualᴹs  : (as : List (CMand X)) → crankΣJ (dualᴹs as) ≡ crankΣM as

crank-dualᶜ (genᶜ x)       = refl
crank-dualᶜ (joinᶜ h t)    = cong suc (cong₂ _+_ (crankM-dualᴶ h) (crankΣM-dualᴶs t))
crank-dualᶜ (meetᶜ h t)    = cong suc (cong₂ _+_ (crankJ-dualᴹ h) (crankΣJ-dualᴹs t))
crankM-dualᴶ (jgen x)      = refl
crankM-dualᴶ (jmeet h t)   = cong suc (cong₂ _+_ (crankJ-dualᴹ h) (crankΣJ-dualᴹs t))
crankJ-dualᴹ (mgen x)      = refl
crankJ-dualᴹ (mjoin h t)   = cong suc (cong₂ _+_ (crankM-dualᴶ h) (crankΣM-dualᴶs t))
crankΣM-dualᴶs []          = refl
crankΣM-dualᴶs (a ∷ as)    = cong₂ _+_ (crankM-dualᴶ a) (crankΣM-dualᴶs as)
crankΣJ-dualᴹs []          = refl
crankΣJ-dualᴹs (a ∷ as)    = cong₂ _+_ (crankJ-dualᴹ a) (crankΣJ-dualᴹs as)

-- The sum of the ranks of the joinands, and of the meetands.
jrank : CTerm X → ℕ
jrank c = crankΣJ (asListJ (joinandsOf c))

mrank : CTerm X → ℕ
mrank c = crankΣM (asListM (meetandsOf c))

jrank≤crank : (c : CTerm X) → jrank c ≤ crank c
jrank≤crank (genᶜ x)     = ≤-refl
jrank≤crank (joinᶜ h t)  = n≤1+n _
jrank≤crank (meetᶜ h t)  = ≤-reflexive (cong suc (+-identityʳ _))

mrank≤crank : (c : CTerm X) → mrank c ≤ crank c
mrank≤crank (genᶜ x)     = ≤-refl
mrank≤crank (joinᶜ h t)  = ≤-reflexive (cong suc (+-identityʳ _))
mrank≤crank (meetᶜ h t)  = n≤1+n _

jrank-dualᶜ : (c : CTerm X) → jrank (dualᶜ c) ≡ mrank c
jrank-dualᶜ (genᶜ x)     = refl
jrank-dualᶜ (joinᶜ h t)  = cong (λ n → suc n + 0) (cong₂ _+_ (crankM-dualᴶ h) (crankΣM-dualᴶs t))
jrank-dualᶜ (meetᶜ h t)  = cong₂ _+_ (crankJ-dualᴹ h) (crankΣJ-dualᴹs t)

mrank-dualᶜ : (c : CTerm X) → mrank (dualᶜ c) ≡ jrank c
mrank-dualᶜ (genᶜ x)     = refl
mrank-dualᶜ (joinᶜ h t)  = cong₂ _+_ (crankM-dualᴶ h) (crankΣM-dualᴶs t)
mrank-dualᶜ (meetᶜ h t)  = cong (λ n → suc n + 0) (cong₂ _+_ (crankJ-dualᴹ h) (crankΣJ-dualᴹs t))
```

#### Canonicalization never raises the flattened rank

Fix a decision procedure for equality of generators, as the algorithm does.  The
canonical join `s ∨ᶜ t`{.AgdaFunction} collects the joinands of `s` and of `t`,
runs the loop, and collapses the result.  The loop's record carries the bound
`bound`{.AgdaField}: the rank sum of its output is at most that of its input,
which is the joinand rank of `s` plus that of `t`
(`crankΣJ-joinands∨`{.AgdaFunction}).  Collapsing a list of joinands to a term
charges at most one for the join node (`crank-collapseᴶ`{.AgdaFunction}) and
leaves the joinand rank at the rank sum of the list
(`jrank-collapseᴶ`{.AgdaFunction}).  So the rank of the canonical join is at most
one plus the joinand ranks of its arguments (`crank-∨ᶜ`{.AgdaFunction}), and its
joinand rank at most their sum (`jrank-∨ᶜ`{.AgdaFunction}); the meet is dual,
through the duality lemmas (`crank-∧ᶜ`{.AgdaFunction}, `mrank-∧ᶜ`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_
    using ( collapseᴶ ; joinands∨ ; reduce∨ ; _∨ᶜ_ ; _∧ᶜ_ ; canonical ; canonical-sound
          ; canonical-isCanonical )

  crank-collapseᴶ : (h : CJand X) (t : List (CJand X)) → crank (collapseᴶ h t) ≤ suc (crankΣJ (h ∷ t))
  crank-collapseᴶ (jgen x)     []       = n≤1+n _
  crank-collapseᴶ (jmeet h t)  []       = s≤s (≤-trans (m≤m+n _ 0) (n≤1+n _))
  crank-collapseᴶ (jgen _)     (_ ∷ _)  = ≤-refl
  crank-collapseᴶ (jmeet _ _)  (_ ∷ _)  = ≤-refl

  jrank-collapseᴶ : (h : CJand X) (t : List (CJand X)) → jrank (collapseᴶ h t) ≡ crankΣJ (h ∷ t)
  jrank-collapseᴶ (jgen x)     []       = refl
  jrank-collapseᴶ (jmeet h t)  []       = refl
  jrank-collapseᴶ (jgen _)     (_ ∷ _)  = refl
  jrank-collapseᴶ (jmeet _ _)  (_ ∷ _)  = refl

  crankΣJ-joinands∨ : (s t : CTerm X) → crankΣJ (asListJ (joinands∨ s t)) ≡ jrank s + jrank t
  crankΣJ-joinands∨ s t = crankΣJ-++ᴶ (joinandsOf s) (asListJ (joinandsOf t))

  jrank-∨ᶜ : (s t : CTerm X) → jrank (s ∨ᶜ t) ≤ jrank s + jrank t
  jrank-∨ᶜ s t =
    ≤-trans (≤-reflexive (jrank-collapseᴶ R.head R.tail))
            (≤-trans R.bound (≤-reflexive (crankΣJ-joinands∨ s t)))
    where module R = ReducedJoin (reduce∨ s t)

  crank-∨ᶜ : (s t : CTerm X) → crank (s ∨ᶜ t) ≤ suc (jrank s + jrank t)
  crank-∨ᶜ s t =
    ≤-trans (crank-collapseᴶ R.head R.tail)
            (s≤s (≤-trans R.bound (≤-reflexive (crankΣJ-joinands∨ s t))))
    where module R = ReducedJoin (reduce∨ s t)

  mrank-∧ᶜ : (s t : CTerm X) → mrank (s ∧ᶜ t) ≤ mrank s + mrank t
  mrank-∧ᶜ s t =
    ≤-trans (≤-reflexive (mrank-dualᶜ (dualᶜ s ∨ᶜ dualᶜ t)))
            (≤-trans (jrank-∨ᶜ (dualᶜ s) (dualᶜ t))
                     (≤-reflexive (cong₂ _+_ (jrank-dualᶜ s) (jrank-dualᶜ t))))

  crank-∧ᶜ : (s t : CTerm X) → crank (s ∧ᶜ t) ≤ suc (mrank s + mrank t)
  crank-∧ᶜ s t =
    ≤-trans (≤-reflexive (crank-dualᶜ (dualᶜ s ∨ᶜ dualᶜ t)))
            (≤-trans (crank-∨ᶜ (dualᶜ s) (dualᶜ t))
                     (s≤s (≤-reflexive (cong₂ _+_ (jrank-dualᶜ s) (jrank-dualᶜ t)))))
```

The bound on `canonical`{.AgdaFunction} is then an induction on the term, carried
out for the rank and the two helpers together (`canonical-rank-bound`{.AgdaFunction},
`canonical-rank∨ᶠ`{.AgdaFunction}, `canonical-rank∧ᶠ`{.AgdaFunction}): at a join
the joinand ranks of the two canonical forms are bounded by the helpers of the two
sides, and the join charges one; at a term that is not a join, the joinand rank is
at most the rank.

```agda
  canonical-rank-bound  : (t : LatTerm X) → crank (canonical t) ≤ rankᶠ t
  canonical-rank∨ᶠ      : (t : LatTerm X) → jrank (canonical t) ≤ rank∨ᶠ t
  canonical-rank∧ᶠ      : (t : LatTerm X) → mrank (canonical t) ≤ rank∧ᶠ t

  canonical-rank-bound (ℊ x)    = ≤-refl
  canonical-rank-bound (s ∨̇ t)  =
    ≤-trans (crank-∨ᶜ (canonical s) (canonical t))
            (s≤s (+-mono-≤ (canonical-rank∨ᶠ s) (canonical-rank∨ᶠ t)))
  canonical-rank-bound (s ∧̇ t)  =
    ≤-trans (crank-∧ᶜ (canonical s) (canonical t))
            (s≤s (+-mono-≤ (canonical-rank∧ᶠ s) (canonical-rank∧ᶠ t)))

  canonical-rank∨ᶠ (ℊ x)    = ≤-refl
  canonical-rank∨ᶠ (s ∨̇ t)  =
    ≤-trans (jrank-∨ᶜ (canonical s) (canonical t))
            (+-mono-≤ (canonical-rank∨ᶠ s) (canonical-rank∨ᶠ t))
  canonical-rank∨ᶠ (s ∧̇ t)  =
    ≤-trans (jrank≤crank (canonical (s ∧̇ t)))
            (≤-trans (crank-∧ᶜ (canonical s) (canonical t))
                     (s≤s (+-mono-≤ (canonical-rank∧ᶠ s) (canonical-rank∧ᶠ t))))

  canonical-rank∧ᶠ (ℊ x)    = ≤-refl
  canonical-rank∧ᶠ (s ∧̇ t)  =
    ≤-trans (mrank-∧ᶜ (canonical s) (canonical t))
            (+-mono-≤ (canonical-rank∧ᶠ s) (canonical-rank∧ᶠ t))
  canonical-rank∧ᶠ (s ∨̇ t)  =
    ≤-trans (mrank≤crank (canonical (s ∨̇ t)))
            (≤-trans (crank-∨ᶜ (canonical s) (canonical t))
                     (s≤s (+-mono-≤ (canonical-rank∨ᶠ s) (canonical-rank∨ᶠ t))))
```

#### Theorem 1.17: minimality of rank

A canonical term `C` has the least rank among all the terms representing its
element (`crank-minimal`{.AgdaFunction}): for every term `u` with `⌊ C ⌋ ≈ʷ u`,
the canonical form of `u` is related to `C` by Theorem 1.17, so it has the rank
of `C`, and it has rank at most `rankᶠ u`.  For the computed canonical form the
statement reads `crank (canonical t) ≤ rankᶠ u` for every `u` equal to `t`
(`canonical-minimal`{.AgdaFunction}); through `rankᶠ-⌊⌋`{.AgdaFunction} it is a
comparison of flattened ranks of lattice terms
(`canonical-minimal-rankᶠ`{.AgdaFunction}), and through
`rankᶠ≤rank`{.AgdaFunction} the canonical form also has rank at most the binary
rank of every term of its element (`canonical-minimal-rank`{.AgdaFunction}).

```agda
  -- Theorem 1.17, minimality: no term of the element has a smaller rank.
  crank-minimal : (C : CTerm X) → IsCanonical C → (u : LatTerm X) → ⌊ C ⌋ ≈ʷ u → crank C ≤ rankᶠ u
  crank-minimal C cC u e =
    ≤-trans (≤-reflexive (crank-≈ʷ C (canonical u) cC (canonical-isCanonical u)
                                   (≈ʷ-trans e (≈ʷ-sym (canonical-sound u)))))
            (canonical-rank-bound u)

  canonical-minimal : (t u : LatTerm X) → u ≈ʷ t → crank (canonical t) ≤ rankᶠ u
  canonical-minimal t u e =
    crank-minimal (canonical t) (canonical-isCanonical t) u (≈ʷ-trans (canonical-sound t) (≈ʷ-sym e))

  canonical-minimal-rankᶠ : (t u : LatTerm X) → u ≈ʷ t → rankᶠ ⌊ canonical t ⌋ ≤ rankᶠ u
  canonical-minimal-rankᶠ t u e =
    ≤-trans (≤-reflexive (rankᶠ-⌊⌋ (canonical-isCanonical t))) (canonical-minimal t u e)

  canonical-minimal-rank : (t u : LatTerm X) → u ≈ʷ t → rankᶠ ⌊ canonical t ⌋ ≤ rank u
  canonical-minimal-rank t u e = ≤-trans (canonical-minimal-rankᶠ t u e) (rankᶠ≤rank u)
```
