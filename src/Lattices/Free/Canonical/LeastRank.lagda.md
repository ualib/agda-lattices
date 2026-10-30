---
layout: default
file: "src/Lattices/Free/Canonical/LeastRank.lagda.md"
title: "Lattices.Free.Canonical.LeastRank module"
date: "2026-10-28"
author: "the agda-lattices development team"
---

### Terms of least rank are canonical

This is the [Lattices.Free.Canonical.LeastRank][] module of the [agda-lattices][] library.

Theorem 1.17 of [Freese, Ježek, and Nation (1995)][] says that every element of a
free lattice has a term of least rank representing it, unique up to
commutativity, its *canonical form*; Theorem 1.18 says that a term is in
canonical form exactly when it satisfies four syntactic conditions.  One
direction is proved elsewhere: a term satisfying the conditions
(`IsCanonical`{.AgdaDatatype} of [Lattices.Free.Canonical.Basic][]) has the least
rank among all the terms of its element (`crank-minimal`{.AgdaFunction} of
[Lattices.Free.Canonical.Minimality][]), and two such terms of one element are
equal up to commutativity (`≈ʷ⇒≈ᶜ`{.AgdaFunction} of
[Lattices.Free.Canonical.Uniqueness][]).  This module proves the other
direction, the necessity of the conditions, which the book calls clear and
which its proof of Theorem 1.17 argues: a term of least rank satisfies the four
conditions (`least⇒canonical`{.AgdaFunction}).  So the conditions characterize
the terms of least rank (`canonical⇔least`{.AgdaFunction}, Theorem 1.18), and
any two terms of least rank naming one element are equal up to commutativity
(`leastRank-unique`{.AgdaFunction}).  That is the uniqueness of Theorem 1.17
as the book states it, of the terms of least rank and not only of the canonical
ones, and `least-rank-form`{.AgdaFunction} states the theorem in one piece.

#### Which terms, which rank, which commutativity

The book's terms are `n`-ary (Section I.2): `x ∨ y ∨ z` is a term of rank 4 and
`x ∨ (y ∨ z)` a different term, of rank 5, since the rank counts the occurrences
of generators plus the pairs of parentheses.  The library represents terms in two
ways, and the theorem is read on each as follows.

+  **The n-ary terms** are the terms `CTerm X`{.AgdaDatatype} of
   [Lattices.Free.Canonical.Basic][], with the book's rank
   `crank`{.AgdaFunction}.  A child of a join is a generator or a meet, and a
   child of a meet is a generator or a join, so these are the book's terms in
   which no join has a join as a child and no meet a meet.  The book's other
   terms never have least rank: removing the parentheses around a join that is a
   child of a join lowers the rank by one, which is the first step of the book's
   proof of Theorem 1.17.  So the least rank among the book's terms of an
   element is the least rank among its terms in `CTerm X`{.AgdaDatatype}, over
   which `LeastRank`{.AgdaFunction} quantifies, and the book's "equivalent under
   commutativity" (Section I.3) is the relation `_≈ᶜ_`{.AgdaDatatype} on them.
   The type also has joins and meets of a single child; they never have least
   rank either, since the child alone names the same element with a smaller
   rank.
+  **The binary terms** are the lattice terms `LatTerm X`{.AgdaDatatype} of
   [Lattices.Free.Term][].  A binary term abbreviates the `n`-ary term obtained
   by collecting each maximal chain of joins, and each maximal chain of meets,
   into one node (`flat`{.AgdaFunction}).  Its rank is the rank of that term
   (`crank-flat`{.AgdaFunction}): the flattened rank `rankᶠ`{.AgdaFunction} of
   [Lattices.Free.Canonical.Minimality][], by which `crank-minimal`{.AgdaFunction}
   measures binary terms, and which is kept here (`LeastRankᶠ`{.AgdaFunction}).
   The binary rank `rank`{.AgdaFunction} of [Lattices.Free.Term][], which
   charges every binary operation, is instead the book's rank of the fully
   parenthesized reading, which is not the reading the theorem is about.
   A binary term of least rank abbreviates a canonical term
   (`leastᶠ⇒canonical`{.AgdaFunction}), and two of them naming one element
   abbreviate terms related by `_≈ᶜ_`{.AgdaDatatype}
   (`leastRankᶠ-unique`{.AgdaFunction}): the two binary terms are equal up to
   associativity, which `flat`{.AgdaFunction} forgets, and commutativity, which
   `_≈ᶜ_`{.AgdaDatatype} forgets.  The book makes the same point in a footnote
   to Section I.3: a term of least rank can be associated in only one way, which
   is why it says "unique up to commutativity" where the canonical form is
   usually said to be unique up to commutativity and associativity.

The two readings of "least rank" agree.  An `n`-ary term has the least rank
among the `n`-ary terms of its element exactly when it has it against the binary
terms measured by `rankᶠ`{.AgdaFunction} (`leastRank⇔rankᶠ`{.AgdaFunction}),
which is the form of the conclusion of `crank-minimal`{.AgdaFunction}: a binary
term flattens to an `n`-ary term of its rank, and an `n`-ary term embeds as a
binary term of rank no larger (`rankᶠ⌊⌋≤crank`{.AgdaFunction}).  And a binary
term has least rank exactly when the term it abbreviates has
(`leastᶠ⇔least-flat`{.AgdaFunction}).

#### The proof

The proof is the book's: if one of the four conditions of Theorem 1.18 fails for
a join, a term of smaller rank names the same element, so a join of least rank
satisfies all four.  Condition 1 holds by the type, as above.  A join of a single
child is not of least rank, since the child names the same element with a
smaller rank (`single-not-least`{.AgdaFunction}).  If a joinand lies below
another, dropping it keeps the join and lowers the rank, so the joinands of a join
of least rank form an antichain (`least-antichain`{.AgdaFunction}, condition 3).
If a joinand is a meet with a meetand below the whole join, replacing the meet by
the joinands of that meetand keeps the join and lowers the rank; this is the
replacement step `splice`{.AgdaFunction} of the canonicalization algorithm of
[Lattices.Free.Canonical.Algorithm][], whose soundness and rank bound give
condition 4 at once (`least-cond4`{.AgdaFunction}).  If a joinand that is a meet
were not of least rank, replacing it by the joinands of a smaller term naming it
would lower the rank of the join, so each such joinand has least rank
(`joinand-least`{.AgdaFunction}) and is canonical by induction (condition 2).  The
induction is a well-founded recursion on the rank, since a joinand has a smaller
rank than its join; it needs neither a termination pragma nor fuel.  Meets are
dual: the dual of a term of least rank has least rank, and the dual of the dual
is the term.

None of this needs decidable equality on the generators.  The characterization
`canonical⇔least`{.AgdaFunction} and the existence half of Theorem 1.17
(`least-rank-form`{.AgdaFunction}) take it, because they use the canonicalization
algorithm and `crank-minimal`{.AgdaFunction}, which take it.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Canonical.LeastRank where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ )
open import Data.List.Membership.Propositional     using ( _∈_ ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-∃++ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; tabulate )
open import Data.List.Relation.Unary.AllPairs      using ( AllPairs ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( suc ; _+_ ; _≤_ ; _<_ ; s≤s ; z≤n )
open import Data.Nat.Induction                     using ( <-wellFounded )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-reflexive ; ≤-trans ; ≤-<-trans
                                                         ; ≤⇒≯ ; ≮⇒≥ ; m≤m+n ; m≤n+m ; m<n+m
                                                         ; n≤1+n ; +-mono-≤ ; +-monoˡ-< ; +-monoʳ-<
                                                         ; +-identityʳ ; +-assoc )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ ; Σ-syntax )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( _⇔_ ; mk⇔ )
open import Induction.WellFounded                  using ( Acc ; acc )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂
                                                         ; subst ; subst₂ )
open import Relation.Nullary                       using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm
  using  ( module Canonicalization ; _++ᴶ_ ; crankΣJ-++ᴶ ; ∈-++ᴶ⁻ ; ∈-++ᴶ⁺ʳ ; ⋁ᴶL-++ᴶ-upper
         ; ⋁ᴶ-++ ; ∈⇒≤-Any ; splice ; splice-sound ; splice-μ ; irreducible→Cond4J )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin
         ; ⌊_⌋ ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋁ᴶ ; ⋀ᴹ ; crank ; crankJ ; crankM ; crankΣJ ; crankΣM
         ; ≈ʷ-refl ; ≈ʷ-sym ; ≈ʷ-trans ; ∨̇-cong ; ∧̇-cong ; ∧̇-assoc ; ⋁ᴶ-upper ; ⋁ᴶ-least
         ; ⋁ᴶ-dom ; AntichainJ ; Cond4J ; IsCanonical ; cgen ; cjoin ; cmeet ; IsCanonicalJ ; cjgen
         ; cjmeet ; IsCanonicalM ; cmgen ; cmjoin ; JList ; MList ; asListJ ; asListM ; ⋁ᴶL ; ⋀ᴹL ; joinandsOf
         ; joinandsOf-sound ; dualᶜ ; dualᴶ ; dualᴹ ; dualᴶs ; dualᴹs ; ⌊dualᶜ⌋
         ; dualᶜ-canonical )
open import Lattices.Free.Canonical.Minimality
  using  ( rankᶠ ; rank∨ᶠ ; rank∧ᶠ ; crank-dualᶜ ; jrank≤crank ; crank-minimal )
open import Lattices.Free.Canonical.Uniqueness
  using  ( _≈ᶜ_ ; ≈ʷ⇒≈ᶜ ; Any-mid⁻ ; Any-mid⁺ )
open import Lattices.Free.Duality  using ( dual-cong ; dual-involutive )
open import Lattices.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ∨≤-inv ; ≤ʷ-refl ; ≤ʷ-trans ; ∨̇-upperˡ ; ∨̇-upperʳ )

private variable
  ℓ ℓ' χ : Level
  A : Type ℓ
  X : Type χ
```
-->

#### Least rank

`LeastRank C`{.AgdaFunction} says that the `n`-ary term `C` has the least rank
among the `n`-ary terms of its element: every term `D` naming the element of `C`
has rank at least that of `C`.  `LeastRankᶠ u`{.AgdaFunction} says the same of a
binary term `u`, among the binary terms, by the flattened rank.

```agda
-- C has the least rank among the n-ary terms of its element.
LeastRank : {X : Type χ} → CTerm X → Type χ
LeastRank C = ∀ D → ⌊ C ⌋ ≈ʷ ⌊ D ⌋ → crank C ≤ crank D

-- u has the least flattened rank among the binary terms of its element.
LeastRankᶠ : {X : Type χ} → LatTerm X → Type χ
LeastRankᶠ u = ∀ v → u ≈ʷ v → rankᶠ u ≤ rankᶠ v
```

#### The n-ary term a binary term abbreviates

A nonempty list of joinands is a `JList`{.AgdaFunction}, and its join is a term
(`joinᶜL`{.AgdaFunction}) or, as a single meetand, a child of a meet
(`mjoinL`{.AgdaFunction}); dually for meetands.  Appending a list of meetands
(`_++ᴹ_`{.AgdaFunction}) is the dual of `_++ᴶ_`{.AgdaFunction} of
[Lattices.Free.Canonical.Algorithm][]: it adds the rank sums
(`crankΣM-++ᴹ`{.AgdaFunction}), and the meet of a concatenation is the meet of
the two meets (`⋀ᴹL-++`{.AgdaFunction}), as the join of a concatenation of
joinands is the join of the two joins (`⋁ᴶL-++`{.AgdaFunction}).

```agda
-- A list of joinands as a term, and as a meetand; dually for meetands.
joinᶜL : JList X → CTerm X
joinᶜL (h , t) = joinᶜ h t

meetᶜL : MList X → CTerm X
meetᶜL (h , t) = meetᶜ h t

mjoinL : JList X → CMand X
mjoinL (h , t) = mjoin h t

jmeetL : MList X → CJand X
jmeetL (h , t) = jmeet h t

infixr 5 _++ᴹ_

-- Appending a list of meetands.
_++ᴹ_ : MList X → List (CMand X) → MList X
(h , t) ++ᴹ u = h , t ++ u

-- The rank sum of a concatenation of meetands.
crankΣM-++ : (as bs : List (CMand X)) → crankΣM (as ++ bs) ≡ crankΣM as + crankΣM bs
crankΣM-++ []        bs = refl
crankΣM-++ (a ∷ as)  bs =
  trans (cong (crankM a +_) (crankΣM-++ as bs)) (sym (+-assoc (crankM a) (crankΣM as) _))

crankΣM-++ᴹ : (P : MList X) (u : List (CMand X))
  → crankΣM (asListM (P ++ᴹ u)) ≡ crankΣM (asListM P) + crankΣM u
crankΣM-++ᴹ (h , t) u = crankΣM-++ (h ∷ t) u

-- The meet of a concatenation is the meet of the two meets.
⋀ᴹ-++ : (h : CMand X) (t : List (CMand X)) (u : CMand X) (us : List (CMand X))
  → ⋀ᴹ h (t ++ u ∷ us) ≈ʷ ⋀ᴹ h t ∧̇ ⋀ᴹ u us
⋀ᴹ-++ h []        u us = ≈ʷ-refl
⋀ᴹ-++ h (a ∷ as)  u us = ≈ʷ-trans (∧̇-cong ≈ʷ-refl (⋀ᴹ-++ a as u us)) (≈ʷ-sym ∧̇-assoc)

⋀ᴹL-++ : (P Q : MList X) → ⋀ᴹL (P ++ᴹ asListM Q) ≈ʷ ⋀ᴹL P ∧̇ ⋀ᴹL Q
⋀ᴹL-++ (h , t) (h' , t') = ⋀ᴹ-++ h t h' t'

-- The join of a concatenation is the join of the two joins.
⋁ᴶL-++ : (P Q : JList X) → ⋁ᴶL (P ++ᴶ asListJ Q) ≈ʷ ⋁ᴶL P ∨̇ ⋁ᴶL Q
⋁ᴶL-++ (h , t) (h' , t') = ⋁ᴶ-++ h t h' t'
```

`flat u`{.AgdaFunction} is the `n`-ary term the binary term `u` abbreviates.  Its
joinands, `flatᴶ u`{.AgdaFunction}, are those of the two sides when `u` is a join
and `u` itself, flattened, otherwise; its meetands, `flatᴹ u`{.AgdaFunction}, are
dual.  Each clause recurses on the immediate subterms, so that the two functions
are structural.

```agda
-- The joinands and the meetands of the n-ary term a binary term abbreviates.
flatᴶ : LatTerm X → JList X
flatᴹ : LatTerm X → MList X

flatᴶ (ℊ x) = jgen x , []
flatᴶ (s ∨̇ t) = flatᴶ s ++ᴶ asListJ (flatᴶ t)
flatᴶ (s ∧̇ t) = jmeetL (flatᴹ s ++ᴹ asListM (flatᴹ t)) , []

flatᴹ (ℊ x) = mgen x , []
flatᴹ (s ∧̇ t) = flatᴹ s ++ᴹ asListM (flatᴹ t)
flatᴹ (s ∨̇ t) = mjoinL (flatᴶ s ++ᴶ asListJ (flatᴶ t)) , []

-- The n-ary term a binary term abbreviates.
flat : LatTerm X → CTerm X
flat (ℊ x) = genᶜ x
flat (s ∨̇ t) = joinᶜL (flatᴶ (s ∨̇ t))
flat (s ∧̇ t) = meetᶜL (flatᴹ (s ∧̇ t))
```

The rank of `flat u`{.AgdaFunction} is the flattened rank of `u`
(`crank-flat`{.AgdaFunction}), which confirms that `rankᶠ`{.AgdaFunction} is the
book's rank of the term `u` abbreviates: the rank sum of the joinands is
`rank∨ᶠ u`{.AgdaFunction} and that of the meetands `rank∧ᶠ u`{.AgdaFunction}.
And `flat u`{.AgdaFunction} names the element of `u`
(`flat-sound`{.AgdaFunction}), since it only reassociates.

```agda
-- The rank of the n-ary term a binary term abbreviates is its flattened rank.
crank-flat : (u : LatTerm X) → crank (flat u) ≡ rankᶠ u
crankΣJ-flatᴶ : (u : LatTerm X) → crankΣJ (asListJ (flatᴶ u)) ≡ rank∨ᶠ u
crankΣM-flatᴹ : (u : LatTerm X) → crankΣM (asListM (flatᴹ u)) ≡ rank∧ᶠ u

crank-flat (ℊ x) = refl
crank-flat (s ∨̇ t) = cong suc (crankΣJ-flatᴶ (s ∨̇ t))
crank-flat (s ∧̇ t) = cong suc (crankΣM-flatᴹ (s ∧̇ t))

crankΣJ-flatᴶ (ℊ x) = refl
crankΣJ-flatᴶ (s ∨̇ t) =
  trans  (crankΣJ-++ᴶ (flatᴶ s) (asListJ (flatᴶ t)))
         (cong₂ _+_ (crankΣJ-flatᴶ s) (crankΣJ-flatᴶ t))
crankΣJ-flatᴶ (s ∧̇ t) =
  trans  (+-identityʳ _)
         (cong suc (trans  (crankΣM-++ᴹ (flatᴹ s) (asListM (flatᴹ t)))
                           (cong₂ _+_ (crankΣM-flatᴹ s) (crankΣM-flatᴹ t))))

crankΣM-flatᴹ (ℊ x) = refl
crankΣM-flatᴹ (s ∧̇ t) =
  trans  (crankΣM-++ᴹ (flatᴹ s) (asListM (flatᴹ t)))
         (cong₂ _+_ (crankΣM-flatᴹ s) (crankΣM-flatᴹ t))
crankΣM-flatᴹ (s ∨̇ t)  =
  trans  (+-identityʳ _)
         (cong suc (trans  (crankΣJ-++ᴶ (flatᴶ s) (asListJ (flatᴶ t)))
                           (cong₂ _+_ (crankΣJ-flatᴶ s) (crankΣJ-flatᴶ t))))

-- The n-ary term a binary term abbreviates names the same element.
flat-sound : (u : LatTerm X) → ⌊ flat u ⌋ ≈ʷ u
flatᴶ-sound : (u : LatTerm X) → ⋁ᴶL (flatᴶ u) ≈ʷ u
flatᴹ-sound : (u : LatTerm X) → ⋀ᴹL (flatᴹ u) ≈ʷ u

flat-sound (ℊ x) = ≈ʷ-refl
flat-sound (s ∨̇ t) = flatᴶ-sound (s ∨̇ t)
flat-sound (s ∧̇ t) = flatᴹ-sound (s ∧̇ t)

flatᴶ-sound (ℊ x) = ≈ʷ-refl
flatᴶ-sound (s ∨̇ t) =
  ≈ʷ-trans (⋁ᴶL-++ (flatᴶ s) (flatᴶ t)) (∨̇-cong (flatᴶ-sound s) (flatᴶ-sound t))
flatᴶ-sound (s ∧̇ t) =
  ≈ʷ-trans (⋀ᴹL-++ (flatᴹ s) (flatᴹ t)) (∧̇-cong (flatᴹ-sound s) (flatᴹ-sound t))

flatᴹ-sound (ℊ x) = ≈ʷ-refl
flatᴹ-sound (s ∧̇ t) =
  ≈ʷ-trans (⋀ᴹL-++ (flatᴹ s) (flatᴹ t)) (∧̇-cong (flatᴹ-sound s) (flatᴹ-sound t))
flatᴹ-sound (s ∨̇ t) =
  ≈ʷ-trans (⋁ᴶL-++ (flatᴶ s) (flatᴶ t)) (∨̇-cong (flatᴶ-sound s) (flatᴶ-sound t))
```

On a canonical term, `flat`{.AgdaFunction} inverts the embedding
(`flat-⌊⌋`{.AgdaFunction}): the binary term `⌊ C ⌋`{.AgdaFunction} abbreviates
`C`.  The induction runs on the canonicity proof, which supplies the
nonemptiness of every tail, as in `rankᶠ-⌊⌋`{.AgdaFunction}: a join of a single
child embeds as the child, which flattens to the child alone.

```agda
-- A canonical term is the n-ary term its embedding abbreviates.
flat-⌊⌋ : {C : CTerm X} → IsCanonical C → flat ⌊ C ⌋ ≡ C
flatᴶ-⌊⌋ᴶ : {a : CJand X} → IsCanonicalJ a → flatᴶ ⌊ a ⌋ᴶ ≡ (a , [])
flatᴹ-⌊⌋ᴹ : {a : CMand X} → IsCanonicalM a → flatᴹ ⌊ a ⌋ᴹ ≡ (a , [])

flatᴶ-⋁ᴶ : {h : CJand X} {t : List (CJand X)}
  → All IsCanonicalJ (h ∷ t) → flatᴶ (⋁ᴶ h t) ≡ (h , t)

flatᴹ-⋀ᴹ : {h : CMand X} {t : List (CMand X)}
  → All IsCanonicalM (h ∷ t) → flatᴹ (⋀ᴹ h t) ≡ (h , t)

flat-⌊⌋ cgen = refl
flat-⌊⌋ (cjoin {jt = []}     ne _  _ _) = ⊥-elim (ne refl)
flat-⌊⌋ (cjoin {jt = _ ∷ _}  _  cs _ _) = cong joinᶜL (flatᴶ-⋁ᴶ cs)
flat-⌊⌋ (cmeet {mt = []}     ne _  _ _) = ⊥-elim (ne refl)
flat-⌊⌋ (cmeet {mt = _ ∷ _}  _  cs _ _) = cong meetᶜL (flatᴹ-⋀ᴹ cs)

flatᴶ-⌊⌋ᴶ cjgen = refl
flatᴶ-⌊⌋ᴶ (cjmeet (cmeet {mt = []}     ne _  _ _)) = ⊥-elim (ne refl)
flatᴶ-⌊⌋ᴶ (cjmeet (cmeet {mt = _ ∷ _}  _  cs _ _)) =
  cong (λ M → jmeetL M , []) (flatᴹ-⋀ᴹ cs)

flatᴹ-⌊⌋ᴹ cmgen = refl
flatᴹ-⌊⌋ᴹ (cmjoin (cjoin {jt = []} ne _ _ _)) = ⊥-elim (ne refl)
flatᴹ-⌊⌋ᴹ (cmjoin (cjoin {jt = _ ∷ _} _ cs _ _)) =
  cong (λ P → mjoinL P , []) (flatᴶ-⋁ᴶ cs)

flatᴶ-⋁ᴶ {t = []} (c ∷ []) = flatᴶ-⌊⌋ᴶ c
flatᴶ-⋁ᴶ {t = _ ∷ _} (c ∷ cs) =
  cong₂ (λ P Q → P ++ᴶ asListJ Q) (flatᴶ-⌊⌋ᴶ c) (flatᴶ-⋁ᴶ cs)

flatᴹ-⋀ᴹ {t = []} (c ∷ []) = flatᴹ-⌊⌋ᴹ c
flatᴹ-⋀ᴹ {t = _ ∷ _} (c ∷ cs) =
  cong₂ (λ P Q → P ++ᴹ asListM Q) (flatᴹ-⌊⌋ᴹ c) (flatᴹ-⋀ᴹ cs)
```

#### The embedding never raises the rank

An `n`-ary term embeds as a binary term of flattened rank at most its rank
(`rankᶠ⌊⌋≤crank`{.AgdaFunction}).  For a canonical term the two are equal
(`rankᶠ-⌊⌋`{.AgdaFunction} of [Lattices.Free.Canonical.Minimality][]); in
general they are not, since a join of a single child embeds as the child, of
smaller rank.  The bound is an induction on the term, through the helpers of the
flattened rank, each of which lies between the flattened rank less one and the
flattened rank: it is at most the flattened rank (`rank∨ᶠ≤rankᶠ`{.AgdaFunction}),
and the flattened rank is at most one more than it
(`rankᶠ≤suc-rank∨ᶠ`{.AgdaFunction}); dually for meets.

```agda
-- The helpers of the flattened rank lie between it and one less.
rank∨ᶠ≤rankᶠ : (s : LatTerm X) → rank∨ᶠ s ≤ rankᶠ s
rank∨ᶠ≤rankᶠ (ℊ x)    = ≤-refl
rank∨ᶠ≤rankᶠ (s ∨̇ t)  = n≤1+n _
rank∨ᶠ≤rankᶠ (s ∧̇ t)  = ≤-refl

rank∧ᶠ≤rankᶠ : (s : LatTerm X) → rank∧ᶠ s ≤ rankᶠ s
rank∧ᶠ≤rankᶠ (ℊ x)    = ≤-refl
rank∧ᶠ≤rankᶠ (s ∧̇ t)  = n≤1+n _
rank∧ᶠ≤rankᶠ (s ∨̇ t)  = ≤-refl

rankᶠ≤suc-rank∨ᶠ : (s : LatTerm X) → rankᶠ s ≤ suc (rank∨ᶠ s)
rankᶠ≤suc-rank∨ᶠ (ℊ x)    = n≤1+n 1
rankᶠ≤suc-rank∨ᶠ (s ∨̇ t)  = ≤-refl
rankᶠ≤suc-rank∨ᶠ (s ∧̇ t)  = n≤1+n _

rankᶠ≤suc-rank∧ᶠ : (s : LatTerm X) → rankᶠ s ≤ suc (rank∧ᶠ s)
rankᶠ≤suc-rank∧ᶠ (ℊ x)    = n≤1+n 1
rankᶠ≤suc-rank∧ᶠ (s ∧̇ t)  = ≤-refl
rankᶠ≤suc-rank∧ᶠ (s ∨̇ t)  = n≤1+n _

-- The embedding of an n-ary term has flattened rank at most its rank.
rankᶠ⌊⌋≤crank : (C : CTerm X) → rankᶠ ⌊ C ⌋ ≤ crank C
rankᶠ⌊⌋ᴶ≤crankJ : (a : CJand X) → rankᶠ ⌊ a ⌋ᴶ ≤ crankJ a
rankᶠ⌊⌋ᴹ≤crankM : (a : CMand X) → rankᶠ ⌊ a ⌋ᴹ ≤ crankM a

rankᶠ-⋁ᴶ≤ : (h : CJand X) (t : List (CJand X))
  → rankᶠ (⋁ᴶ h t) ≤ suc (crankJ h + crankΣJ t)

rankᶠ-⋀ᴹ≤ : (h : CMand X) (t : List (CMand X))
  → rankᶠ (⋀ᴹ h t) ≤ suc (crankM h + crankΣM t)

rank∨ᶠ-⋁ᴶ≤ : (h : CJand X) (t : List (CJand X))
  → rank∨ᶠ (⋁ᴶ h t) ≤ crankJ h + crankΣJ t

rank∧ᶠ-⋀ᴹ≤ : (h : CMand X) (t : List (CMand X))
  → rank∧ᶠ (⋀ᴹ h t) ≤ crankM h + crankΣM t

rankᶠ⌊⌋≤crank (genᶜ x) = ≤-refl
rankᶠ⌊⌋≤crank (joinᶜ h t) = rankᶠ-⋁ᴶ≤ h t
rankᶠ⌊⌋≤crank (meetᶜ h t) = rankᶠ-⋀ᴹ≤ h t

rankᶠ⌊⌋ᴶ≤crankJ (jgen x)     = ≤-refl
rankᶠ⌊⌋ᴶ≤crankJ (jmeet h t)  = rankᶠ-⋀ᴹ≤ h t

rankᶠ⌊⌋ᴹ≤crankM (mgen x)     = ≤-refl
rankᶠ⌊⌋ᴹ≤crankM (mjoin h t)  = rankᶠ-⋁ᴶ≤ h t

rankᶠ-⋁ᴶ≤ h t = ≤-trans (rankᶠ≤suc-rank∨ᶠ (⋁ᴶ h t)) (s≤s (rank∨ᶠ-⋁ᴶ≤ h t))

rankᶠ-⋀ᴹ≤ h t = ≤-trans (rankᶠ≤suc-rank∧ᶠ (⋀ᴹ h t)) (s≤s (rank∧ᶠ-⋀ᴹ≤ h t))

rank∨ᶠ-⋁ᴶ≤ h [] =
  ≤-trans (rank∨ᶠ≤rankᶠ ⌊ h ⌋ᴶ) (≤-trans (rankᶠ⌊⌋ᴶ≤crankJ h) (m≤m+n _ 0))
rank∨ᶠ-⋁ᴶ≤ h (a ∷ as) =
  +-mono-≤ (≤-trans (rank∨ᶠ≤rankᶠ ⌊ h ⌋ᴶ) (rankᶠ⌊⌋ᴶ≤crankJ h)) (rank∨ᶠ-⋁ᴶ≤ a as)

rank∧ᶠ-⋀ᴹ≤ h [] = ≤-trans (rank∧ᶠ≤rankᶠ ⌊ h ⌋ᴹ) (≤-trans (rankᶠ⌊⌋ᴹ≤crankM h) (m≤m+n _ 0))
rank∧ᶠ-⋀ᴹ≤ h (a ∷ as) =
  +-mono-≤ (≤-trans (rank∧ᶠ≤rankᶠ ⌊ h ⌋ᴹ) (rankᶠ⌊⌋ᴹ≤crankM h)) (rank∧ᶠ-⋀ᴹ≤ a as)
```

#### The readings of least rank agree

An `n`-ary term has the least rank among the `n`-ary terms of its element exactly
when its rank is at most the flattened rank of every binary term of its element
(`leastRank⇔rankᶠ`{.AgdaFunction}), the form in which
`crank-minimal`{.AgdaFunction} states minimality.  One way, a binary term flattens
to an `n`-ary term of its rank; the other, an `n`-ary term embeds as a binary
term of rank no larger.  For the same two reasons a binary term has least rank
exactly when the term it abbreviates has (`leastᶠ⇔least-flat`{.AgdaFunction}).

```agda
module _ {X : Type χ} where

  -- Least rank among n-ary terms bounds the flattened rank of every binary term.
  least⇒rankᶠ : (C : CTerm X) → LeastRank C → ∀ u → ⌊ C ⌋ ≈ʷ u → crank C ≤ rankᶠ u
  least⇒rankᶠ C lr u e =
    ≤-trans (lr (flat u) (≈ʷ-trans e (≈ʷ-sym (flat-sound u)))) (≤-reflexive (crank-flat u))

  -- A bound by the flattened rank of every binary term is least rank.
  rankᶠ⇒least : (C : CTerm X) → (∀ u → ⌊ C ⌋ ≈ʷ u → crank C ≤ rankᶠ u) → LeastRank C
  rankᶠ⇒least C f D e = ≤-trans (f ⌊ D ⌋ e) (rankᶠ⌊⌋≤crank D)

  -- The two readings of least rank for an n-ary term.
  leastRank⇔rankᶠ : (C : CTerm X) → LeastRank C ⇔ (∀ u → ⌊ C ⌋ ≈ʷ u → crank C ≤ rankᶠ u)
  leastRank⇔rankᶠ C = mk⇔ (least⇒rankᶠ C) (rankᶠ⇒least C)

  -- A binary term of least rank abbreviates an n-ary term of least rank, and conversely.
  leastᶠ⇒least-flat : (u : LatTerm X) → LeastRankᶠ u → LeastRank (flat u)
  leastᶠ⇒least-flat u lr D e =
    ≤-trans (≤-reflexive (crank-flat u))
            (≤-trans (lr ⌊ D ⌋ (≈ʷ-trans (≈ʷ-sym (flat-sound u)) e)) (rankᶠ⌊⌋≤crank D))

  least-flat⇒leastᶠ : (u : LatTerm X) → LeastRank (flat u) → LeastRankᶠ u
  least-flat⇒leastᶠ u lr v e =
    subst₂ _≤_ (crank-flat u) (crank-flat v)
           (lr (flat v) (≈ʷ-trans (flat-sound u) (≈ʷ-trans e (≈ʷ-sym (flat-sound v)))))

  -- A binary term has least rank exactly when the term it abbreviates has.
  leastᶠ⇔least-flat : (u : LatTerm X) → LeastRankᶠ u ⇔ LeastRank (flat u)
  leastᶠ⇔least-flat u = mk⇔ (leastᶠ⇒least-flat u) (least-flat⇒leastᶠ u)
```

#### Terms of smaller rank

A term of smaller rank naming the same element refutes least rank
(`not-least`{.AgdaFunction}).  For a join the smaller term is usually another
list of joinands with the same join and a smaller rank sum
(`smaller-join`{.AgdaFunction}).

```agda
-- A term of smaller rank naming the same element refutes least rank.
not-least : (C D : CTerm X) → ⌊ C ⌋ ≈ʷ ⌊ D ⌋ → crank D < crank C → ¬ LeastRank C
not-least C D e lt lr = ≤⇒≯ (lr D e) lt

-- A list of joinands with the same join and a smaller rank sum refutes least rank.
smaller-join : (h : CJand X) (t : List (CJand X)) (P : JList X)
  → ⋁ᴶL P ≈ʷ ⋁ᴶ h t → crankΣJ (asListJ P) < crankΣJ (h ∷ t) → ¬ LeastRank (joinᶜ h t)
smaller-join h t P e lt = not-least (joinᶜ h t) (joinᶜL P) (≈ʷ-sym e) (s≤s lt)
```

#### The conditions, one at a time

**A join has at least two joinands**.  A join of one joinand names the element of
the joinand, whose rank is smaller (`single-not-least`{.AgdaFunction}).

```agda
-- A join of a single joinand is not of least rank.
single-not-least : (h : CJand X) → ¬ LeastRank (joinᶜ h [])
single-not-least (jgen x) =
  not-least (joinᶜ (jgen x) []) (genᶜ x) ≈ʷ-refl (s≤s (m≤m+n 1 0))
single-not-least (jmeet h t) =
  not-least (joinᶜ (jmeet h t) []) (meetᶜ h t) ≈ʷ-refl (s≤s (m≤m+n _ 0))
```

**Condition 4**.  A meetand below the whole join makes its meet reducible, and the
replacement step of the canonicalization algorithm, `splice`{.AgdaFunction},
replaces the meet by the joinands of that meetand, keeping the join
(`splice-sound`{.AgdaFunction}) and lowering the rank sum
(`splice-μ`{.AgdaFunction}).  So a join of least rank has no reducible joinand,
which is condition 4 (`least-cond4`{.AgdaFunction}).

```agda
-- Condition 4 holds for a join of least rank.
least-cond4 : (h : CJand X) (t : List (CJand X)) → LeastRank (joinᶜ h t) → Cond4J h t
least-cond4 h t lr =
  irreducible→Cond4J λ r → smaller-join h t (splice r) (splice-sound r) (splice-μ r) lr
```

**Condition 3**.  A list is an antichain when no member is related to a member at
another position (`antichain-by`{.AgdaFunction}), the positions given by a
decomposition `ys ++ a ∷ zs`{.AgdaFunction} of the list, with the other member
in `ys ++ zs`{.AgdaFunction}.  For the joinands of a join, dropping a joinand
`a` that lies below another leaves a list `ys ++ zs`{.AgdaFunction} that has the
same join (every member of the one lies below a member of the other) and a
smaller rank sum, since every joinand has positive rank
(`crankΣJ-drop`{.AgdaFunction}).  So the joinands of a join of least rank form an
antichain (`least-antichain`{.AgdaFunction}).

```agda
-- No member related to a member at another position: an antichain.
antichain-by : {R : A → A → Type ℓ'} {xs : List A}
  → (∀ {ys zs a b} → xs ≡ ys ++ a ∷ zs → b ∈ ys ++ zs → ¬ R a b)
  → AllPairs (λ a b → ¬ R a b × ¬ R b a) xs
antichain-by {xs = []}      f = []
antichain-by {xs = u ∷ us}  f =
  tabulate (λ b∈ →  f {[]} {us} refl b∈
                    , λ b≤u →  let (ys , zs , e) = ∈-∃++ b∈
                               in f {u ∷ ys} {zs} (cong (u ∷_) e) (here refl) b≤u)
  ∷ antichain-by (λ {ys} {zs} e b∈ → f {u ∷ ys} {zs} (cong (u ∷_) e) (there b∈))

-- Every joinand has positive rank, so dropping one lowers the rank sum.
crankJ-pos : (a : CJand X) → 0 < crankJ a
crankJ-pos (jgen x)     = s≤s z≤n
crankJ-pos (jmeet h t)  = s≤s z≤n

crankΣJ-drop : (ys : List (CJand X)) {zs : List (CJand X)} (a : CJand X)
             → crankΣJ (ys ++ zs) < crankΣJ (ys ++ a ∷ zs)
crankΣJ-drop [] a = m<n+m _ (crankJ-pos a)
crankΣJ-drop (y ∷ ys) a = +-monoʳ-< (crankJ y) (crankΣJ-drop ys a)

-- A sublist of joinands that dominates the list has the same join.
drop-to : (h : CJand X) (t : List (CJand X)) {b : CJand X} {bs : List (CJand X)} → b ∈ bs
  → (∀ {c} → c ∈ bs → c ∈ (h ∷ t))
  → (∀ {c} → c ∈ (h ∷ t) → Any (λ d → ⌊ c ⌋ᴶ ≤ʷ ⌊ d ⌋ᴶ) bs)
  → crankΣJ bs < crankΣJ (h ∷ t) → ¬ LeastRank (joinᶜ h t)
drop-to h t {bs = []} ()
drop-to h t {bs = c ∷ cs} _ sub dom lt =
  smaller-join h t (c , cs) (⋁ᴶ-dom (λ d∈ → ∈⇒≤-Any (sub d∈)) , ⋁ᴶ-dom dom) lt

-- Dropping a joinand that lies below another keeps the join and lowers the rank.
drop-below : (h : CJand X) (t : List (CJand X)) {a b : CJand X} (ys : List (CJand X))
  {zs : List (CJand X)}
  → h ∷ t ≡ ys ++ a ∷ zs
  → b ∈ ys ++ zs
  → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ
  → ¬ LeastRank (joinᶜ h t)
drop-below h t {a} ys {zs} e b∈ a≤b =
  drop-to  h t b∈ (λ {c} c∈ → subst (c ∈_) (sym e) (Any-mid⁺ ys c∈))
           (λ {c} c∈ →  [ (λ { refl → lose b∈ a≤b }) , ∈⇒≤-Any ]′
                        (Any-mid⁻ ys (subst (c ∈_) e c∈)) )
           (subst (crankΣJ (ys ++ zs) <_) (cong crankΣJ (sym e)) (crankΣJ-drop ys a))

-- Condition 3 holds for a join of least rank.
least-antichain : (h : CJand X) (t : List (CJand X))
  → LeastRank (joinᶜ h t) → AntichainJ (h ∷ t)
least-antichain h t lr =
  antichain-by  {R = λ a b → ⌊ a ⌋ᴶ ≤ʷ ⌊ b ⌋ᴶ}
                λ {ys} e b∈ a≤b → drop-below h t ys e b∈ a≤b lr
```

**Condition 2**.  `replaceAt i P`{.AgdaFunction} replaces the joinand at the
position `i` by the list of joinands `P`, as `splice`{.AgdaFunction} does for a
reducible joinand.  If `P` names the replaced joinand, the join is unchanged
(`replaceAt-sound`{.AgdaFunction}, from a bound in each direction,
`replaceAt-≤`{.AgdaFunction} and `replaceAt-≥`{.AgdaFunction}), and if `P` has a
smaller rank sum, so has the result (`replaceAt-μ`{.AgdaFunction}).  A term `D`
naming a joinand gives the list of its own joinands, of rank sum at most the rank
of `D`.  So a meet among the joinands of a join of least rank has least rank
(`joinand-least`{.AgdaFunction}): a term of smaller rank naming it would lower
the rank of the join.

```agda
-- Replace the joinand at a position by a list of joinands.
replaceAt : {h a : CJand X} {t : List (CJand X)} → a ∈ (h ∷ t) → JList X → JList X
replaceAt {t = t} (here refl)  P = P ++ᴶ t
replaceAt {t = []} (there ())
replaceAt {h = h} {t = _ ∷ _} (there i) P = h , asListJ (replaceAt i P)

-- The two bounds of the join after a replacement.
replaceAt-≤ : {z : LatTerm X} {h a : CJand X} {t : List (CJand X)}
  (i : a ∈ (h ∷ t)) (P : JList X) → ⋁ᴶL P ≤ʷ z → ⋁ᴶ h t ≤ʷ z → ⋁ᴶL (replaceAt i P) ≤ʷ z
replaceAt-≤ (here refl) P p q =
  ⋁ᴶ-least λ c∈ → [ (λ c∈P → ≤ʷ-trans (⋁ᴶ-upper c∈P) p)
                  , (λ c∈t → ≤ʷ-trans (⋁ᴶ-upper (there c∈t)) q) ]′ (∈-++ᴶ⁻ P c∈)
replaceAt-≤ {t = []} (there ())
replaceAt-≤ {t = _ ∷ _} (there i) P p q =
  ∨≤ (proj₁ (∨≤-inv q)) (replaceAt-≤ i P p (proj₂ (∨≤-inv q)))

replaceAt-≥ : {h a : CJand X} {t : List (CJand X)} (i : a ∈ (h ∷ t)) (P : JList X)
  → ⌊ a ⌋ᴶ ≤ʷ ⋁ᴶL P → ⋁ᴶ h t ≤ʷ ⋁ᴶL (replaceAt i P)
replaceAt-≥ (here refl) P p =
  ⋁ᴶ-least λ  { (here refl)  → ≤ʷ-trans p (⋁ᴶL-++ᴶ-upper P)
              ; (there c∈t)  → ⋁ᴶ-upper (∈-++ᴶ⁺ʳ P c∈t) }
replaceAt-≥ {t = []} (there ()) _ _
replaceAt-≥ {t = _ ∷ _} (there i) P p =
  ∨≤ ∨̇-upperˡ (≤ʷ-trans (replaceAt-≥ i P p) ∨̇-upperʳ)

-- Replacing a joinand by a list that names it keeps the join.
replaceAt-sound : {h a : CJand X} {t : List (CJand X)} (i : a ∈ (h ∷ t)) (P : JList X)
  → ⋁ᴶL P ≈ʷ ⌊ a ⌋ᴶ → ⋁ᴶL (replaceAt i P) ≈ʷ ⋁ᴶ h t
replaceAt-sound i P (p , q) =
  replaceAt-≤ i P (≤ʷ-trans p (⋁ᴶ-upper i)) ≤ʷ-refl , replaceAt-≥ i P q

-- Replacing a joinand by a list of smaller rank sum lowers the rank sum.
replaceAt-μ : {h a : CJand X} {t : List (CJand X)} (i : a ∈ (h ∷ t)) (P : JList X)
  → crankΣJ (asListJ P) < crankJ a → crankΣJ (asListJ (replaceAt i P)) < crankΣJ (h ∷ t)
replaceAt-μ {h = h} {t = t} (here refl) P lt =
  subst (_< crankΣJ (h ∷ t)) (sym (crankΣJ-++ᴶ P t)) (+-monoˡ-< (crankΣJ t) lt)
replaceAt-μ {t = []} (there ())
replaceAt-μ {h = h} {t = _ ∷ _} (there i) P lt = +-monoʳ-< (crankJ h) (replaceAt-μ i P lt)

-- A joinand has smaller rank than its join.
∈-≤-crankΣJ : {a : CJand X} {as : List (CJand X)} → a ∈ as → crankJ a ≤ crankΣJ as
∈-≤-crankΣJ (here refl)  = m≤m+n _ _
∈-≤-crankΣJ (there a∈)   = ≤-trans (∈-≤-crankΣJ a∈) (m≤n+m _ _)

-- A meet among the joinands of a join of least rank has least rank.
joinand-least : (h : CJand X) (t : List (CJand X)) {mh : CMand X} {mt : List (CMand X)}
  → jmeet mh mt ∈ (h ∷ t) → LeastRank (joinᶜ h t) → LeastRank (meetᶜ mh mt)
joinand-least h t {mh} {mt} i lr D e = ≮⇒≥ λ lt →
  smaller-join h t
    (replaceAt i (joinandsOf D))
    (replaceAt-sound i (joinandsOf D)
      (subst (_≈ʷ ⋀ᴹ mh mt) (sym (joinandsOf-sound D)) (≈ʷ-sym e)))
    (replaceAt-μ i (joinandsOf D) (≤-<-trans (jrank≤crank D) lt))
    lr
```

#### A term of least rank is canonical

Given the claim for every term of smaller rank, a join of least rank is canonical
(`join-step`{.AgdaFunction}): its joinands that are meets have least rank and a
smaller rank, so they are canonical, and the other three conditions are above.
Meets are dual (`meet-step`{.AgdaFunction}).  The dual of a term of least rank has
least rank (`least-dualᶜ`{.AgdaFunction}), since the dual preserves the rank
(`crank-dualᶜ`{.AgdaFunction}) and takes terms naming one element to terms
naming one element (`dual-cong`{.AgdaFunction}), and the dual of the dual is the
term
(`dualᶜ-involutive`{.AgdaFunction}); so the claim for a meet is the claim for the
dual join, and the dual of a canonical term is canonical.

```agda
-- Each condition at a join of least rank, given the claim for smaller terms.
join-step : (h : CJand X) (t : List (CJand X))
  → (∀ C → crank C < crank (joinᶜ h t) → LeastRank C → IsCanonical C)
  → LeastRank (joinᶜ h t) → IsCanonical (joinᶜ h t)
join-step h t ih lr =
  cjoin (λ e → single-not-least h (subst (λ u → LeastRank (joinᶜ h u)) e lr))
        (tabulate λ { {jgen x}       _   → cjgen
                    ; {jmeet mh mt}  a∈  → cjmeet (ih (meetᶜ mh mt) (s≤s (∈-≤-crankΣJ a∈))
                                                      (joinand-least h t a∈ lr)) })
        (least-antichain h t lr)
        (least-cond4 h t lr)

-- The dual of the dual of a term is the term.
dualᶜ-involutive : (c : CTerm X) → dualᶜ (dualᶜ c) ≡ c
dualᴶ-involutive : (a : CJand X) → dualᴹ (dualᴶ a) ≡ a
dualᴹ-involutive : (a : CMand X) → dualᴶ (dualᴹ a) ≡ a
dualᴶs-involutive : (as : List (CJand X)) → dualᴹs (dualᴶs as) ≡ as
dualᴹs-involutive : (as : List (CMand X)) → dualᴶs (dualᴹs as) ≡ as

dualᶜ-involutive (genᶜ x) = refl
dualᶜ-involutive (joinᶜ h t) = cong₂ joinᶜ (dualᴶ-involutive h) (dualᴶs-involutive t)
dualᶜ-involutive (meetᶜ h t) = cong₂ meetᶜ (dualᴹ-involutive h) (dualᴹs-involutive t)
dualᴶ-involutive (jgen x) = refl
dualᴶ-involutive (jmeet h t) = cong₂ jmeet (dualᴹ-involutive h) (dualᴹs-involutive t)
dualᴹ-involutive (mgen x) = refl
dualᴹ-involutive (mjoin h t) = cong₂ mjoin (dualᴶ-involutive h) (dualᴶs-involutive t)
dualᴶs-involutive [] = refl
dualᴶs-involutive (a ∷ as) = cong₂ _∷_ (dualᴶ-involutive a) (dualᴶs-involutive as)
dualᴹs-involutive [] = refl
dualᴹs-involutive (a ∷ as) = cong₂ _∷_ (dualᴹ-involutive a) (dualᴹs-involutive as)

-- The dual of a term of least rank has least rank.
least-dualᶜ : (C : CTerm X) → LeastRank C → LeastRank (dualᶜ C)
least-dualᶜ C lr D e =
  subst₂ _≤_ (sym (crank-dualᶜ C)) (crank-dualᶜ D)
         (lr (dualᶜ D) (subst₂ _≈ʷ_ (dual-involutive ⌊ C ⌋) (sym (⌊dualᶜ⌋ D))
                                     (dual-cong (subst (_≈ʷ ⌊ D ⌋) (⌊dualᶜ⌋ C) e))))

-- A term whose dual is canonical is canonical.
canonical-dual⁻ : (C : CTerm X) → IsCanonical (dualᶜ C) → IsCanonical C
canonical-dual⁻ C c = subst IsCanonical (dualᶜ-involutive C) (dualᶜ-canonical c)

-- A meet of least rank is canonical, given the claim for smaller terms.
meet-step : (h : CMand X) (t : List (CMand X))
          → (∀ C → crank C < crank (meetᶜ h t) → LeastRank C → IsCanonical C)
          → LeastRank (meetᶜ h t) → IsCanonical (meetᶜ h t)
meet-step h t ih lr =
  canonical-dual⁻ (meetᶜ h t)
    (join-step  (dualᴹ h) (dualᴹs t)
                (λ C lt lrC →  canonical-dual⁻ C
                               (ih (dualᶜ C) ( subst₂ _<_  (sym (crank-dualᶜ C))
                                                           (crank-dualᶜ (meetᶜ h t))
                                                           lt )
                                   (least-dualᶜ C lrC)))
               (least-dualᶜ (meetᶜ h t) lr))
```

The theorem is a well-founded recursion on the rank
(`least⇒canonical`{.AgdaFunction}).

```agda
-- The recursion, on the accessibility of the rank.
least⇒canonical-acc : (C : CTerm X) → Acc _<_ (crank C) → LeastRank C → IsCanonical C
least⇒canonical-acc (genᶜ x) _ _ = cgen
least⇒canonical-acc (joinᶜ h t) (acc rs) lr =
  join-step h t (λ C lt → least⇒canonical-acc C (rs lt)) lr
least⇒canonical-acc (meetᶜ h t) (acc rs) lr =
  meet-step h t (λ C lt → least⇒canonical-acc C (rs lt)) lr

-- Theorem 1.18, necessity of the conditions: a term of least rank is canonical.
least⇒canonical : (C : CTerm X) → LeastRank C → IsCanonical C
least⇒canonical C = least⇒canonical-acc C (<-wellFounded (crank C))
```

#### Uniqueness

Two terms of least rank naming one element are canonical, so they are equal up to
commutativity by `≈ʷ⇒≈ᶜ`{.AgdaFunction} (`leastRank-unique`{.AgdaFunction}).  For
binary terms, a term of least rank abbreviates a canonical term
(`leastᶠ⇒canonical`{.AgdaFunction}), and two of them naming one element
abbreviate terms equal up to commutativity (`leastRankᶠ-unique`{.AgdaFunction}).

```agda
-- Theorem 1.17, uniqueness: terms of least rank naming one element agree up to commutativity.
leastRank-unique : (C D : CTerm X) → LeastRank C → LeastRank D → ⌊ C ⌋ ≈ʷ ⌊ D ⌋ → C ≈ᶜ D
leastRank-unique C D lC lD e = ≈ʷ⇒≈ᶜ C D (least⇒canonical C lC) (least⇒canonical D lD) e

-- A binary term of least rank abbreviates a canonical term.
leastᶠ⇒canonical : (u : LatTerm X) → LeastRankᶠ u → IsCanonical (flat u)
leastᶠ⇒canonical u lr = least⇒canonical (flat u) (leastᶠ⇒least-flat u lr)

-- Binary terms of least rank naming one element agree up to associativity and commutativity.
leastRankᶠ-unique : (u v : LatTerm X) → LeastRankᶠ u → LeastRankᶠ v → u ≈ʷ v → flat u ≈ᶜ flat v
leastRankᶠ-unique u v lu lv e =
  leastRank-unique (flat u) (flat v) (leastᶠ⇒least-flat u lu) (leastᶠ⇒least-flat v lv)
               (≈ʷ-trans (flat-sound u) (≈ʷ-trans e (≈ʷ-sym (flat-sound v))))
```

#### Theorems 1.17 and 1.18

Fix a decision procedure for equality of generators, as the canonicalization
algorithm does.  A canonical term has least rank, by
`crank-minimal`{.AgdaFunction} read through `leastRank⇔rankᶠ`{.AgdaFunction}
(`canonical⇒least`{.AgdaFunction}), so the four conditions characterize the
terms of least rank: this is Theorem 1.18 (`canonical⇔least`{.AgdaFunction}),
its condition 2 being the recursion of `IsCanonical`{.AgdaDatatype}.  Read on
binary terms, a binary term has least rank exactly when the term it abbreviates
is canonical (`canonical⇔leastᶠ`{.AgdaFunction}), and the embedding of a
canonical term is one, since it abbreviates the term
(`canonical⇒leastᶠ`{.AgdaFunction}).  And Theorem 1.17 in one piece
(`least-rank-form`{.AgdaFunction}): the element of any term `t` is named by a
term of least rank, the canonical form `canonical t`{.AgdaFunction}, and every
term of least rank naming it is equal to that one up to commutativity.

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- A canonical term has least rank.
  canonical⇒least : (C : CTerm X) → IsCanonical C → LeastRank C
  canonical⇒least C cC = rankᶠ⇒least C (crank-minimal _≟_ C cC)

  -- Theorem 1.18: a term is canonical exactly when it has least rank.
  canonical⇔least : (C : CTerm X) → IsCanonical C ⇔ LeastRank C
  canonical⇔least C = mk⇔ (canonical⇒least C) (least⇒canonical C)

  -- A binary term has least rank exactly when the term it abbreviates is canonical.
  canonical⇔leastᶠ : (u : LatTerm X) → IsCanonical (flat u) ⇔ LeastRankᶠ u
  canonical⇔leastᶠ u =
    mk⇔ (λ c → least-flat⇒leastᶠ u (canonical⇒least (flat u) c)) (leastᶠ⇒canonical u)

  -- The embedding of a canonical term is a binary term of least rank.
  canonical⇒leastᶠ : (C : CTerm X) → IsCanonical C → LeastRankᶠ ⌊ C ⌋
  canonical⇒leastᶠ C cC =
    least-flat⇒leastᶠ ⌊ C ⌋ (subst LeastRank (sym (flat-⌊⌋ cC)) (canonical⇒least C cC))

  -- Theorem 1.17: every element has a term of least rank, unique up to commutativity.
  least-rank-form : (t : LatTerm X)
                  → Σ[ C ∈ CTerm X ] ⌊ C ⌋ ≈ʷ t × LeastRank C
                                   × (∀ D → ⌊ D ⌋ ≈ʷ t → LeastRank D → D ≈ᶜ C)
  least-rank-form t =
    canonical t , canonical-sound t , canonical⇒least (canonical t) (canonical-isCanonical t)
    , λ D e lD → ≈ʷ⇒≈ᶜ D (canonical t) (least⇒canonical D lD) (canonical-isCanonical t)
                        (≈ʷ-trans e (≈ʷ-sym (canonical-sound t)))
```

#### The statements of Theorems 1.17 and 1.18

Each of the two theorems is one definition whose type is the statement, with
its proof beside it, a type in `Setω` since it quantifies over the level of
the generators; [Lattices.Free.FJN][] lists them with the rest of Chapter I.
Both read the book's terms as the `n`-ary terms `CTerm X`{.AgdaDatatype}, with
the book's rank `crank`{.AgdaFunction}, and "unique up to commutativity" as
`_≈ᶜ_`{.AgdaDatatype}, as the opening sections explain: a term with a join
directly under a join never has least rank, so the least rank over these
terms is the least rank over all of the book's terms, and equivalently over
all binary terms by the flattened rank (`leastRank⇔rankᶠ`{.AgdaFunction}).
Both assume decidable equality on the generators, which the computation of
the canonical form uses.

`FJN-1·17`{.AgdaFunction} is Theorem 1.17: the element of every term `t` has a
term of least rank, and every term of least rank naming it is equal to that
one up to commutativity.  `FJN-1·18`{.AgdaFunction} is Theorem 1.18: a term is
in canonical form, that is, has least rank, exactly when it satisfies the four
conditions of the theorem, dually for a meet, a generator always
(`IsCanonical`{.AgdaDatatype} of [Lattices.Free.Canonical.Basic][], whose
constructors are the conditions, applied at every node).

```agda
-- FJN Theorem 1.17: every element of FL(X) has a term of least rank, unique up
-- to commutativity.
FJN-1·17 : Setω
FJN-1·17 =  ∀ {χ} {X : Type χ} → DecidableEquality X → (t : LatTerm X)
            → Σ[ C ∈ CTerm X ] ⌊ C ⌋ ≈ʷ t × LeastRank C
                             × (∀ D → ⌊ D ⌋ ≈ʷ t → LeastRank D → D ≈ᶜ C)

fjn-1·17 : FJN-1·17
fjn-1·17 = least-rank-form

-- FJN Theorem 1.18: a term has least rank exactly when it satisfies the four
-- conditions.
FJN-1·18 : Setω
FJN-1·18 =  ∀ {χ} {X : Type χ} → DecidableEquality X
            → (C : CTerm X) → IsCanonical C ⇔ LeastRank C

fjn-1·18 : FJN-1·18
fjn-1·18 = canonical⇔least
```
