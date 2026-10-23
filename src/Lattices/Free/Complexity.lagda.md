---
layout: default
file: "src/Lattices/Free/Complexity.lagda.md"
title: "Lattices.Free.Complexity module"
date: "2026-10-13"
author: "the agda-lattices development team"
---

### The complexity of an element of a free lattice

This is the [Lattices.Free.Complexity][] module of the [agda-lattices][] library.

[Freese, Ježek, and Nation (1995)][], Section I.2, measure the depth of a term by
its *complexity*: a generator has complexity 0, and a join or meet of `n > 1`
terms has complexity one more than the largest complexity among them.  The
complexity of an *element* of `FL(X)` is the complexity of its canonical form,
the height of the tree drawn from the canonical form, with the joinands and
meetands at each level as the children.  This module proves three facts about
it.

+  **It is well defined** (`complexity-resp`{.AgdaFunction}).  Two canonical
   terms of the same element differ only in the order of children
   (Theorem 1.17, `≈ʷ⇒≈ᶜ`{.AgdaFunction} of
   [Lattices.Free.Canonical.Uniqueness][]), and reordering children does not
   change the height.
+  **A lattice embedding never lowers it** (`complexity-mono`{.AgdaFunction}).
   Let `σ : FL(X) → FL(Y)` be injective and let `w` be a canonical join
   `w₁ ∨ ⋯ ∨ wₙ`, `n > 1`.  The image `σ(w)` is not a generator, because a
   generator in the image of an embedding is the image of a generator
   (Corollary 1.6) and `w` is not one; so `σ(w)` has complexity at least 1.  And
   if `wᵢ` is not a generator, Lemma 9.13
   (`embedding-canonicalJoinand`{.AgdaFunction} of [Lattices.Free.Embedding][])
   makes `σ(wᵢ)` a canonical joinand of `σ(w)`, and a proper one, since
   `σ(wᵢ) = σ(w)` would give `wᵢ = w`; so the complexity of `σ(w)` exceeds that
   of `σ(wᵢ)`, which by induction is at least that of `wᵢ`.  Meets are dual.
+  **Over finitely many generators, only finitely many elements have complexity
   at most `n`** (`bounded-complete`{.AgdaFunction}).  The elements of
   complexity 0 are the generators, and an element of complexity at most
   `n + 1` is a generator or a join or meet of a set of elements of complexity
   at most `n`; so the list `bounded n`{.AgdaFunction} of the generators and
   all joins and meets of nonempty sublists of `bounded (n - 1)` contains every
   such element up to equality.  With the pigeonhole principle
   (`pigeonhole-≈`{.AgdaFunction}), any sequence of elements of bounded
   complexity repeats a value.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Complexity where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; zero ; suc ; toℕ ; combine )
open import Data.Fin.Properties                    using ( pigeonhole ; combine-injective )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; _++_ ; map ; length )
                                                   renaming ( lookup to lookupᴸ )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁺ ; ∈-map⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ
                                                         ; ∈-++⁻ )
open import Data.List.Relation.Binary.Permutation.Propositional
                                                   using ( ↭-sym )
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
                                                   using ( ∈-resp-↭ )
open import Data.List.Relation.Binary.Pointwise    using ( Pointwise ; [] ; _∷_ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ ; lookup )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there ; index )
open import Data.List.Relation.Unary.Any.Properties
                                                   using ( lookup-index ; ++⁺ˡ ; ++⁺ʳ )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _≤_ ; _<_ ; _⊔_ ; _^_
                                                         ; z≤n ; s≤s )
open import Data.Nat.Properties                    using ( ≤-refl ; ≤-trans ; ≤-antisym ; ⊔-lub
                                                         ; m≤m⊔n ; m≤n⊔m ; n<1+n ; n≢0⇒n>0 )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( _⊎_ ; inj₁ ; inj₂ ; map₂ )
open import Function                               using ( _∘_ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; subst )
open import Relation.Nullary                       using ( ¬_ )

import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.Any as Any

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Lattices.Free.Canonical.Algorithm      using ( module Canonicalization )
open import Lattices.Free.Canonical.Basic
  using  ( CTerm ; genᶜ ; joinᶜ ; meetᶜ ; CJand ; jgen ; jmeet ; CMand ; mgen ; mjoin ; ⌊_⌋
         ; ⌊_⌋ᴶ ; ⌊_⌋ᴹ ; ⋀ᴹ ; ⋁⁺ ; ⋀⁺ ; ⋁ᴶ-upper ; ⋀ᴹ-lower ; ⋁ᴶ≡⋁⁺ ; ⋀ᴹ≡⋀⁺ ; ≈ʷ-refl ; ≈ʷ-sym
         ; ≈ʷ-trans ; ∨̇-cong ; ∧̇-cong ; ∨̇-comm ; ∧̇-comm ; ∨̇-assoc ; ∧̇-assoc ; ∨̇-idem
         ; ∧̇-idem ; IsCanonical ; cgen ; cjoin ; cmeet ; IsCanonicalJ ; cjgen ; cjmeet
         ; IsCanonicalM ; cmgen ; cmjoin
         ; asListJ ; asListM ; joinandsOf ; meetandsOf )
open import Lattices.Free.Canonical.Joinands       using ( canonicalJoinands ; canonicalMeetands )
open import Lattices.Free.Canonical.Uniqueness
  using  ( _≈ᶜ_ ; gen≈ ; join≈ ; meet≈ ; _≈ᶜᴶ_ ; jgen≈ ; jmeet≈ ; _≈ᶜᴹ_ ; mgen≈ ; mjoin≈ ; PW-∈
         ; PW-∈ʳ ; ≈ʷ⇒≈ᶜ ; gen≉join ; gen≉meet ; module Antichains )
open import Lattices.Free.Embedding
  using  ( embedding-canonicalJoinand ; embedding-canonicalMeetand )
open import Lattices.Free.Generation               using ( generator-in-image )
open import Lattices.Free.Substitution             using ( Sub ; _[_] ; subst-hom
                                                         ; injective→reflects )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; _≈ʷ_ ; ≤ʷ-trans )
open import Setoid.Functions                       using ( IsInjective )

private variable
  χ υ : Level
  X : Type χ
  Y : Type υ
```
-->

#### The depth of a canonical term

`depth`{.AgdaFunction} is the complexity of a canonical term: 0 for a generator,
and one more than the largest depth among the children for a join or a meet.
The largest depth among a nonempty list of children (`depthΣJ`{.AgdaFunction},
`depthΣM`{.AgdaFunction}) is defined, like the embedding `⌊_⌋`{.AgdaFunction}
of [Lattices.Free.Canonical.Basic][], by structural recursion on the tail, in
the same mutual block, so that the termination checker sees every call.

```agda
-- The complexity of a canonical term, and of its children.
depth    : CTerm X → ℕ
depthJ   : CJand X → ℕ
depthM   : CMand X → ℕ
depthΣJ  : CJand X → List (CJand X) → ℕ
depthΣM  : CMand X → List (CMand X) → ℕ

depth (genᶜ x)      = 0
depth (joinᶜ h t)   = suc (depthΣJ h t)
depth (meetᶜ h t)   = suc (depthΣM h t)
depthJ (jgen x)     = 0
depthJ (jmeet h t)  = suc (depthΣM h t)
depthM (mgen x)     = 0
depthM (mjoin h t)  = suc (depthΣJ h t)
depthΣJ h []        = depthJ h
depthΣJ h (a ∷ as)  = depthJ h ⊔ depthΣJ a as
depthΣM h []        = depthM h
depthΣM h (a ∷ as)  = depthM h ⊔ depthΣM a as
```

The largest depth among the children bounds each of them
(`depthΣJ-upper`{.AgdaFunction}), lies below every common bound
(`depthΣJ-least`{.AgdaFunction}), and below every common strict bound
(`depthΣJ-<`{.AgdaFunction}); dually for meetands.

```agda
-- Each child's depth is at most the largest.
depthΣJ-upper : {h a : CJand X} {t : List (CJand X)} → a ∈ h ∷ t → depthJ a ≤ depthΣJ h t
depthΣJ-upper {t = []}     (here refl)  = ≤-refl
depthΣJ-upper {t = _ ∷ _}  (here refl)  = m≤m⊔n _ _
depthΣJ-upper {t = _ ∷ _}  (there a∈)   = ≤-trans (depthΣJ-upper a∈) (m≤n⊔m _ _)

depthΣM-upper : {h a : CMand X} {t : List (CMand X)} → a ∈ h ∷ t → depthM a ≤ depthΣM h t
depthΣM-upper {t = []}     (here refl)  = ≤-refl
depthΣM-upper {t = _ ∷ _}  (here refl)  = m≤m⊔n _ _
depthΣM-upper {t = _ ∷ _}  (there a∈)   = ≤-trans (depthΣM-upper a∈) (m≤n⊔m _ _)

-- The largest depth lies below every common bound of the children's depths.
depthΣJ-least : {h : CJand X} {t : List (CJand X)} {m : ℕ}
              → (∀ {a} → a ∈ h ∷ t → depthJ a ≤ m) → depthΣJ h t ≤ m
depthΣJ-least {t = []}     f = f (here refl)
depthΣJ-least {t = _ ∷ _}  f = ⊔-lub (f (here refl)) (depthΣJ-least λ a∈ → f (there a∈))

depthΣM-least : {h : CMand X} {t : List (CMand X)} {m : ℕ}
              → (∀ {a} → a ∈ h ∷ t → depthM a ≤ m) → depthΣM h t ≤ m
depthΣM-least {t = []}     f = f (here refl)
depthΣM-least {t = _ ∷ _}  f = ⊔-lub (f (here refl)) (depthΣM-least λ a∈ → f (there a∈))

-- The largest depth lies below every common strict bound.
depthΣJ-< : {h : CJand X} {t : List (CJand X)} {m : ℕ}
          → (∀ {a} → a ∈ h ∷ t → depthJ a < m) → depthΣJ h t < m
depthΣJ-< {t = []}     f = f (here refl)
depthΣJ-< {t = _ ∷ _}  f = ⊔-lub (f (here refl)) (depthΣJ-< λ a∈ → f (there a∈))

depthΣM-< : {h : CMand X} {t : List (CMand X)} {m : ℕ}
          → (∀ {a} → a ∈ h ∷ t → depthM a < m) → depthΣM h t < m
depthΣM-< {t = []}     f = f (here refl)
depthΣM-< {t = _ ∷ _}  f = ⊔-lub (f (here refl)) (depthΣM-< λ a∈ → f (there a∈))
```

A child is itself a canonical term (`toCᴶ`{.AgdaFunction},
`toCᴹ`{.AgdaFunction}): a generator, or the meet (or join) of its own children.
The conversion keeps the depth, the embedded lattice term, and canonicity.

```agda
-- A joinand as a canonical term.
toCᴶ : CJand X → CTerm X
toCᴶ (jgen x)     = genᶜ x
toCᴶ (jmeet h t)  = meetᶜ h t

-- A meetand as a canonical term.
toCᴹ : CMand X → CTerm X
toCᴹ (mgen x)     = genᶜ x
toCᴹ (mjoin h t)  = joinᶜ h t

-- The conversion keeps the depth.
depth-toCᴶ : (a : CJand X) → depth (toCᴶ a) ≡ depthJ a
depth-toCᴶ (jgen x)     = refl
depth-toCᴶ (jmeet h t)  = refl

depth-toCᴹ : (a : CMand X) → depth (toCᴹ a) ≡ depthM a
depth-toCᴹ (mgen x)     = refl
depth-toCᴹ (mjoin h t)  = refl

-- The conversion keeps the embedded lattice term.
⌊toCᴶ⌋ : (a : CJand X) → ⌊ toCᴶ a ⌋ ≡ ⌊ a ⌋ᴶ
⌊toCᴶ⌋ (jgen x)     = refl
⌊toCᴶ⌋ (jmeet h t)  = refl

⌊toCᴹ⌋ : (a : CMand X) → ⌊ toCᴹ a ⌋ ≡ ⌊ a ⌋ᴹ
⌊toCᴹ⌋ (mgen x)     = refl
⌊toCᴹ⌋ (mjoin h t)  = refl

-- The conversion keeps canonicity.
toCᴶ-canonical : {a : CJand X} → IsCanonicalJ a → IsCanonical (toCᴶ a)
toCᴶ-canonical cjgen        = cgen
toCᴶ-canonical (cjmeet ic)  = ic

toCᴹ-canonical : {a : CMand X} → IsCanonicalM a → IsCanonical (toCᴹ a)
toCᴹ-canonical cmgen        = cgen
toCᴹ-canonical (cmjoin ic)  = ic
```

A canonical term of depth 0 is a generator (`depth-zero`{.AgdaFunction}).

```agda
-- Only a generator has depth 0.
depth-zero : (C : CTerm X) → depth C ≡ 0 → Σ[ x ∈ X ] C ≡ genᶜ x
depth-zero (genᶜ x)     _ = x , refl
depth-zero (joinᶜ _ _)  ()
depth-zero (meetᶜ _ _)  ()
```

#### Reordering children keeps the depth

Two canonical terms related by `_≈ᶜ_`{.AgdaDatatype} have the same depth
(`depth-≈ᶜ`{.AgdaFunction}).  The proof is by induction on the relation.  For two
joins, the children of the first are, after a permutation, pointwise related to
those of the second; the induction hypothesis turns the pointwise relation into
pointwise equality of depths (`depth-≈ᶜᴶs`{.AgdaFunction}), and then each child
of either join has a partner of equal depth in the other, so the largest depths
agree.

```agda
-- Related canonical terms, children, and lists of children have equal depths.
depth-≈ᶜ    : {s t : CTerm X} → s ≈ᶜ t → depth s ≡ depth t
depth-≈ᶜᴶ   : {a b : CJand X} → a ≈ᶜᴶ b → depthJ a ≡ depthJ b
depth-≈ᶜᴹ   : {a b : CMand X} → a ≈ᶜᴹ b → depthM a ≡ depthM b
depth-≈ᶜᴶs  : {as bs : List (CJand X)} → Pointwise _≈ᶜᴶ_ as bs
            → Pointwise (λ a b → depthJ a ≡ depthJ b) as bs
depth-≈ᶜᴹs  : {as bs : List (CMand X)} → Pointwise _≈ᶜᴹ_ as bs
            → Pointwise (λ a b → depthM a ≡ depthM b) as bs

depth-≈ᶜ (gen≈ refl)  = refl
depth-≈ᶜ {X = X} (join≈ {jh = h} {jt = t} {js = js} {jh' = h'} {jt' = t'} p q) =
  cong suc (≤-antisym (depthΣJ-least λ a∈ → ≤-from-right (find (PW-∈ pw (∈-resp-↭ p a∈))))
                      (depthΣJ-least λ b∈ → ≤-from-left (find (PW-∈ʳ pw b∈))))
  where
  -- The permuted children of the first join have the depths of the second's.
  pw : Pointwise (λ a b → depthJ a ≡ depthJ b) js (h' ∷ t')
  pw = depth-≈ᶜᴶs q

  -- A child of the first join, with its partner in the second.
  ≤-from-right : {a : CJand X} → Σ[ b ∈ CJand X ] b ∈ h' ∷ t' × depthJ a ≡ depthJ b
               → depthJ a ≤ depthΣJ h' t'
  ≤-from-right (_ , b∈ , e) = subst (_≤ depthΣJ h' t') (sym e) (depthΣJ-upper b∈)

  -- A child of the second join, with its partner in the first.
  ≤-from-left : {b : CJand X} → Σ[ a ∈ CJand X ] a ∈ js × depthJ a ≡ depthJ b
              → depthJ b ≤ depthΣJ h t
  ≤-from-left (_ , a∈ , e) = subst (_≤ depthΣJ h t) e (depthΣJ-upper (∈-resp-↭ (↭-sym p) a∈))
depth-≈ᶜ {X = X} (meet≈ {mh = h} {mt = t} {ms = ms} {mh' = h'} {mt' = t'} p q) =
  cong suc (≤-antisym (depthΣM-least λ a∈ → ≤-from-right (find (PW-∈ pw (∈-resp-↭ p a∈))))
                      (depthΣM-least λ b∈ → ≤-from-left (find (PW-∈ʳ pw b∈))))
  where
  -- The permuted children of the first meet have the depths of the second's.
  pw : Pointwise (λ a b → depthM a ≡ depthM b) ms (h' ∷ t')
  pw = depth-≈ᶜᴹs q

  -- A child of the first meet, with its partner in the second.
  ≤-from-right : {a : CMand X} → Σ[ b ∈ CMand X ] b ∈ h' ∷ t' × depthM a ≡ depthM b
               → depthM a ≤ depthΣM h' t'
  ≤-from-right (_ , b∈ , e) = subst (_≤ depthΣM h' t') (sym e) (depthΣM-upper b∈)

  -- A child of the second meet, with its partner in the first.
  ≤-from-left : {b : CMand X} → Σ[ a ∈ CMand X ] a ∈ ms × depthM a ≡ depthM b
              → depthM b ≤ depthΣM h t
  ≤-from-left (_ , a∈ , e) = subst (_≤ depthΣM h t) e (depthΣM-upper (∈-resp-↭ (↭-sym p) a∈))
depth-≈ᶜᴶ (jgen≈ refl)  = refl
depth-≈ᶜᴶ (jmeet≈ e)    = depth-≈ᶜ e
depth-≈ᶜᴹ (mgen≈ refl)  = refl
depth-≈ᶜᴹ (mjoin≈ e)    = depth-≈ᶜ e
depth-≈ᶜᴶs []        = []
depth-≈ᶜᴶs (r ∷ rs)  = depth-≈ᶜᴶ r ∷ depth-≈ᶜᴶs rs
depth-≈ᶜᴹs []        = []
depth-≈ᶜᴹs (r ∷ rs)  = depth-≈ᶜᴹ r ∷ depth-≈ᶜᴹs rs
```

#### The complexity of an element

With decidable equality of generators the canonical form of a term is computed
(`canonical`{.AgdaFunction} of [Lattices.Free.Canonical.Algorithm][]), and the
complexity of a term is the depth of its canonical form
(`complexity`{.AgdaFunction}).  Equal elements have equal complexity
(`complexity-resp`{.AgdaFunction}), by Theorem 1.17 and `depth-≈ᶜ`{.AgdaFunction}.
So the complexity of a canonical term is its depth
(`complexity-canonical`{.AgdaFunction}), whatever canonical term the algorithm
returns for it, and the complexity of a child of a canonical term is the child's
depth (`complexityᴶ`{.AgdaFunction}, `complexityᴹ`{.AgdaFunction}).  An element of
complexity 0 is a generator (`complexity-zero`{.AgdaFunction}).

```agda
module _ {X : Type χ} (_≟_ : DecidableEquality X) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )

  -- The complexity of an element: the depth of its canonical form.
  complexity : LatTerm X → ℕ
  complexity w = depth (canonical w)

  -- A canonical term has the complexity of the element it represents.
  depth-canonical : (C : CTerm X) → IsCanonical C → {w : LatTerm X} → ⌊ C ⌋ ≈ʷ w
                  → depth C ≡ complexity w
  depth-canonical C ic {w} e =
    depth-≈ᶜ (≈ʷ⇒≈ᶜ C (canonical w) ic (canonical-isCanonical w)
                    (≈ʷ-trans e (≈ʷ-sym (canonical-sound w))))

  -- Equal elements have equal complexity.
  complexity-resp : {w w' : LatTerm X} → w ≈ʷ w' → complexity w ≡ complexity w'
  complexity-resp {w} e = depth-canonical (canonical w) (canonical-isCanonical w)
                                          (≈ʷ-trans (canonical-sound w) e)

  -- The complexity of a canonical term is its depth.
  complexity-canonical : (C : CTerm X) → IsCanonical C → complexity ⌊ C ⌋ ≡ depth C
  complexity-canonical C ic = sym (depth-canonical C ic ≈ʷ-refl)

  -- The complexity of a child of a canonical term is the child's depth.
  complexityᴶ : {a : CJand X} → IsCanonicalJ a → complexity ⌊ a ⌋ᴶ ≡ depthJ a
  complexityᴶ {a} ic = trans (cong complexity (sym (⌊toCᴶ⌋ a)))
                             (trans (complexity-canonical (toCᴶ a) (toCᴶ-canonical ic))
                                    (depth-toCᴶ a))

  complexityᴹ : {a : CMand X} → IsCanonicalM a → complexity ⌊ a ⌋ᴹ ≡ depthM a
  complexityᴹ {a} ic = trans (cong complexity (sym (⌊toCᴹ⌋ a)))
                             (trans (complexity-canonical (toCᴹ a) (toCᴹ-canonical ic))
                                    (depth-toCᴹ a))

  -- An element of complexity 0 is a generator.
  complexity-zero : (w : LatTerm X) → complexity w ≡ 0 → Σ[ x ∈ X ] w ≈ʷ ℊ x
  complexity-zero w z =
    let (x , e) = depth-zero (canonical w) z
    in x , ≈ʷ-sym (subst (λ C → ⌊ C ⌋ ≈ʷ w) e (canonical-sound w))
```

A canonical joinand `c` of `v` that is strictly below `v` has smaller complexity:
`suc (complexity c) ≤ complexity v` (`joinand-complexity`{.AgdaFunction}).  If
the canonical form of `v` is a generator or a meet, its only joinand is `v`
itself, which is not strictly below `v`; if it is a join, `c` is one of its
children, whose depth is at most the largest.  Dually for a canonical meetand
strictly above `v` (`meetand-complexity`{.AgdaFunction}).  Both are stated first
for any canonical term `C` that represents `v`, and then read for the computed
canonical form.

```agda
  -- A joinand of a canonical term, strictly below it, is shallower.
  joinandᶜ-complexity : (C : CTerm X) → IsCanonical C → {v : LatTerm X} → ⌊ C ⌋ ≈ʷ v
                      → {c : LatTerm X} → c ∈ map ⌊_⌋ᴶ (asListJ (joinandsOf C)) → ¬ (v ≤ʷ c)
                      → suc (complexity c) ≤ depth C
  joinandᶜ-complexity (genᶜ _)     _                  e (here refl)  v≰c = ⊥-elim (v≰c (proj₂ e))
  joinandᶜ-complexity (meetᶜ _ _)  _                  e (here refl)  v≰c = ⊥-elim (v≰c (proj₂ e))
  joinandᶜ-complexity (joinᶜ h t)  (cjoin _ cs _ _)   e c∈           _   =
    let (b , b∈ , c≡) = ∈-map⁻ ⌊_⌋ᴶ c∈
    in s≤s (subst (_≤ depthΣJ h t) (sym (trans (cong complexity c≡) (complexityᴶ (lookup cs b∈))))
                  (depthΣJ-upper b∈))

  -- A meetand of a canonical term, strictly above it, is shallower.
  meetandᶜ-complexity : (C : CTerm X) → IsCanonical C → {v : LatTerm X} → ⌊ C ⌋ ≈ʷ v
                      → {c : LatTerm X} → c ∈ map ⌊_⌋ᴹ (asListM (meetandsOf C)) → ¬ (c ≤ʷ v)
                      → suc (complexity c) ≤ depth C
  meetandᶜ-complexity (genᶜ _)     _                  e (here refl)  c≰v = ⊥-elim (c≰v (proj₁ e))
  meetandᶜ-complexity (joinᶜ _ _)  _                  e (here refl)  c≰v = ⊥-elim (c≰v (proj₁ e))
  meetandᶜ-complexity (meetᶜ h t)  (cmeet _ cs _ _)   e c∈           _   =
    let (b , b∈ , c≡) = ∈-map⁻ ⌊_⌋ᴹ c∈
    in s≤s (subst (_≤ depthΣM h t) (sym (trans (cong complexity c≡) (complexityᴹ (lookup cs b∈))))
                  (depthΣM-upper b∈))

  -- A canonical joinand strictly below an element is shallower.
  joinand-complexity : (v : LatTerm X) {c : LatTerm X} → c ∈ canonicalJoinands _≟_ v → ¬ (v ≤ʷ c)
                     → suc (complexity c) ≤ complexity v
  joinand-complexity v =
    joinandᶜ-complexity (canonical v) (canonical-isCanonical v) (canonical-sound v)

  -- A canonical meetand strictly above an element is shallower.
  meetand-complexity : (v : LatTerm X) {c : LatTerm X} → c ∈ canonicalMeetands _≟_ v → ¬ (c ≤ʷ v)
                     → suc (complexity c) ≤ complexity v
  meetand-complexity v =
    meetandᶜ-complexity (canonical v) (canonical-isCanonical v) (canonical-sound v)
```

#### A lattice embedding never lowers the complexity

Fix a substitution `σ` from `X` to `Y` whose induced homomorphism is injective.
An element whose image is a generator is a generator (`image-gen`{.AgdaFunction}):
the generator lies in the image, so by Corollary 1.6 it is the image `σ x` of a
generator (`generator-in-image`{.AgdaFunction}), and injectivity gives `w = x`.
So the image of an element that is not a generator has positive complexity
(`image-positive`{.AgdaFunction}).

```agda
module _ {X : Type χ} {Y : Type υ} (_≟ˣ_ : DecidableEquality X) (_≟ʸ_ : DecidableEquality Y)
         (σ : Sub X Y) (inj : IsInjective (proj₁ (subst-hom σ))) where
  open Canonicalization _≟ˣ_ using ( canonical ; canonical-sound ; canonical-isCanonical )
  open Antichains {A = CJand X} (λ u v → ⌊ u ⌋ᴶ ≤ʷ ⌊ v ⌋ᴶ) ≤ʷ-trans
    using () renaming ( antichain-no-max to no-maxᴶ )
  open Antichains {A = CMand X} (λ u v → ⌊ u ⌋ᴹ ≤ʷ ⌊ v ⌋ᴹ) ≤ʷ-trans
    using () renaming ( antichain-no-min to no-minᴹ )

  private
    -- The complexities on the two sides.
    κˣ : LatTerm X → ℕ
    κˣ = complexity _≟ˣ_

    κʸ : LatTerm Y → ℕ
    κʸ = complexity _≟ʸ_

    -- The embedding reflects the order.
    reflect : {s t : LatTerm X} → s [ σ ] ≤ʷ t [ σ ] → s ≤ʷ t
    reflect {s} {t} = injective→reflects σ {s = s} {t = t} inj

    -- A meet child is not a generator; nor is a join child.
    meet-not-gen : {mh : CMand X} {mt : List (CMand X)} → IsCanonicalJ (jmeet mh mt)
                 → ∀ x → ¬ (⌊ jmeet mh mt ⌋ᴶ ≈ʷ ℊ x)
    meet-not-gen (cjmeet ic) x e = gen≉meet ic (≈ʷ-sym e)

    join-not-gen : {jh : CJand X} {jt : List (CJand X)} → IsCanonicalM (mjoin jh jt)
                 → ∀ x → ¬ (⌊ mjoin jh jt ⌋ᴹ ≈ʷ ℊ x)
    join-not-gen (cmjoin ic) x e = gen≉join ic (≈ʷ-sym e)

  -- An element whose image is a generator is a generator.
  image-gen : (w : LatTerm X) {y : Y} → w [ σ ] ≈ʷ ℊ y → Σ[ x ∈ X ] w ≈ʷ ℊ x
  image-gen w e = let (x , y≈) = generator-in-image σ w (≈ʷ-sym e)
                  in x , inj {w} {ℊ x} (≈ʷ-trans e y≈)

  -- The image of an element that is not a generator has positive complexity.
  image-positive : (w : LatTerm X) → (∀ x → ¬ (w ≈ʷ ℊ x)) → 0 < κʸ (w [ σ ])
  image-positive w not-gen = n≢0⇒n>0 λ z →
    let (_ , e) = complexity-zero _≟ʸ_ (w [ σ ]) z
        (x , e') = image-gen w e
    in not-gen x e'
```

The theorem (`complexity-mono`{.AgdaFunction}) is proved for a canonical term
`C` of `w` whose children are the canonical joinands and meetands of `w`
(`complexity-monoᶜ`{.AgdaFunction}), with a bound `n` on the depth that
decreases at each recursive call (`complexity-mono≤`{.AgdaFunction}), and then
read for the computed canonical form.  For a join `C`, each child `a` has depth
below the complexity of `σ(w)`.  A generator child has depth 0, and `σ(w)` has
positive complexity since `w`, a canonical join, is not a generator.  A meet child `c = ⌊ a ⌋ᴶ` has, by
Lemma 9.13, an image equal to a canonical joinand `c'` of `σ(w)`.  That joinand
is strictly below `σ(w)`: otherwise `σ(w) ≤ σ(c)`, so `w ≤ c` by injectivity, and
`c` would be the largest member of an antichain of two or more.  So the
complexity of `σ(w)` exceeds that of `c'`, which equals that of `σ(c)`, which by
the induction hypothesis is at least that of `c`, the depth of `a`.  A meet `C`
is dual, with `embedding-canonicalMeetand`{.AgdaFunction}.

```agda
  -- The theorem with a bound on the complexity, and for a canonical term.
  complexity-mono≤  : (n : ℕ) (w : LatTerm X) → κˣ w ≤ n → κˣ w ≤ κʸ (w [ σ ])
  complexity-monoᶜ  : (n : ℕ) (w : LatTerm X) (C : CTerm X) → IsCanonical C → ⌊ C ⌋ ≈ʷ w
                    → (∀ {a} → a ∈ asListJ (joinandsOf C) → ⌊ a ⌋ᴶ ∈ canonicalJoinands _≟ˣ_ w)
                    → (∀ {a} → a ∈ asListM (meetandsOf C) → ⌊ a ⌋ᴹ ∈ canonicalMeetands _≟ˣ_ w)
                    → depth C ≤ n → depth C ≤ κʸ (w [ σ ])

  complexity-mono≤ n w b =
    complexity-monoᶜ n w (canonical w) (canonical-isCanonical w) (canonical-sound w)
                     (∈-map⁺ ⌊_⌋ᴶ) (∈-map⁺ ⌊_⌋ᴹ) b

  complexity-monoᶜ n        w (genᶜ _)     _                      _ _  _  _        = z≤n
  complexity-monoᶜ zero     w (joinᶜ _ _)  _                      _ _  _  ()
  complexity-monoᶜ zero     w (meetᶜ _ _)  _                      _ _  _  ()
  complexity-monoᶜ (suc n)  w (joinᶜ h t)  ic@(cjoin ne cs ac _)  e J∈ _  (s≤s b)  =
    depthΣJ-< child<
    where
    -- w is a canonical join, not a generator.
    not-gen : ∀ x → ¬ (w ≈ʷ ℊ x)
    not-gen x e' = gen≉join ic (≈ʷ-sym (≈ʷ-trans e e'))

    -- A meet child, with the canonical joinand of σ(w) its image equals.
    meet-child : {mh : CMand X} {mt : List (CMand X)} → jmeet mh mt ∈ h ∷ t
               → Σ[ c' ∈ LatTerm Y ] c' ∈ canonicalJoinands _≟ʸ_ (w [ σ ])
                                     × ⋀ᴹ mh mt [ σ ] ≈ʷ c'
               → depthJ (jmeet mh mt) < κʸ (w [ σ ])
    meet-child {mh} {mt} a∈ (c' , c'∈ , c≈c') =
      ≤-trans (s≤s (≤-trans (subst (_≤ κˣ c) (complexityᴶ _≟ˣ_ (lookup cs a∈)) ≤-refl)
                   (≤-trans (complexity-mono≤ n c c≤n)
                            (subst (κʸ (c [ σ ]) ≤_) (complexity-resp _≟ʸ_ c≈c') ≤-refl))))
              (joinand-complexity _≟ʸ_ (w [ σ ]) c'∈ w≰c')
      where
      c : LatTerm X
      c = ⋀ᴹ mh mt

      c≤n : κˣ c ≤ n
      c≤n = subst (_≤ n) (sym (complexityᴶ _≟ˣ_ (lookup cs a∈))) (≤-trans (depthΣJ-upper a∈) b)

      w≰c' : ¬ (w [ σ ] ≤ʷ c')
      w≰c' p = no-maxᴶ ac ne a∈ λ v∈ →
        ≤ʷ-trans (⋁ᴶ-upper v∈) (≤ʷ-trans (proj₁ e) (reflect (≤ʷ-trans p (proj₂ c≈c'))))

    -- Every child is shallower than σ(w).
    child< : ∀ {a} → a ∈ h ∷ t → depthJ a < κʸ (w [ σ ])
    child< {jgen _}       _   = image-positive w not-gen
    child< {jmeet mh mt}  a∈  =
      meet-child a∈ (find (embedding-canonicalJoinand _≟ˣ_ _≟ʸ_ σ inj w (J∈ a∈)
                                                      (meet-not-gen (lookup cs a∈))))
  complexity-monoᶜ (suc n)  w (meetᶜ h t)  ic@(cmeet ne cs ac _)  e _  M∈ (s≤s b)  =
    depthΣM-< child<
    where
    -- w is a canonical meet, not a generator.
    not-gen : ∀ x → ¬ (w ≈ʷ ℊ x)
    not-gen x e' = gen≉meet ic (≈ʷ-sym (≈ʷ-trans e e'))

    -- A join child, with the canonical meetand of σ(w) its image equals.
    join-child : {jh : CJand X} {jt : List (CJand X)} → mjoin jh jt ∈ h ∷ t
               → Σ[ c' ∈ LatTerm Y ] c' ∈ canonicalMeetands _≟ʸ_ (w [ σ ])
                                     × ⌊ mjoin jh jt ⌋ᴹ [ σ ] ≈ʷ c'
               → depthM (mjoin jh jt) < κʸ (w [ σ ])
    join-child {jh} {jt} a∈ (c' , c'∈ , c≈c') =
      ≤-trans (s≤s (≤-trans (subst (_≤ κˣ c) (complexityᴹ _≟ˣ_ (lookup cs a∈)) ≤-refl)
                   (≤-trans (complexity-mono≤ n c c≤n)
                            (subst (κʸ (c [ σ ]) ≤_) (complexity-resp _≟ʸ_ c≈c') ≤-refl))))
              (meetand-complexity _≟ʸ_ (w [ σ ]) c'∈ c'≰w)
      where
      c : LatTerm X
      c = ⌊ mjoin jh jt ⌋ᴹ

      c≤n : κˣ c ≤ n
      c≤n = subst (_≤ n) (sym (complexityᴹ _≟ˣ_ (lookup cs a∈))) (≤-trans (depthΣM-upper a∈) b)

      c'≰w : ¬ (c' ≤ʷ w [ σ ])
      c'≰w p = no-minᴹ ac ne a∈ λ v∈ →
        ≤ʷ-trans (reflect (≤ʷ-trans (proj₁ c≈c') p)) (≤ʷ-trans (proj₂ e) (⋀ᴹ-lower v∈))

    -- Every child is shallower than σ(w).
    child< : ∀ {a} → a ∈ h ∷ t → depthM a < κʸ (w [ σ ])
    child< {mgen _}       _   = image-positive w not-gen
    child< {mjoin jh jt}  a∈  =
      join-child a∈ (find (embedding-canonicalMeetand _≟ˣ_ _≟ʸ_ σ inj w (M∈ a∈)
                                                      (join-not-gen (lookup cs a∈))))

  -- A lattice embedding never lowers the complexity.
  complexity-mono : (w : LatTerm X) → κˣ w ≤ κʸ (w [ σ ])
  complexity-mono w = complexity-mono≤ (κˣ w) w ≤-refl
```

#### Joins and meets of sublists

Fix a binary operation `_·_` on lattice terms that is a congruence, idempotent,
commutative, and associative up to `_≈ʷ_`{.AgdaFunction} (the module
`Folds`{.AgdaModule}; formal join and formal meet are the two instances).
`combos L`{.AgdaFunction} lists the products of the nonempty sublists of `L`:
`combos (l ∷ L)` is `l`, then the products of the sublists of `L`, then `l`
times each of those.  Every member of `L` is in the list
(`∈-combos`{.AgdaFunction}); the product of a member of `L` and a member of the
list equals a member of the list (`combos-·`{.AgdaFunction}), by cases on where
each sits and the laws of `_·_`; so the product of any nonempty list of terms,
each equal to a member of `L`, equals a member of `combos L`
(`fold-cover`{.AgdaFunction}).

```agda
module Folds {X : Type χ} (_·_ : LatTerm X → LatTerm X → LatTerm X)
             (·-cong  : ∀ {s t u v} → s ≈ʷ u → t ≈ʷ v → s · t ≈ʷ u · v)
             (·-idem  : ∀ {t} → t · t ≈ʷ t)
             (·-comm  : ∀ {s t} → s · t ≈ʷ t · s)
             (·-assoc : ∀ {s t u} → (s · t) · u ≈ʷ s · (t · u)) where

  -- The products of the nonempty sublists of a list.
  combos : List (LatTerm X) → List (LatTerm X)
  combos []       = []
  combos (l ∷ L)  = l ∷ (combos L ++ map (l ·_) (combos L))

  -- The product of a nonempty list.
  fold : LatTerm X → List (LatTerm X) → LatTerm X
  fold u []        = u
  fold u (w ∷ ws)  = u · fold w ws

  -- Two consequences of the laws.
  ·-absorb : ∀ {k j} → k · (k · j) ≈ʷ k · j
  ·-absorb = ≈ʷ-trans (≈ʷ-sym ·-assoc) (·-cong ·-idem ≈ʷ-refl)

  ·-lcomm : ∀ {l k j} → l · (k · j) ≈ʷ k · (l · j)
  ·-lcomm = ≈ʷ-trans (≈ʷ-sym ·-assoc) (≈ʷ-trans (·-cong ·-comm ≈ʷ-refl) ·-assoc)

  -- Every member of the list is one of the products.
  ∈-combos : {l : LatTerm X} {L : List (LatTerm X)} → l ∈ L → l ∈ combos L
  ∈-combos             (here refl)  = here refl
  ∈-combos {L = _ ∷ L} (there l∈)   = there (∈-++⁺ˡ (∈-combos l∈))

  -- Where a product of a sublist of k ∷ L sits.
  combos-view : {k j : LatTerm X} {L : List (LatTerm X)} → j ∈ combos (k ∷ L)
              → j ≡ k ⊎ (j ∈ combos L ⊎ Σ[ j' ∈ LatTerm X ] j' ∈ combos L × j ≡ k · j')
  combos-view             (here e)   = inj₁ e
  combos-view {k} {L = L} (there j∈) = inj₂ (map₂ (∈-map⁻ (k ·_)) (∈-++⁻ (combos L) j∈))

  -- A member of the list times a product is a product.
  combos-· : {l j : LatTerm X} {L : List (LatTerm X)} → l ∈ L → j ∈ combos L
           → Any (l · j ≈ʷ_) (combos L)
  combos-· {L = k ∷ L} l∈ j∈ = step l∈ (combos-view j∈)
    where
    -- A product in the right half of combos (k ∷ L).
    right : {v : LatTerm X} {j' : LatTerm X} → j' ∈ combos L → v ≈ʷ k · j'
          → Any (v ≈ʷ_) (combos (k ∷ L))
    right j'∈ e = lose (there (∈-++⁺ʳ (combos L) (∈-map⁺ (k ·_) j'∈))) e

    step : {l j : LatTerm X} → l ∈ k ∷ L
         → j ≡ k ⊎ (j ∈ combos L ⊎ Σ[ j' ∈ LatTerm X ] j' ∈ combos L × j ≡ k · j')
         → Any (l · j ≈ʷ_) (combos (k ∷ L))
    step (here refl)  (inj₁ refl)                     = here ·-idem
    step (here refl)  (inj₂ (inj₁ j∈L))               = right j∈L ≈ʷ-refl
    step (here refl)  (inj₂ (inj₂ (_ , j'∈ , refl)))  = right j'∈ ·-absorb
    step (there l∈L)  (inj₁ refl)                     = right (∈-combos l∈L) ·-comm
    step (there l∈L)  (inj₂ (inj₁ j∈L))               = there (++⁺ˡ (combos-· l∈L j∈L))
    step (there l∈L)  (inj₂ (inj₂ (_ , j'∈ , refl)))  =
      let (j″ , j″∈ , e) = find (combos-· l∈L j'∈)
      in right j″∈ (≈ʷ-trans ·-lcomm (·-cong ≈ʷ-refl e))

  -- The product of terms each equal to a member of L equals a product in combos L.
  fold-cover : {L : List (LatTerm X)} {u : LatTerm X} {us : List (LatTerm X)}
             → All (λ m → Any (m ≈ʷ_) L) (u ∷ us) → Any (fold u us ≈ʷ_) (combos L)
  fold-cover {us = []}     (p ∷ [])  = let (_ , l∈ , e) = find p in lose (∈-combos l∈) e
  fold-cover {us = _ ∷ _}  (p ∷ ps)  =
    let (_ , l∈ , e)   = find p
        (_ , j∈ , e')  = find (fold-cover ps)
        (_ , j″∈ , e″) = find (combos-· l∈ j∈)
    in lose j″∈ (≈ʷ-trans (·-cong e e') e″)
```

#### Finitely many elements of bounded complexity

Let `enum` list the generators.  `bounded n`{.AgdaFunction} lists the generators,
and for `n > 0` also the joins and the meets of the nonempty sublists of
`bounded (n - 1)` (`Bounded`{.AgdaModule}).  Every element of complexity at most
`n` equals a member of `bounded n` (`bounded-complete`{.AgdaFunction}), by
induction on `n` through its canonical form (`boundedᶜ`{.AgdaFunction}): a
generator is listed, and a canonical join is the join of its children, each of
smaller complexity and so equal to a member of `bounded (n - 1)`; dually for a
meet.  The list is never computed, only its length used.

```agda
module Bounded {X : Type χ} (_≟_ : DecidableEquality X) (enum : List X)
               (complete : ∀ x → x ∈ enum) where
  open Canonicalization _≟_ using ( canonical ; canonical-sound ; canonical-isCanonical )
  open Folds {X = X} _∨̇_ ∨̇-cong ∨̇-idem ∨̇-comm ∨̇-assoc
    using () renaming ( combos to joins ; fold to foldᴶ ; fold-cover to joins-cover )
  open Folds {X = X} _∧̇_ ∧̇-cong ∧̇-idem ∧̇-comm ∧̇-assoc
    using () renaming ( combos to meets ; fold to foldᴹ ; fold-cover to meets-cover )

  -- The fold of formal joins is the join of a list; likewise for meets.
  foldᴶ≡⋁⁺ : (u : LatTerm X) (us : List (LatTerm X)) → foldᴶ u us ≡ ⋁⁺ u us
  foldᴶ≡⋁⁺ u []        = refl
  foldᴶ≡⋁⁺ u (w ∷ ws)  = cong (u ∨̇_) (foldᴶ≡⋁⁺ w ws)

  foldᴹ≡⋀⁺ : (u : LatTerm X) (us : List (LatTerm X)) → foldᴹ u us ≡ ⋀⁺ u us
  foldᴹ≡⋀⁺ u []        = refl
  foldᴹ≡⋀⁺ u (w ∷ ws)  = cong (u ∧̇_) (foldᴹ≡⋀⁺ w ws)

  -- Representatives of every element of complexity at most n.
  bounded : ℕ → List (LatTerm X)
  bounded zero     = map ℊ enum
  bounded (suc n)  = map ℊ enum ++ joins (bounded n) ++ meets (bounded n)

  -- Every generator is listed at every bound.
  gen∈bounded : (n : ℕ) (x : X) → ℊ x ∈ bounded n
  gen∈bounded zero     x = ∈-map⁺ ℊ (complete x)
  gen∈bounded (suc n)  x = ∈-++⁺ˡ (∈-map⁺ ℊ (complete x))

  bounded-complete  : (n : ℕ) (w : LatTerm X) → complexity _≟_ w ≤ n → Any (w ≈ʷ_) (bounded n)
  boundedᶜ          : (n : ℕ) (w : LatTerm X) (C : CTerm X) → IsCanonical C → ⌊ C ⌋ ≈ʷ w
                    → depth C ≤ n → Any (w ≈ʷ_) (bounded n)

  bounded-complete n w b =
    boundedᶜ n w (canonical w) (canonical-isCanonical w) (canonical-sound w) b

  boundedᶜ n        w (genᶜ x)     _                 e _        = lose (gen∈bounded n x) (≈ʷ-sym e)
  boundedᶜ zero     w (joinᶜ _ _)  _                 _ ()
  boundedᶜ zero     w (meetᶜ _ _)  _                 _ ()
  boundedᶜ (suc n)  w (joinᶜ h t)  (cjoin _ cs _ _)  e (s≤s b)  =
    ++⁺ʳ (map ℊ enum) (++⁺ˡ (Any-≈ (joins-cover (All.tabulate child))))
    where
    -- Each child is listed one level down.
    child : ∀ {m} → m ∈ map ⌊_⌋ᴶ (h ∷ t) → Any (m ≈ʷ_) (bounded n)
    child m∈ =
      let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴶ m∈
      in subst (λ m → Any (m ≈ʷ_) (bounded n)) (sym m≡)
               (bounded-complete n ⌊ a ⌋ᴶ
                 (subst (_≤ n) (sym (complexityᴶ _≟_ (lookup cs a∈)))
                        (≤-trans (depthΣJ-upper a∈) b)))

    -- w is the join of its children.
    Any-≈ : Any (foldᴶ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t) ≈ʷ_) (joins (bounded n))
          → Any (w ≈ʷ_) (joins (bounded n))
    Any-≈ = Any.map λ p →
      ≈ʷ-trans (≈ʷ-sym e)
               (subst (_≈ʷ _) (trans (foldᴶ≡⋁⁺ ⌊ h ⌋ᴶ (map ⌊_⌋ᴶ t)) (sym (⋁ᴶ≡⋁⁺ h t))) p)
  boundedᶜ (suc n)  w (meetᶜ h t)  (cmeet _ cs _ _)  e (s≤s b)  =
    ++⁺ʳ (map ℊ enum) (++⁺ʳ (joins (bounded n)) (Any-≈ (meets-cover (All.tabulate child))))
    where
    -- Each child is listed one level down.
    child : ∀ {m} → m ∈ map ⌊_⌋ᴹ (h ∷ t) → Any (m ≈ʷ_) (bounded n)
    child m∈ =
      let (a , a∈ , m≡) = ∈-map⁻ ⌊_⌋ᴹ m∈
      in subst (λ m → Any (m ≈ʷ_) (bounded n)) (sym m≡)
               (bounded-complete n ⌊ a ⌋ᴹ
                 (subst (_≤ n) (sym (complexityᴹ _≟_ (lookup cs a∈)))
                        (≤-trans (depthΣM-upper a∈) b)))

    -- w is the meet of its children.
    Any-≈ : Any (foldᴹ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t) ≈ʷ_) (meets (bounded n))
          → Any (w ≈ʷ_) (meets (bounded n))
    Any-≈ = Any.map λ p →
      ≈ʷ-trans (≈ʷ-sym e)
               (subst (_≈ʷ _) (trans (foldᴹ≡⋀⁺ ⌊ h ⌋ᴹ (map ⌊_⌋ᴹ t)) (sym (⋀ᴹ≡⋀⁺ h t))) p)
```

#### Pigeonhole

A sequence of lattice terms each equal to a member of a list `L` repeats a value
up to equality among its first `length L + 1` entries
(`pigeonhole-≈`{.AgdaFunction}): the position in `L` of a witness for each entry
is a map from `Fin (length L + 1)` to `Fin (length L)`, which the standard
library's `pigeonhole`{.AgdaFunction} shows is not injective.

```agda
-- A sequence whose values all lie in a finite list repeats a value.
pigeonhole-≈ : (L : List (LatTerm X)) (u : ℕ → LatTerm X) → (∀ k → Any (u k ≈ʷ_) L)
             → Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] i < j × u i ≈ʷ u j
pigeonhole-≈ L u cov =
  let (i , j , i<j , fi≡fj) = pigeonhole (n<1+n (length L)) f
  in toℕ i , toℕ j , i<j ,
     ≈ʷ-trans (lookup-index (cov (toℕ i)))
              (subst (λ k → lookupᴸ L k ≈ʷ u (toℕ j)) (sym fi≡fj)
                     (≈ʷ-sym (lookup-index (cov (toℕ j)))))
  where
  -- The position of a witness for each of the first length L + 1 entries.
  f : Fin (suc (length L)) → Fin (length L)
  f k = index (cov (toℕ k))
```

#### Pigeonhole for tuples

A sequence of `n`-tuples of lattice terms, each entry equal to a member of `L`,
repeats a tuple up to equality among its first `length L ^ n + 1` entries
(`pigeonhole-≈ⁿ`{.AgdaFunction}).  The `n` positions of the witnesses for one
tuple are encoded as a single position in `Fin (length L ^ n)`
(`encode`{.AgdaFunction}), by the standard library's `combine`{.AgdaFunction}
one coordinate at a time; the encoding is injective
(`encode-injective`{.AgdaFunction}), so a repeat of the encoding is a repeat of
every coordinate.

```agda
-- n positions in Fin N, encoded as one position in Fin (N ^ n).
encode : {N : ℕ} (n : ℕ) → (Fin n → Fin N) → Fin (N ^ n)
encode zero     f = zero
encode (suc n)  f = combine (f zero) (encode n (f ∘ suc))

-- The encoding is injective.
encode-injective : {N : ℕ} (n : ℕ) (f g : Fin n → Fin N) → encode n f ≡ encode n g
                 → ∀ i → f i ≡ g i
encode-injective (suc n) f g e zero     =
  proj₁ (combine-injective (f zero) (encode n (f ∘ suc)) (g zero) (encode n (g ∘ suc)) e)
encode-injective (suc n) f g e (suc i)  =
  encode-injective n (f ∘ suc) (g ∘ suc)
    (proj₂ (combine-injective (f zero) (encode n (f ∘ suc)) (g zero) (encode n (g ∘ suc)) e)) i

-- A tuple of covered terms has a code in a finite set of explicit size.
tuple-code : (L : List (LatTerm X)) (n : ℕ) (u : Fin n → LatTerm X)
           → (∀ i → Any (u i ≈ʷ_) L) → Fin (length L ^ n)
tuple-code L n u cov = encode n (λ i → index (cov i))

-- Equal codes witness componentwise equality, even for different covers.
tuple-code-sound : (L : List (LatTerm X)) (n : ℕ)
                 (u v : Fin n → LatTerm X)
                 (cu : ∀ i → Any (u i ≈ʷ_) L)
                 (cv : ∀ i → Any (v i ≈ʷ_) L)
                 → tuple-code L n u cu ≡ tuple-code L n v cv
                 → ∀ i → u i ≈ʷ v i
tuple-code-sound L n u v cu cv e i =
  ≈ʷ-trans (lookup-index (cu i))
    (subst (λ p → lookupᴸ L p ≈ʷ v i)
           (sym (encode-injective n _ _ e i))
           (≈ʷ-sym (lookup-index (cv i))))

-- More than length L ^ n covered tuples contain two equivalent tuples.
finite-pigeonhole-≈ⁿ : (L : List (LatTerm X)) (n : ℕ) {m : ℕ}
                     → length L ^ n < m → (u : Fin m → Fin n → LatTerm X)
                     → (∀ k i → Any (u k i ≈ʷ_) L)
                     → Σ[ j ∈ Fin m ] Σ[ k ∈ Fin m ]
                         toℕ j < toℕ k × (∀ i → u j i ≈ʷ u k i)
finite-pigeonhole-≈ⁿ L n large u cov =
  let (j , k , j<k , e) = pigeonhole large (λ k → tuple-code L n (u k) (cov k))
  in j , k , j<k , tuple-code-sound L n (u j) (u k) (cov j) (cov k) e

-- A sequence of n-tuples whose entries all lie in a finite list repeats a tuple.
pigeonhole-≈ⁿ : (L : List (LatTerm X)) (n : ℕ) (u : ℕ → Fin n → LatTerm X)
              → (∀ k i → Any (u k i ≈ʷ_) L)
              → Σ[ j ∈ ℕ ] Σ[ k ∈ ℕ ] j < k × (∀ i → u j i ≈ʷ u k i)
pigeonhole-≈ⁿ L n u cov =
  let (j , k , j<k , e) =
        finite-pigeonhole-≈ⁿ L n (n<1+n (length L ^ n))
          (u ∘ toℕ) (λ k → cov (toℕ k))
  in toℕ j , toℕ k , j<k , e
```

The finite form `finite-pigeonhole-≈ⁿ`{.AgdaFunction} exposes the bound:
more than `length L ^ n` tuples have a repeated value.  Taking `L` to be
`bounded B`{.AgdaFunction} and using `bounded-complete`{.AgdaFunction}
therefore bounds the number of pairwise non-equivalent tuples of complexity
at most `B`.  The list can contain equivalent representatives; its length
is an upper bound, not a count of distinct elements.  The code's soundness
is all that is needed, with no canonical choice of representative.
