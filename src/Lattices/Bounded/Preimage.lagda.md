---
layout: default
file: "src/Lattices/Bounded/Preimage.lagda.md"
title: "Lattices.Bounded.Preimage module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Least preimages from the sets `D_k`: Theorem 2.6 and Lemma 2.7

This is the [Lattices.Bounded.Preimage][] module of the [agda-lattices][] library.

[Freese, Ježek, and Nation (1995)][], Theorem 2.6 (p. 31): if `D(L) = L`, every
homomorphism from a finitely generated lattice into `L` is lower bounded.  Its
proof, Lemma 2.7, is constructive once the order of `L` is decided and every
element comes with its rank.  For a homomorphism `h : FL(X) → L` with `X`
finite, the book defines the finite sets of terms
`H₀ = X`, `H_{k+1} = (H_k)^{∨∧}` (p. 28) and, for `a ∈ L`,

    β_k(a) = ⋀ { w ∈ H_k : a ≤ h w },

and proves that for `a ∈ D_k(L)` and every `w`, `a ≤ h w` holds exactly when
`β_k(a) ≤ w`.  So `β(a) = β_{ρ(a)}(a)` is the least preimage above `a`, the
datum of `LowerBounded h`{.AgdaRecord} in [Lattices.Bounded.Homomorphism][].
This module carries that out for `h` the extension of an assignment
`η : Fin (suc m) → L` that is onto, and dualizes it: `Dᵈ(L) = L` makes `h`
upper bounded, with `α(a)` the dual of the least preimage of `a` under the
same assignment into the dual lattice.  So a finitely generated lattice with a
decided order and `D(L) = L = Dᵈ(L)` is bounded in the sense of the data, and
Kostinsky's theorem ([Lattices.Kostinsky][]) applies to it with the book's
reading of "bounded": that is the use of this module.

The constructive content is the following.  The lists `H k`{.AgdaFunction} are
built with the joins and meets of nonempty sublists of
[Lattices.Free.Complexity][]'s `Folds`{.AgdaModule}, with the join `⊤` of all
the generators, the top of `FL(Fin (suc m))`, placed in `H 0` so that each
`H k` contains it and the meets below are never empty (the book's convention
`⋀ ∅ = 1`).  The members of `H k` whose image lies above `a` are selected by
the decision procedure for the order of `L`, and `βₖ k a`{.AgdaFunction} is
their meet.  Lemma 2.7's induction runs on `k` and, inside it, on the term
`w`: the only case with content is a join `w₁ ∨ w₂` with `a ≤ h w₁ ∨ h w₂`,
where either `a` lies below one of `h w₁`, `h w₂` (decided) or
`{h w₁, h w₂}` is a nontrivial join cover of `a`, which `a ∈ D_{k+1}(L)`
refines to a cover `T` inside `D_k(L)`; the join of the `β_k(t)`, `t ∈ T`, lies
below `w₁ ∨ w₂` by the induction hypothesis at `k`, has image above `a`, and
equals a member of `H (k+1)`, so `β_{k+1}(a)` lies below it.  The rank of `a`
is the witness of `D-total`{.AgdaFunction}; nothing else about it is used.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Bounded.Preimage where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin ; zero ; suc )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map ; filter ; allFin )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-allFin ; ∈-filter⁺ ; ∈-filter⁻ ; ∈-map⁺ ; ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product                           using ( _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( Func )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst )
open import Relation.Nullary                       using ( ¬_ ; Dec )
open import Relation.Nullary.Decidable.Core        using ( toSum )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsSurjective ; Image_∋_ )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Covers        using ( D ; D-total ; Dᵈ-total ; ≤ᵈ? )
open import Lattices.Bounded.Homomorphism  using ( LowerBounded ; UpperBounded ; Bounded )
open import Lattices.Dual                  using ( dualLattice ; module LatticeDual )
open import Lattices.Free.Canonical.Basic  using ( ⋁⁺ ; ⋀⁺ ; ⋁⁺-upper ; ⋁⁺-least ; ⋀⁺-lower ; ≈ʷ-refl
                                                 ; ∨̇-cong ; ∨̇-idem ; ∨̇-comm ; ∨̇-assoc
                                                 ; ∧̇-cong ; ∧̇-idem ; ∧̇-comm ; ∧̇-assoc )
open import Lattices.Free.Complexity       using ( module Folds )
open import Lattices.Free.Duality          using ( dual ; dual-involutive ; dual-antitone )
open import Lattices.Free.Term             using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ ; module Evaluation )
open import Lattices.Free.Universal        using ( FL ; FL-extend ; FL-extend-hom ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Lattices.Free.Whitman          using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤∧ ; ≤ʷ-trans ; ≤∨ˡ ; ≤∨ʳ ; ∧ˡ≤ )
open import Lattices.Generation            using ( _≤⋁_ ; ≤⋁⁺ ) renaming ( ⋁⁺ to ⋁⁺ᴸ )
open import Lattices.Semidistributive      using ( hom-preserves-≤ )

private variable αᴸ ρᴸ : Level
```
-->

#### The setting

Fix a lattice `𝑳`{.AgdaBound} with a decision procedure for its order, an
assignment `η : Fin (suc m) → L` whose extension `f : FL(suc m) → L` is onto,
and write `f w` for `⟦ w ⟧ η`.  The generators are listed by
`gens`{.AgdaFunction}, their join `⊤`{.AgdaFunction} is the top of the free
lattice (`≤⊤`{.AgdaFunction}), and every element of `𝑳`{.AgdaBound} lies below
`f ⊤` (`≤f⊤`{.AgdaFunction}).  The meet `⋀* S`{.AgdaFunction} of a list of
terms is `⊤` for the empty list; it lies below every member, and its image lies
above whatever lies below the images of all the members.

```agda
module LowerBoundedFromD {m : ℕ} (𝑳 : Lattice αᴸ ρᴸ)
                         (_≤?_ : ∀ a b → Dec (Lattice-Order._≤_ 𝑳 a b))
                         (η : Fin (suc m) → 𝕌[ proj₁ 𝑳 ])
                         (onto : IsSurjective (FL-extend 𝑳 η)) where
  open Evaluation 𝑳         using ( ⟦_⟧ )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ )
  open Lattice-Order 𝑳      using ( _≤_ ; ≤-trans ; ≤-reflexive ; ≤-respʳ-≈
                                  ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  private
    L : Type αᴸ
    L = 𝕌[ proj₁ 𝑳 ]

    T : Type
    T = LatTerm (Fin (suc m))

    f : T → L
    f w = ⟦ w ⟧ η

  -- The generators, as terms.
  gens : List T
  gens = map ℊ (allFin (suc m))

  -- The join of a list of terms, with the first generator for the empty list.
  ⋁* : List T → T
  ⋁* []        = ℊ zero
  ⋁* (w ∷ ws)  = ⋁⁺ w ws

  ⋁*-upper : ∀ {w S} → w ∈ S → w ≤ʷ ⋁* S
  ⋁*-upper {S = d ∷ ds} w∈ = ⋁⁺-upper {w = d} {ws = ds} w∈

  -- The join of all the generators, the top of the free lattice.
  ⊤ : T
  ⊤ = ⋁* gens

  ≤⊤ : ∀ w → w ≤ʷ ⊤
  ≤⊤ (ℊ x)      = ⋁*-upper (∈-map⁺ ℊ (∈-allFin x))
  ≤⊤ (w₁ ∨̇ w₂)  = ∨≤ (≤⊤ w₁) (≤⊤ w₂)
  ≤⊤ (w₁ ∧̇ w₂)  = ∧ˡ≤ (≤⊤ w₁)

  -- Every element lies below f ⊤, since f is onto.
  ≤f⊤ : ∀ a → a ≤ f ⊤
  ≤f⊤ a with onto {a}
  ... | Image_∋_.eq w a≈fw =
    ≤-trans (≤-reflexive a≈fw) (hom-preserves-≤ (FL (Fin (suc m))) 𝑳 (FL-extend-hom 𝑳 η) (≤ʷ→≤ (≤⊤ w)))

  -- The meet of a list of terms, ⊤ for the empty list.
  ⋀* : List T → T
  ⋀* []        = ⊤
  ⋀* (w ∷ ws)  = ⋀⁺ w ws

  ⋀*-lower : ∀ {w S} → w ∈ S → ⋀* S ≤ʷ w
  ⋀*-lower {S = d ∷ ds} w∈ = ⋀⁺-lower {w = d} {ws = ds} w∈

  -- An element below the images of all the members lies below the image of the meet.
  ⋀⁺-above : ∀ {a} s ss → All (λ u → a ≤ f u) (s ∷ ss) → a ≤ f (⋀⁺ s ss)
  ⋀⁺-above s []         (p ∷ [])  = p
  ⋀⁺-above s (s' ∷ ss)  (p ∷ ps)  = ∧-greatest p (⋀⁺-above s' ss ps)

  ⋀*-above : ∀ {a} S → All (λ u → a ≤ f u) S → a ≤ f (⋀* S)
  ⋀*-above {a} []       []  = ≤f⊤ a
  ⋀*-above     (s ∷ ss) ps  = ⋀⁺-above s ss ps
```

#### The lists `H_k`

`H 0` is the generators with `⊤`, and `H (k+1)` the meets of nonempty
sublists of the joins of nonempty sublists of the meets of nonempty sublists
of `H k`, with the `combos`{.AgdaFunction} of `Folds`{.AgdaModule}: the book's
`(H_k)^{∨∧}` after closing `H_k` under meets, so that no closure property of
`H k` itself has to be proved.  Every `H k` contains `⊤` and the generators.
The folds of `Folds`{.AgdaModule} are the list joins and meets of
[Lattices.Free.Canonical.Basic][].

```agda
  module J = Folds {X = Fin (suc m)} _∨̇_ ∨̇-cong ∨̇-idem ∨̇-comm ∨̇-assoc
  module M = Folds {X = Fin (suc m)} _∧̇_ ∧̇-cong ∧̇-idem ∧̇-comm ∧̇-assoc

  -- The lists H_k.
  H : ℕ → List T
  H zero     = ⊤ ∷ gens
  H (suc k)  = M.combos (J.combos (M.combos (H k)))

  ⊤∈H : ∀ k → ⊤ ∈ H k
  ⊤∈H zero     = here refl
  ⊤∈H (suc k)  = M.∈-combos (J.∈-combos (M.∈-combos (⊤∈H k)))

  gen∈H : ∀ k x → ℊ x ∈ H k
  gen∈H zero     x = there (∈-map⁺ ℊ (∈-allFin x))
  gen∈H (suc k)  x = M.∈-combos (J.∈-combos (M.∈-combos (gen∈H k x)))

  foldᴶ≡⋁⁺ : ∀ u us → J.fold u us ≡ ⋁⁺ u us
  foldᴶ≡⋁⁺ u []        = refl
  foldᴶ≡⋁⁺ u (w ∷ ws)  = cong (u ∨̇_) (foldᴶ≡⋁⁺ w ws)

  foldᴹ≡⋀⁺ : ∀ u us → M.fold u us ≡ ⋀⁺ u us
  foldᴹ≡⋀⁺ u []        = refl
  foldᴹ≡⋀⁺ u (w ∷ ws)  = cong (u ∧̇_) (foldᴹ≡⋀⁺ w ws)
```

#### The maps `β_k`

`above a S`{.AgdaFunction} lists the members of `S` whose image lies above
`a`, by the decision procedure, and `βₖ k a`{.AgdaFunction} is the meet of
`above a (H k)`.  Its image lies above `a` (`βₖ-above`{.AgdaFunction}), and it
lies below every member of `H k` whose image lies above `a`
(`βₖ-below`{.AgdaFunction}): the two halves of the book's Theorem 2.2 (2).  As
a meet of members of `H k`, it equals a member of the meets of `H k`
(`βₖ-cover`{.AgdaFunction}), and a join of such `β_k` equals a member of
`H (k+1)` (`⋁β-cover`{.AgdaFunction}), with image above the join of the
elements it was built from (`⋁β-above`{.AgdaFunction}).

```agda
  -- The members of a list whose image lies above a.
  above : L → List T → List T
  above a S = filter (λ w → a ≤? f w) S

  above⊆ : ∀ a S → All (_∈ S) (above a S)
  above⊆ a S = All.tabulate {xs = above a S} λ {w} w∈ → proj₁ (∈-filter⁻ (λ w → a ≤? f w) {xs = S} w∈)

  above-≤ : ∀ a S → All (λ w → a ≤ f w) (above a S)
  above-≤ a S = All.tabulate {xs = above a S} λ {w} w∈ → proj₂ (∈-filter⁻ (λ w → a ≤? f w) {xs = S} w∈)

  -- β_k(a): the meet of the members of H_k whose image lies above a.
  βₖ : ℕ → L → T
  βₖ k a = ⋀* (above a (H k))

  -- a ≤ f (β_k a).
  βₖ-above : ∀ k a → a ≤ f (βₖ k a)
  βₖ-above k a = ⋀*-above (above a (H k)) (above-≤ a (H k))

  -- β_k a lies below every member of H_k whose image lies above a.
  βₖ-below : ∀ k a {w} → w ∈ H k → a ≤ f w → βₖ k a ≤ʷ w
  βₖ-below k a {w} w∈ p = ⋀*-lower (∈-filter⁺ (λ w → a ≤? f w) {xs = H k} w∈ p)

  -- The meet of members of H_k equals a member of the meets of H_k.
  ⋀*-cover : ∀ k S → All (_∈ H k) S → Any (⋀* S ≈ʷ_) (M.combos (H k))
  ⋀*-cover k []        []   = lose (M.∈-combos (⊤∈H k)) ≈ʷ-refl
  ⋀*-cover k (s ∷ ss)  all  =
    subst (λ u → Any (u ≈ʷ_) (M.combos (H k))) (foldᴹ≡⋀⁺ s ss)
          (M.fold-cover (All.map (λ s∈ → lose s∈ ≈ʷ-refl) all))

  βₖ-cover : ∀ k a → Any (βₖ k a ≈ʷ_) (M.combos (H k))
  βₖ-cover k a = ⋀*-cover k (above a (H k)) (above⊆ a (H k))

  -- The β_k of a list of elements, each a member of the meets of H_k up to equality.
  βs-cover : ∀ k ts → All (λ v → Any (v ≈ʷ_) (M.combos (H k))) (map (βₖ k) ts)
  βs-cover k []        = []
  βs-cover k (t ∷ ts)  = βₖ-cover k t ∷ βs-cover k ts

  -- The join of the β_k of a nonempty list equals a member of H_{k+1}.
  ⋁β-cover : ∀ k t ts → Any (⋁⁺ (βₖ k t) (map (βₖ k) ts) ≈ʷ_) (H (suc k))
  ⋁β-cover k t ts =
    let (J′ , J′∈ , e) = find (J.fold-cover {L = M.combos (H k)} (βs-cover k (t ∷ ts)))
    in lose (M.∈-combos J′∈) (subst (_≈ʷ J′) (foldᴶ≡⋁⁺ (βₖ k t) (map (βₖ k) ts)) e)

  -- The join of a list of elements lies below the image of the join of their β_k.
  ⋁β-above : ∀ k t ts → ⋁⁺ᴸ 𝑳 t ts ≤ f (⋁⁺ (βₖ k t) (map (βₖ k) ts))
  ⋁β-above k t []          = βₖ-above k t
  ⋁β-above k t (t' ∷ ts)   =
    ∨-least (≤-trans (βₖ-above k t) ∨-upperˡ) (≤-trans (⋁β-above k t' ts) ∨-upperʳ)
```

#### Lemma 2.7

For `a ∈ D_k(L)` and every term `w`, `a ≤ f w` implies `β_k(a) ≤ w`, by
induction on `k` and on `w`.  A generator is a member of `H k`; a meet splits;
a join `w₁ ∨ w₂` splits by join primality when `k = 0`, and otherwise either
`a` lies below `f w₁` or `f w₂`, decided, or `{f w₁, f w₂}` is a nontrivial
join cover of `a`, refined by `a ∈ D_{k+1}` to a cover `T ⊆ D_k` with each
member below `f w₁` or `f w₂`.  The join `J` of the `β_k(t)`, `t ∈ T`, then
lies below `w₁ ∨ w₂` by the induction hypothesis at `k`, its image lies above
`a`, and it equals a member `J′` of `H (k+1)`, so `β_{k+1}(a) ≤ J′ = J`.

```agda
  -- Lemma 2.7: for a ∈ D_k and every term w, a ≤ f w implies β_k a ≤ w.
  least : ∀ k a → D 𝑳 k a → ∀ w → a ≤ f w → βₖ k a ≤ʷ w
  least k a d (ℊ x)      p = βₖ-below k a (gen∈H k x) p
  least k a d (w₁ ∧̇ w₂)  p =
    ≤∧ (least k a d w₁ (≤-trans p ∧-lowerˡ)) (least k a d w₂ (≤-trans p ∧-lowerʳ))
  least zero a jp (w₁ ∨̇ w₂) p =
    [ (λ q → ≤∨ˡ (least zero a jp w₁ q)) , (λ q → ≤∨ʳ (least zero a jp w₂ q)) ]′ (jp p)
  least (suc k) a d (w₁ ∨̇ w₂) p =
    [ (λ q → ≤∨ˡ (least (suc k) a d w₁ q))
    , (λ ¬q₁ → [ (λ q → ≤∨ʳ (least (suc k) a d w₂ q)) , (λ ¬q₂ → nontrivial ¬q₁ ¬q₂) ]′
                  (toSum (a ≤? f w₂))) ]′
    (toSum (a ≤? f w₁))
    where
    -- A member of the refinement, below f w₁ or f w₂, has its β_k below w₁ ∨ w₂.
    bound : ∀ u → D 𝑳 k u → Any (u ≤_) (f w₁ ∷ f w₂ ∷ []) → βₖ k u ≤ʷ w₁ ∨̇ w₂
    bound u du (here q)          = ≤∨ˡ (least k u du w₁ q)
    bound u du (there (here q))  = ≤∨ʳ (least k u du w₂ q)
    bound u du (there (there ()))

    from-refinement : ∀ T′ → All (λ t → Any (t ≤_) (f w₁ ∷ f w₂ ∷ [])) T′ → All (D 𝑳 k) T′
                    → _≤⋁_ 𝑳 a T′ → βₖ (suc k) a ≤ʷ w₁ ∨̇ w₂
    from-refinement T′ T′≪S allT (≤⋁⁺ {t} {ts} a≤T′) =
      ≤ʷ-trans (≤ʷ-trans (βₖ-below (suc k) a J′∈ a≤fJ′) (proj₂ e)) J≤w
      where
      -- The join of the β_k of the refinement.
      J : T
      J = ⋁⁺ (βₖ k t) (map (βₖ k) ts)

      J≤w : J ≤ʷ w₁ ∨̇ w₂
      J≤w = ⋁⁺-least {w = βₖ k t} {ws = map (βₖ k) ts} λ {v} v∈ →
        let (u , u∈ , v≡) = ∈-map⁻ (βₖ k) {xs = t ∷ ts} v∈
        in subst (_≤ʷ w₁ ∨̇ w₂) (sym v≡) (bound u (All.lookup allT u∈) (All.lookup T′≪S u∈))

      -- The member of H (k+1) that J equals.
      J′ : T
      J′ = proj₁ (find (⋁β-cover k t ts))

      J′∈ : J′ ∈ H (suc k)
      J′∈ = proj₁ (proj₂ (find (⋁β-cover k t ts)))

      e : J ≈ʷ J′
      e = proj₂ (proj₂ (find (⋁β-cover k t ts)))

      a≤fJ′ : a ≤ f J′
      a≤fJ′ = ≤-respʳ-≈ (Func.cong (FL-extend 𝑳 η) e) (≤-trans a≤T′ (⋁β-above k t ts))

    -- The cover {f w₁, f w₂} is nontrivial: refine it inside D_k.
    nontrivial : ¬ (a ≤ f w₁) → ¬ (a ≤ f w₂) → βₖ (suc k) a ≤ʷ w₁ ∨̇ w₂
    nontrivial ¬q₁ ¬q₂ =
      let (T′ , T′≪S , allT , a≤T′) = d (f w₁ ∷ f w₂ ∷ []) (≤⋁⁺ p) (¬q₁ ∷ ¬q₂ ∷ [])
      in from-refinement T′ T′≪S allT a≤T′
```

#### Theorem 2.6

With `D(L) = L`, the least preimage of `a` is `β_{ρ(a)}(a)` for the rank
`ρ(a)` that `D-total`{.AgdaFunction} supplies: `f` is lower bounded.

```agda
  -- Theorem 2.6: D(L) = L makes f lower bounded, with β a = β_{rank a} a.
  lowerBounded : D-total 𝑳 → LowerBounded (FL (Fin (suc m))) 𝑳 (FL-extend-hom 𝑳 η)
  lowerBounded dt = record
    { β        = λ a → βₖ (proj₁ (dt a)) a
    ; β-above  = λ a → βₖ-above (proj₁ (dt a)) a
    ; β-least  = λ a w p → ≤ʷ→≤ (least (proj₁ (dt a)) a (proj₂ (dt a)) w p)
    }
```

#### The dual: upper bounds from `Dᵈ(L) = L`

In the dual lattice a term evaluates as its dual evaluates in
`𝑳`{.AgdaBound} (`⟦⟧ᵈ`{.AgdaFunction}, in the module `Dual`{.AgdaModule},
for any number of generators), so the assignment `η` is onto for the dual
too, and Theorem 2.6 for the dual gives, for each `a`, the least term `β a`
with `a ≤ᵈ ⟦ β a ⟧ᵈ`, that is, with `f (dual (β a)) ≤ a`.  Its dual is the
greatest preimage below `a`: `f` is upper bounded when `Dᵈ(L) = L`, and
bounded when `D(L) = L = Dᵈ(L)`.

```agda
module Dual {n : ℕ} (𝑳 : Lattice αᴸ ρᴸ) (η : Fin n → 𝕌[ proj₁ 𝑳 ])
            (onto : IsSurjective (FL-extend 𝑳 η)) where
  open Evaluation 𝑳                    using ( ⟦_⟧ )
  open Evaluation (dualLattice 𝑳)      using () renaming ( ⟦_⟧ to ⟦_⟧ᵈ )
  open Lattice-Op 𝑳                    using ( _∧_ ; _∨_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]             using ( reflexive ) renaming ( trans to ≈trans )

  -- A term evaluates in the dual lattice as its dual evaluates in 𝑳.
  ⟦⟧ᵈ : ∀ w → ⟦ w ⟧ᵈ η ≡ ⟦ dual w ⟧ η
  ⟦⟧ᵈ (ℊ x)    = refl
  ⟦⟧ᵈ (s ∧̇ t)  = cong₂ _∨_ (⟦⟧ᵈ s) (⟦⟧ᵈ t)
  ⟦⟧ᵈ (s ∨̇ t)  = cong₂ _∧_ (⟦⟧ᵈ s) (⟦⟧ᵈ t)

  -- The value of dual w in the dual lattice is the value of w in 𝑳.
  ⟦dual⟧ᵈ : ∀ w → ⟦ dual w ⟧ᵈ η ≡ ⟦ w ⟧ η
  ⟦dual⟧ᵈ w = trans (⟦⟧ᵈ (dual w)) (cong (λ u → ⟦ u ⟧ η) (dual-involutive w))

  -- The assignment is onto for the dual lattice too.
  ontoᵈ : IsSurjective (FL-extend (dualLattice 𝑳) η)
  ontoᵈ {a} with onto {a}
  ... | Image_∋_.eq w a≈fw = Image_∋_.eq (dual w) (≈trans a≈fw (reflexive (sym (⟦dual⟧ᵈ w))))

module UpperBoundedFromD {m : ℕ} (𝑳 : Lattice αᴸ ρᴸ)
                         (_≤?_ : ∀ a b → Dec (Lattice-Order._≤_ 𝑳 a b))
                         (η : Fin (suc m) → 𝕌[ proj₁ 𝑳 ])
                         (onto : IsSurjective (FL-extend 𝑳 η)) where
  open Lattice-Order 𝑳                 using ( ≤-respˡ-≈ )
  open LatticeDual 𝑳                   using ( ≤ᵈ-flip ; ≤ᵈ-unflip )
  open Setoid 𝔻[ proj₁ 𝑳 ]             using ( reflexive )
  open Dual 𝑳 η onto                   using ( ⟦⟧ᵈ ; ⟦dual⟧ᵈ ; ontoᵈ )

  private
    module Low = LowerBoundedFromD (dualLattice 𝑳) (≤ᵈ? 𝑳 _≤?_) η ontoᵈ

  -- The dual of Theorem 2.6: Dᵈ(L) = L makes f upper bounded.
  upperBounded : Dᵈ-total 𝑳 → UpperBounded (FL (Fin (suc m))) 𝑳 (FL-extend-hom 𝑳 η)
  upperBounded dtᵈ = record
    { α           = λ a → dual (β a)
    ; α-below     = λ a → ≤-respˡ-≈ (reflexive (⟦⟧ᵈ (β a))) (≤ᵈ-flip (β-above a))
    ; α-greatest  = λ a w fw≤a →
        ≤ʷ→≤ (subst (_≤ʷ dual (β a)) (dual-involutive w)
                (dual-antitone (≤→≤ʷ (β-least a (dual w)
                  (≤ᵈ-unflip (≤-respˡ-≈ (reflexive (sym (⟦dual⟧ᵈ w))) fw≤a))))))
    }
    where open LowerBounded (Low.lowerBounded dtᵈ)

-- A finitely generated lattice with a decided order and D(L) = L = Dᵈ(L) has a bounded
-- presentation: the book's reading of "bounded" gives the data.
bounded : ∀ {m} (𝑳 : Lattice αᴸ ρᴸ) → (∀ a b → Dec (Lattice-Order._≤_ 𝑳 a b))
        → (η : Fin (suc m) → 𝕌[ proj₁ 𝑳 ]) → IsSurjective (FL-extend 𝑳 η)
        → D-total 𝑳 → Dᵈ-total 𝑳 → Bounded (FL (Fin (suc m))) 𝑳 (FL-extend-hom 𝑳 η)
bounded 𝑳 _≤?_ η onto dt dtᵈ =
  LowerBoundedFromD.lowerBounded 𝑳 _≤?_ η onto dt , UpperBoundedFromD.upperBounded 𝑳 _≤?_ η onto dtᵈ
```

The module checks in about a second of its own.
