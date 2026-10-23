---
layout: default
file: "src/Lattices/Kostinsky.lagda.md"
title: "Lattices.Kostinsky module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Kostinsky's theorem: the finitely generated sublattices of free lattices

This is the [Lattices.Kostinsky][] module of the [agda-lattices][] library.

For a finitely generated lattice `L`, the following are equivalent: `L` is
projective; `L` is a sublattice of a free lattice; and `L` is bounded and
satisfies Whitman's condition (W).  This is Kostinsky's theorem ("Projective
lattices and bounded homomorphisms", *Pacific J. Math.* 40 (1972), Theorems
3.3 and 3.4 with the remark after 3.4), extending McKenzie's and Jónsson's
finite case; [Freese, Ježek, and Nation (1995)][] state it as Corollaries 5.9
and 5.10 (p. 100) and reach it through their characterization of all projective
lattices, Theorem 5.7.  Jónsson and Nation's report of 1977 states it as
Theorem 2.1 (b), and Nation's paper of 1982 restates it in its closing
paragraph.  This module proves it with Kostinsky's own proofs, for a lattice
`𝑳`{.AgdaBound} presented by an epimorphism `f : FL(n) ↠ 𝑳`, with "bounded"
read as the data of [Lattices.Bounded.Homomorphism][]: the least and greatest
preimages `β` and `α` under `f`, with their laws.

+  **The hard direction** (Kostinsky's Theorem 3.3, pp. 117 to 118) is proved
   for every epimorphism `f : FL(X) ↠ L` with bounds `β` and `α`, for any set
   `X`.  Let `h` be the endomorphism of `FL(X)` extending `x ↦ α (f x)`.  An
   induction on `w` gives `β (f w) ≤ h w ≤ α (f w)`, so `f ∘ h = f`; and a
   second induction on `w`, with (W) in `L` in the join case and the law of `α`
   in the generator case, gives `h (β b₁ ∧ β b₂) ≤ h w` whenever
   `b₁ ∧ b₂ ≤ f w`, which makes `g = h ∘ β` preserve meets, as it preserves
   joins because `β` does.  So `g` is a homomorphic section of `f`: `L` is a
   retract of `FL(X)`, hence projective (Theorem 5.1), and `g` embeds it in
   `FL(X)` itself.  The proof needs neither minimal join covers nor ranks, and
   no decided order; Kostinsky's case split on whether some generator lies
   above `b₁ ∧ b₂` under `f` is absorbed by the second induction.
+  **The easy direction** is Kostinsky's Note 2.4 with his Lemma 3.1
   ([Lattices.Free.Bounded][]): an embedding `e : L ↪ FL(Y)`, `Y` with
   decidable equality, composed with `f : FL(n) ↠ L`, is a substitution
   `FL(n) → FL(Y)`, which is bounded; the least `a` with `e b ≤ e (f a)` is
   `β b`, since `e` reflects the order, and dually for `α`.  Whitman's
   condition passes to sublattices ([Lattices.Nation][]).  This is the content
   of the book's Corollary 2.16 for the lattices at hand.
+  **The equivalences**, for `𝑳`{.AgdaBound} with `f : FL(n) ↠ 𝑳`: that `f`
   has a section, that `𝑳`{.AgdaBound} is projective, that it embeds in
   `FL(n)`, that it embeds in some `FL(Y)` with `Y` decidable, and that `f` is
   bounded and `𝑳`{.AgdaBound} satisfies (W), are all equivalent
   (`Presentation`{.AgdaModule}).  Projectivity is asked at the levels of
   `FL(n)` and of `𝑳`{.AgdaBound}, and comes back at every choice of levels.
   The theorem holds for any epimorphism `f` from `FL(n)`, not only for the
   extension of an assignment of the generators
   (`embeds⇔bounded×W`{.AgdaFunction}), and for a quotient `FL(n)/ψ` by any
   congruence `ψ`, with the quotient map as `f`
   (`quotient-embeds⇔bounded×W`{.AgdaFunction}); nothing need be assumed of
   `ψ`.

On the reading of "bounded".  The book defines a finitely generated lattice to
be bounded by the equivalent conditions of its Theorem 2.13, one of which,
`D(L) = L = Dᵈ(L)`, speaks of the lattice alone.  The data of a bounded
epimorphism, used here, decide the order of `𝑳`{.AgdaBound}: `a ≤ b` exactly
when `β a ≤ β b` in `FL(n)`, whose order Whitman's procedure decides.  So the
theorem in this form cannot apply to a quotient `FL(n)/ψ` whose order is
undecided, and that is as it should be: for any proposition `P`, the congruence
"equal, or `P`" of `FL(n)` has a quotient that satisfies (W) and has
`D(L) = L = Dᵈ(L)` with the ranks of `FL(n)`, while an embedding of it into
`FL(n)` would decide `P`.  [Lattices.Bounded.Covers][] defines the sets
`D_k(L)` and [Lattices.Bounded.Preimage][] proves that `D(L) = L` with a
decided order gives the data, so the theorem holds with the book's reading for
every finitely generated lattice whose order is decided.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Kostinsky where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥ ; ⊥-elim )
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.Nat.Base                          using ( ℕ )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Function                               using ( Func ; _⇔_ ; mk⇔ ; id )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.Definitions            using ( DecidableEquality )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret      using ( interp-cong )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Congruences.Basic            using ( Con ; IsCongruence )
open import Setoid.Functions                    using ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Homomorphism
  using  ( LowerBounded ; UpperBounded ; Bounded ; module BoundedProperties ; Bounded-resp
         ; FinitelyGenerated ; BoundedLattice )
open import Lattices.Free.Bounded          using ( GreatestBelow ; NoneBelow ; LeastAbove ; NoneAbove
                                                 ; greatestBelow? ; leastAbove? )
open import Lattices.Free.Canonical.Basic  using ( ≈ʷ-refl ; ≈ʷ-trans )
open import Lattices.Free.Substitution     using ( Sub ; _[_] ; []-mono ; []-cong ; hom-induced )
open import Lattices.Free.Term             using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ ; module Evaluation )
open import Lattices.Free.Universal        using ( FL ; FL-extend ; FL-extend-hom ; FL-extend-unique
                                                 ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Lattices.Free.Whitman          using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤∧ ; ≤ʷ-refl ; ≤ʷ-trans
                                                 ; ≤∨ˡ ; ≤∨ʳ ; ∧ˡ≤ ; ∧ʳ≤ )
open import Lattices.Nation                using ( Embeds ; embeds→SatisfiesW )
open import Lattices.Projective            using ( IsSection ; HasSection ; _IsRetractOf_ ; IsProjective
                                                 ; section→Embeds ; retractOfFree→projective
                                                 ; projective→hasSection ; sections→retractOfFL )
open import Lattices.Quotient              using ( _╱ˡ_ )
open import Lattices.Semidistributive      using ( SatisfiesW ; hom-preserves-≤ ; hom-reflects-≤ )

open Func using () renaming ( to to _⟨$⟩_ )

private variable αᴸ ρᴸ α₁ ρ₁ α₂ ρ₂ χ υ ℓ : Level
```
-->

#### The hard direction: a bounded epimorphism onto a lattice with (W) has a section

Fix a lattice `𝑳`{.AgdaBound}, an assignment `η : X → L` whose extension
`f : FL(X) → L` is onto, the bounds `β` and `α` of `f`, and (W) in
`𝑳`{.AgdaBound}.  The endomorphism `h` of `FL(X)` is substitution by
`τ x = α (η x)`.  The values of `f` are the evaluations `⟦ w ⟧ η`, so the
inductions below run on the term `w`.

```agda
module HardDirection {X : Type χ} (𝑳 : Lattice αᴸ ρᴸ) (η : X → 𝕌[ proj₁ 𝑳 ])
                     (onto : IsSurjective (FL-extend 𝑳 η))
                     (bd : Bounded (FL X) 𝑳 (FL-extend-hom 𝑳 η)) (W : SatisfiesW 𝑳) where
  private
    f : hom (proj₁ (FL X)) (proj₁ 𝑳)
    f = FL-extend-hom 𝑳 η

  open Evaluation 𝑳         using ( ⟦_⟧ )
  open Lattice-Op 𝑳         using ( _∧_ ; _∨_ ; ∧-cong )
  open Lattice-Order 𝑳      using ( _≤_ ; ≤-trans ; ≤-antisym ; ≤-respˡ-≈
                                  ; ∧-lowerˡ ; ∧-lowerʳ ; ∨-upperˡ ; ∨-upperʳ )
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; refl ; sym ; trans )
  open BoundedProperties (FL X) 𝑳 f bd

  -- The endomorphism of FL(X) extending x ↦ α (η x), as a substitution.
  τ : Sub X X
  τ x = α (η x)
```

Kostinsky's sandwich, `β (f w) ≤ h w ≤ α (f w)`, by induction on `w`: at a
generator it is `β ≤ α`; at a join, `β` preserves joins and `α` is monotone; at
a meet, `β` is monotone and `α` preserves meets.  Applying `f` to the sandwich
and using `f (β b) = b = f (α b)` gives `f (h w) = f w`.

```agda
  -- β (f w) ≤ h w ≤ α (f w).
  sandwich : ∀ w → (β (⟦ w ⟧ η) ≤ʷ w [ τ ]) × (w [ τ ] ≤ʷ α (⟦ w ⟧ η))
  sandwich (ℊ x)      = ≤→≤ʷ (β≤α onto (η x)) , ≤ʷ-refl
  sandwich (w₁ ∨̇ w₂)  =
    let (l₁ , u₁) = sandwich w₁
        (l₂ , u₂) = sandwich w₂
    in ≤ʷ-trans (proj₁ (β-∨ (⟦ w₁ ⟧ η) (⟦ w₂ ⟧ η))) (∨≤ (≤∨ˡ l₁) (≤∨ʳ l₂))
     , ∨≤ (≤ʷ-trans u₁ (≤→≤ʷ (α-mono ∨-upperˡ))) (≤ʷ-trans u₂ (≤→≤ʷ (α-mono ∨-upperʳ)))
  sandwich (w₁ ∧̇ w₂)  =
    let (l₁ , u₁) = sandwich w₁
        (l₂ , u₂) = sandwich w₂
    in ≤∧ (≤ʷ-trans (≤→≤ʷ (β-mono ∧-lowerˡ)) l₁) (≤ʷ-trans (≤→≤ʷ (β-mono ∧-lowerʳ)) l₂)
     , ≤ʷ-trans (≤∧ (∧ˡ≤ u₁) (∧ʳ≤ u₂)) (proj₂ (α-∧ (⟦ w₁ ⟧ η) (⟦ w₂ ⟧ η)))

  -- f ∘ h is f.
  f-τ : ∀ w → ⟦ w [ τ ] ⟧ η ≈ ⟦ w ⟧ η
  f-τ w = ≤-antisym
    (≤-trans (hom-preserves-≤ (FL X) 𝑳 f (≤ʷ→≤ (proj₂ (sandwich w)))) (α-below (⟦ w ⟧ η)))
    (≤-trans (β-above (⟦ w ⟧ η)) (hom-preserves-≤ (FL X) 𝑳 f (≤ʷ→≤ (proj₁ (sandwich w)))))

  -- f sends h (β b₁ ∧ β b₂) to b₁ ∧ b₂.
  f-β∧ : ∀ b₁ b₂ → ⟦ (β b₁ ∧̇ β b₂) [ τ ] ⟧ η ≈ b₁ ∧ b₂
  f-β∧ b₁ b₂ = trans (f-τ (β b₁ ∧̇ β b₂)) (∧-cong (β-section onto b₁) (β-section onto b₂))
```

The claim that makes `h ∘ β` preserve meets: `h (β b₁ ∧ β b₂) ≤ h w` whenever
`b₁ ∧ b₂ ≤ f w`, by induction on `w`.  At a generator `x`, `h x = α (η x)`, and
the law of `α` asks for `f (h (β b₁ ∧ β b₂)) ≤ η x`, which is `b₁ ∧ b₂ ≤ η x`.
At a meet, both meetands are above `b₁ ∧ b₂`.  At a join `w₁ ∨ w₂`, Whitman's
condition in `𝑳`{.AgdaBound} applied to `b₁ ∧ b₂ ≤ f w₁ ∨ f w₂` gives four
cases: if `bᵢ ≤ f (w₁ ∨ w₂)`, then `β bᵢ ≤ w₁ ∨ w₂` by the law of `β` and `h` is
monotone; if `b₁ ∧ b₂ ≤ f wᵢ`, the induction hypothesis applies to `wᵢ`.  This
is where Kostinsky splits on whether some generator lies above `b₁ ∧ b₂`; the
induction needs no split.

```agda
  -- h (β b₁ ∧ β b₂) ≤ h w whenever b₁ ∧ b₂ ≤ f w.
  meet-bound : ∀ w {b₁ b₂} → b₁ ∧ b₂ ≤ ⟦ w ⟧ η → (β b₁ ∧̇ β b₂) [ τ ] ≤ʷ w [ τ ]
  meet-bound (ℊ x) {b₁} {b₂} p =
    ≤→≤ʷ (α-greatest (η x) ((β b₁ ∧̇ β b₂) [ τ ]) (≤-respˡ-≈ (sym (f-β∧ b₁ b₂)) p))
  meet-bound (w₁ ∧̇ w₂) p =
    ≤∧ (meet-bound w₁ (≤-trans p ∧-lowerˡ)) (meet-bound w₂ (≤-trans p ∧-lowerʳ))
  meet-bound (w₁ ∨̇ w₂) {b₁} {b₂} p =
    [ [ (λ q → ∧ˡ≤ ([]-mono τ (≤→≤ʷ (β-least b₁ (w₁ ∨̇ w₂) q))))
      , (λ q → ∧ʳ≤ ([]-mono τ (≤→≤ʷ (β-least b₂ (w₁ ∨̇ w₂) q)))) ]′
    , [ (λ q → ≤∨ˡ (meet-bound w₁ q)) , (λ q → ≤∨ʳ (meet-bound w₂ q)) ]′ ]′
    (W b₁ b₂ (⟦ w₁ ⟧ η) (⟦ w₂ ⟧ η) p)
```

The section `g = h ∘ β`.  It respects equality and preserves joins because `β`
does and `h` is a homomorphism; it preserves meets by monotonicity in one
direction and by the claim, at `w = β (b₁ ∧ b₂)`, in the other; and
`f ∘ g = id` since `f ∘ h = f` and `f ∘ β = id`.

```agda
  -- The section g = h ∘ β.
  g : 𝕌[ proj₁ 𝑳 ] → LatTerm X
  g b = β b [ τ ]

  g-cong : ∀ {b b'} → b ≈ b' → g b ≈ʷ g b'
  g-cong e = []-cong τ (β-cong e)

  g-∨ : ∀ b₁ b₂ → g (b₁ ∨ b₂) ≈ʷ g b₁ ∨̇ g b₂
  g-∨ b₁ b₂ = []-cong τ (β-∨ b₁ b₂)

  g-∧ : ∀ b₁ b₂ → g (b₁ ∧ b₂) ≈ʷ g b₁ ∧̇ g b₂
  g-∧ b₁ b₂ = []-mono τ (≤∧ (≤→≤ʷ (β-mono ∧-lowerˡ)) (≤→≤ʷ (β-mono ∧-lowerʳ)))
            , meet-bound (β (b₁ ∧ b₂)) (β-above (b₁ ∧ b₂))

  private
    g-func : Func 𝔻[ proj₁ 𝑳 ] 𝔻[ proj₁ (FL X) ]
    g-func = record { to = g ; cong = g-cong }

    g-compatible : compatible-map (proj₁ 𝑳) (proj₁ (FL X)) g-func
    g-compatible {∧-Op} {a} =
      ≈ʷ-trans (g-cong (interp-cong (proj₁ 𝑳) ∧-Op λ { 0F → refl ; 1F → refl })) (g-∧ (a 0F) (a 1F))
    g-compatible {∨-Op} {a} =
      ≈ʷ-trans (g-cong (interp-cong (proj₁ 𝑳) ∨-Op λ { 0F → refl ; 1F → refl })) (g-∨ (a 0F) (a 1F))

  -- g is a homomorphism 𝑳 → FL(X).
  g-hom : hom (proj₁ 𝑳) (proj₁ (FL X))
  g-hom = mkhom (proj₁ 𝑳) (proj₁ (FL X)) g-func g-compatible

  -- f ∘ g is the identity.
  g-section : IsSection (FL X) 𝑳 f g-hom
  g-section b = trans (f-τ (β b)) (β-section onto b)
```

Kostinsky's Theorem 3.3 follows: `f` is a retraction, `𝑳`{.AgdaBound} is a
retract of `FL(X)`, hence projective at every choice of levels by Theorem 5.1,
and `g` embeds it in `FL(X)`.

```agda
  -- Theorem 3.3: the bounded epimorphism f has a section.
  hasSection : HasSection (FL X) 𝑳 f
  hasSection = g-hom , g-section

  retractOfFree : 𝑳 IsRetractOf FL X
  retractOfFree = f , hasSection

  projective : IsProjective 𝑳 α₁ ρ₁ α₂ ρ₂
  projective = retractOfFree→projective 𝑳 retractOfFree

  embeds : Embeds 𝑳 (FL X)
  embeds = section→Embeds (FL X) 𝑳 f hasSection
```

#### The easy direction: a sublattice of a free lattice is bounded with (W)

Fix a lattice `𝑳`{.AgdaBound} presented by `η : Fin n → L` with `f` onto, a
set `Y` with decidable equality, and an embedding `e : 𝑳 ↪ FL(Y)`.  The
composite `e ∘ f : FL(n) → FL(Y)` is substitution by `σ x = e (η x)`
(`hom-induced`{.AgdaFunction} of [Lattices.Free.Substitution][]).  For each
`b`, Lemma 3.1 gives a least `a` with `e b ≤ a [ σ ]` or says there is none;
there is one, since `b` has a preimage.  That least `a` is `β b`: `e` reflects
the order, so `b ≤ f a` exactly when `e b ≤ e (f a) = a [ σ ]`.  Dually for
`α`.  (W) holds in `𝑳`{.AgdaBound} as in every sublattice of a free lattice.

```agda
module EasyDirection {n : ℕ} (𝑳 : Lattice αᴸ ρᴸ) (η : Fin n → 𝕌[ proj₁ 𝑳 ])
                     (onto : IsSurjective (FL-extend 𝑳 η))
                     {Y : Type υ} (_≟ʸ_ : DecidableEquality Y) (emb : Embeds 𝑳 (FL Y)) where
  private
    f : hom (proj₁ (FL (Fin n))) (proj₁ 𝑳)
    f = FL-extend-hom 𝑳 η

    e : hom (proj₁ 𝑳) (proj₁ (FL Y))
    e = proj₁ emb

    e′ : 𝕌[ proj₁ 𝑳 ] → LatTerm Y
    e′ b = proj₁ e ⟨$⟩ b

  open Evaluation 𝑳 using ( ⟦_⟧ )

  -- The composite e ∘ f, as a substitution.
  σ : Sub (Fin n) Y
  σ x = e′ (η x)

  e-f : ∀ w → e′ (⟦ w ⟧ η) ≈ʷ w [ σ ]
  e-f = hom-induced (⊙-hom f e)

  private
    -- Every e b lies above, and below, the image of a preimage of b.
    some-above : ∀ b → NoneAbove σ (e′ b) → ⊥
    some-above b none with onto {b}
    ... | Image_∋_.eq w b≈fw = none w (≤ʷ-trans (proj₁ (Func.cong (proj₁ e) b≈fw)) (proj₁ (e-f w)))

    some-below : ∀ b → NoneBelow σ (e′ b) → ⊥
    some-below b none with onto {b}
    ... | Image_∋_.eq w b≈fw = none w (≤ʷ-trans (proj₂ (e-f w)) (proj₂ (Func.cong (proj₁ e) b≈fw)))

    -- The least a with e b ≤ a [ σ ], and the greatest with a [ σ ] ≤ e b.
    least : ∀ b → LeastAbove σ (e′ b)
    least b = [ id , (λ none → ⊥-elim (some-above b none)) ]′ (leastAbove? _≟ʸ_ σ (e′ b))

    greatest : ∀ b → GreatestBelow σ (e′ b)
    greatest b = [ id , (λ none → ⊥-elim (some-below b none)) ]′ (greatestBelow? _≟ʸ_ σ (e′ b))

  -- Note 2.4 with Lemma 3.1: f is lower bounded.
  lowerBounded : LowerBounded (FL (Fin n)) 𝑳 f
  lowerBounded = record
    { β        = λ b → LeastAbove.elt (least b)
    ; β-above  = λ b → hom-reflects-≤ 𝑳 (FL Y) e (proj₂ emb)
                   (≤ʷ→≤ (≤ʷ-trans (LeastAbove.above (least b)) (proj₂ (e-f (LeastAbove.elt (least b))))))
    ; β-least  = λ b w b≤fw → ≤ʷ→≤ (LeastAbove.least (least b) w
                   (≤ʷ-trans (≤→≤ʷ (hom-preserves-≤ 𝑳 (FL Y) e b≤fw)) (proj₁ (e-f w))))
    }

  -- And upper bounded.
  upperBounded : UpperBounded (FL (Fin n)) 𝑳 f
  upperBounded = record
    { α           = λ b → GreatestBelow.elt (greatest b)
    ; α-below     = λ b → hom-reflects-≤ 𝑳 (FL Y) e (proj₂ emb)
                      (≤ʷ→≤ (≤ʷ-trans (proj₁ (e-f (GreatestBelow.elt (greatest b)))) (GreatestBelow.below (greatest b))))
    ; α-greatest  = λ b w fw≤b → ≤ʷ→≤ (GreatestBelow.greatest (greatest b) w
                      (≤ʷ-trans (proj₂ (e-f w)) (≤→≤ʷ (hom-preserves-≤ 𝑳 (FL Y) e fw≤b))))
    }

  bounded : Bounded (FL (Fin n)) 𝑳 f
  bounded = lowerBounded , upperBounded

  -- (W) passes to the sublattice.
  satisfiesW : SatisfiesW 𝑳
  satisfiesW = embeds→SatisfiesW 𝑳 emb
```

#### The theorem, for a lattice presented by `n` generators

With both directions in hand, the equivalences follow for a lattice
`𝑳`{.AgdaBound} presented by `η : Fin n → L` with `f` onto.  Projectivity is
asked at the levels of `FL(n)` and `𝑳`{.AgdaBound}, where Theorem 5.1 (1)
implies (3) applies to `f`, and it comes back at all levels from a section of
`f` by (2) implies (1).  Likewise (3) implies (2) asks for sections only of
epimorphisms from lattices at the levels of `FL(n)`, whatever the levels of
`𝑳`{.AgdaBound} (`sections→retractOfFLn`{.AgdaFunction}).

```agda
module Presentation {n : ℕ} (𝑳 : Lattice αᴸ ρᴸ) (η : Fin n → 𝕌[ proj₁ 𝑳 ])
                    (onto : IsSurjective (FL-extend 𝑳 η)) where
  private
    f : hom (proj₁ (FL (Fin n))) (proj₁ 𝑳)
    f = FL-extend-hom 𝑳 η

  -- Theorem 3.3: if f is bounded and 𝑳 satisfies (W), f has a section.
  bounded×W→hasSection : Bounded (FL (Fin n)) 𝑳 f → SatisfiesW 𝑳 → HasSection (FL (Fin n)) 𝑳 f
  bounded×W→hasSection bd W = HardDirection.hasSection 𝑳 η onto bd W

  -- Corollary 2.16: an embedding in a free lattice with decidable generators makes f bounded,
  -- and 𝑳 satisfies (W).
  embeds→bounded×W : {Y : Type υ} → DecidableEquality Y → Embeds 𝑳 (FL Y)
                   → Bounded (FL (Fin n)) 𝑳 f × SatisfiesW 𝑳
  embeds→bounded×W _≟ʸ_ emb =
    EasyDirection.bounded 𝑳 η onto _≟ʸ_ emb , EasyDirection.satisfiesW 𝑳 η onto _≟ʸ_ emb

  -- A section of f embeds 𝑳 in FL(n).
  hasSection→embeds : HasSection (FL (Fin n)) 𝑳 f → Embeds 𝑳 (FL (Fin n))
  hasSection→embeds = section→Embeds (FL (Fin n)) 𝑳 f

  -- Theorem 3.4: an embedding in any free lattice with decidable generators gives a section
  -- of f, hence an embedding in FL(n) itself.
  embeds→hasSection : {Y : Type υ} → DecidableEquality Y → Embeds 𝑳 (FL Y) → HasSection (FL (Fin n)) 𝑳 f
  embeds→hasSection _≟ʸ_ emb = let (bd , W) = embeds→bounded×W _≟ʸ_ emb in bounded×W→hasSection bd W

  embeds→embedsFLn : {Y : Type υ} → DecidableEquality Y → Embeds 𝑳 (FL Y) → Embeds 𝑳 (FL (Fin n))
  embeds→embedsFLn _≟ʸ_ emb = hasSection→embeds (embeds→hasSection _≟ʸ_ emb)

  -- Theorem 5.1 for f: a section makes 𝑳 projective at every level, and projectivity at the
  -- levels of FL(n) and 𝑳 gives a section.
  hasSection→projective : HasSection (FL (Fin n)) 𝑳 f → IsProjective 𝑳 α₁ ρ₁ α₂ ρ₂
  hasSection→projective hs = retractOfFree→projective 𝑳 (f , hs)

  projective→hasSectionOf : IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ → HasSection (FL (Fin n)) 𝑳 f
  projective→hasSectionOf proj = projective→hasSection 𝑳 proj (FL (Fin n)) f onto

  -- Theorem 5.1 (3) ⇒ (2) for f: sections of the epimorphisms from lattices at the levels of
  -- FL(n) make 𝑳 a retract of FL(n).
  sections→retractOfFLn : ((𝑲 : Lattice 0ℓ 0ℓ) (g : hom (proj₁ 𝑲) (proj₁ 𝑳)) → IsSurjective (proj₁ g)
                           → HasSection 𝑲 𝑳 g)
                        → 𝑳 IsRetractOf FL (Fin n)
  sections→retractOfFLn = sections→retractOfFL 𝑳 f onto

  -- Corollary 5.9: 𝑳 is projective iff f is bounded and 𝑳 satisfies (W).
  projective⇔bounded×W : IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ ⇔ (Bounded (FL (Fin n)) 𝑳 f × SatisfiesW 𝑳)
  projective⇔bounded×W =
    mk⇔ (λ proj → embeds→bounded×W _≟_ (hasSection→embeds (projective→hasSectionOf proj)))
        (λ (bd , W) → hasSection→projective (bounded×W→hasSection bd W))

  -- Corollary 5.10: 𝑳 is projective iff it is a sublattice of FL(n).
  projective⇔embedsFLn : IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ ⇔ Embeds 𝑳 (FL (Fin n))
  projective⇔embedsFLn =
    mk⇔ (λ proj → hasSection→embeds (projective→hasSectionOf proj))
        (λ emb → hasSection→projective (embeds→hasSection _≟_ emb))

  -- Kostinsky's theorem: 𝑳 is a sublattice of FL(n) iff f is bounded and 𝑳 satisfies (W).
  embedsFLn⇔bounded×W : Embeds 𝑳 (FL (Fin n)) ⇔ (Bounded (FL (Fin n)) 𝑳 f × SatisfiesW 𝑳)
  embedsFLn⇔bounded×W =
    mk⇔ (embeds→bounded×W _≟_) (λ (bd , W) → hasSection→embeds (bounded×W→hasSection bd W))

  -- For a finitely generated lattice, projectivity at one choice of levels is projectivity at all.
  projective-levels : IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ → IsProjective 𝑳 α₁ ρ₁ α₂ ρ₂
  projective-levels proj = hasSection→projective (projective→hasSectionOf proj)
```

#### Any epimorphism from `FL(n)`

A homomorphism `f : FL(n) → 𝑳` is the extension of its values on the
generators, up to the equality of `𝑳`{.AgdaBound} (`FL-extend-unique`), and
bounds carry over between homomorphisms with the same values.  So the theorem
holds for every epimorphism `f` from `FL(n)`, in the form the quotients below
need; and so does the proof of Theorem 3.4, which makes a sublattice of any free
lattice `FL(Y)`, `Y` with decidable equality, a sublattice of `FL(n)` itself
(`embeds→embedsFLn`{.AgdaFunction}).

```agda
module _ {n : ℕ} (𝑳 : Lattice αᴸ ρᴸ) (f : hom (proj₁ (FL (Fin n))) (proj₁ 𝑳))
         (onto : IsSurjective (proj₁ f)) where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; refl ; sym ; trans )

  private
    η : Fin n → 𝕌[ proj₁ 𝑳 ]
    η x = proj₁ f ⟨$⟩ ℊ x

    f′ : hom (proj₁ (FL (Fin n))) (proj₁ 𝑳)
    f′ = FL-extend-hom 𝑳 η

    f≈f′ : ∀ w → proj₁ f ⟨$⟩ w ≈ proj₁ f′ ⟨$⟩ w
    f≈f′ = FL-extend-unique 𝑳 η f (λ _ → refl)

    onto′ : IsSurjective (FL-extend 𝑳 η)
    onto′ {b} with onto {b}
    ... | Image_∋_.eq w b≈fw = Image_∋_.eq w (trans b≈fw (f≈f′ w))

    module P = Presentation 𝑳 η onto′

  -- Kostinsky's theorem for any epimorphism f : FL(n) ↠ 𝑳.
  embeds⇔bounded×W : Embeds 𝑳 (FL (Fin n)) ⇔ (Bounded (FL (Fin n)) 𝑳 f × SatisfiesW 𝑳)
  embeds⇔bounded×W =
    mk⇔ (λ emb → let (bd , W) = P.embeds→bounded×W _≟_ emb
                 in Bounded-resp (FL (Fin n)) 𝑳 f′ f (λ w → sym (f≈f′ w)) bd , W)
        (λ (bd , W) → P.hasSection→embeds
                        (P.bounded×W→hasSection (Bounded-resp (FL (Fin n)) 𝑳 f f′ f≈f′ bd) W))

  -- Corollary 5.9 for any epimorphism f : FL(n) ↠ 𝑳.
  projective⇔bounded×W : IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ ⇔ (Bounded (FL (Fin n)) 𝑳 f × SatisfiesW 𝑳)
  projective⇔bounded×W =
    mk⇔ (λ proj → let (bd , W) = P.embeds→bounded×W _≟_ (P.hasSection→embeds (P.projective→hasSectionOf proj))
                  in Bounded-resp (FL (Fin n)) 𝑳 f′ f (λ w → sym (f≈f′ w)) bd , W)
        (λ (bd , W) → P.hasSection→projective
                        (P.bounded×W→hasSection (Bounded-resp (FL (Fin n)) 𝑳 f f′ f≈f′ bd) W))

  -- Theorem 3.4 for any epimorphism f : FL(n) ↠ 𝑳: an embedding in a free lattice with
  -- decidable generators gives one in FL(n).
  embeds→embedsFLn : {Y : Type υ} → DecidableEquality Y → Embeds 𝑳 (FL Y) → Embeds 𝑳 (FL (Fin n))
  embeds→embedsFLn = P.embeds→embedsFLn
```

#### Bounded lattices

In the book's words (Corollary 5.9): a finitely generated lattice is projective
if and only if it is a bounded lattice satisfying (W), with "bounded lattice"
the data of some bounded presentation (`BoundedLattice`{.AgdaFunction} of
[Lattices.Bounded.Homomorphism][]).  Projectivity is produced at every level
and consumed at the levels of the lattice.

```agda
module _ (𝑳 : Lattice αᴸ ρᴸ) where

  -- A bounded lattice satisfying (W) is projective.
  boundedLattice×W→projective : BoundedLattice 𝑳 → SatisfiesW 𝑳 → IsProjective 𝑳 α₁ ρ₁ α₂ ρ₂
  boundedLattice×W→projective (n , η , onto , bd) W =
    Presentation.hasSection→projective 𝑳 η onto (Presentation.bounded×W→hasSection 𝑳 η onto bd W)

  -- A finitely generated projective lattice is bounded and satisfies (W).
  projective→boundedLattice×W : FinitelyGenerated 𝑳 → IsProjective 𝑳 0ℓ 0ℓ αᴸ ρᴸ
                              → BoundedLattice 𝑳 × SatisfiesW 𝑳
  projective→boundedLattice×W (n , η , onto) proj =
    let (bd , W) = P.embeds→bounded×W _≟_ (P.hasSection→embeds (P.projective→hasSectionOf proj))
    in (n , η , onto , bd) , W
    where module P = Presentation 𝑳 η onto
```

#### Quotients of `FL(n)`

Every quotient `FL(n)/ψ` ([Lattices.Quotient][]) is presented by the quotient
map, the identity on terms, which is a homomorphism onto the quotient.  So for
every congruence `ψ`, decidable or not, the quotient embeds in `FL(n)` exactly
when the quotient map is bounded and the quotient satisfies (W); and it embeds
in `FL(n)` as soon as it embeds in some free lattice `FL(Y)` with `Y` decidable
(`quotient-embeds→embedsFLn`{.AgdaFunction}).  This is the form in which the
theorem speaks of the congruences of `FL(n)`.

```agda
module _ {n : ℕ} (ψ : Con (proj₁ (FL (Fin n))) ℓ) where
  private
    𝑸 : Lattice 0ℓ ℓ
    𝑸 = FL (Fin n) ╱ˡ ψ

    ψ-refl : ∀ {s t} → s ≈ʷ t → proj₁ ψ s t
    ψ-refl = IsCongruence.reflexive (proj₂ ψ)

  -- The quotient map: the identity on terms.
  quotient-hom : hom (proj₁ (FL (Fin n))) (proj₁ 𝑸)
  quotient-hom = mkhom (proj₁ (FL (Fin n))) (proj₁ 𝑸) q (ψ-refl ≈ʷ-refl)
    where
    q : Func 𝔻[ proj₁ (FL (Fin n)) ] 𝔻[ proj₁ 𝑸 ]
    q = record { to = id ; cong = ψ-refl }

  quotient-onto : IsSurjective (proj₁ quotient-hom)
  quotient-onto {t} = Image_∋_.eq t (ψ-refl ≈ʷ-refl)

  -- Kostinsky's theorem for a quotient of FL(n), for every congruence ψ.
  quotient-embeds⇔bounded×W : Embeds 𝑸 (FL (Fin n)) ⇔ (Bounded (FL (Fin n)) 𝑸 quotient-hom × SatisfiesW 𝑸)
  quotient-embeds⇔bounded×W = embeds⇔bounded×W 𝑸 quotient-hom quotient-onto

  -- Theorem 3.4 for a quotient of FL(n), for every congruence ψ.
  quotient-embeds→embedsFLn : {Y : Type υ} → DecidableEquality Y → Embeds 𝑸 (FL Y) → Embeds 𝑸 (FL (Fin n))
  quotient-embeds→embedsFLn = embeds→embedsFLn 𝑸 quotient-hom quotient-onto
```

The module checks in about a second of its own.
