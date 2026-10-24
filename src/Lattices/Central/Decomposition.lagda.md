---
layout: default
file: "src/Lattices/Central/Decomposition.lagda.md"
title: "Lattices.Central.Decomposition module"
date: "2026-10-22"
author: "the agda-algebras development team"
---

### Direct decompositions by central elements

This is the [Lattices.Central.Decomposition][] module of the [agda-lattices][] library.

A bounded lattice `L` decomposes as a direct product of two lattices exactly
along its central elements: if `c` is central with complement `c'`, then
`x ↦ (x ∧ c , x ∨ c)` is an isomorphism of `L` with `[0, c] × [c, 1]`, and
conversely if `L ≅ L₁ × L₂` with both factors bounded, the element
corresponding to `(1, 0)` is central ([Grätzer (1998)][], Chapter III,
Theorem 4.1; [Birkhoff (1948)][], Chapter II, Theorem 10 and its corollary).
The two factors are nontrivial exactly when `c` is neither `0` nor `1`.  So
a bounded lattice is directly indecomposable, in the sense of
`IsDirectlyIndecomposable`{.AgdaFunction} of [Lattices.Central][], exactly
when it is nontrivial and has no decomposition into two nontrivial factors;
and for a finite lattice the question is decided there, by a sweep over the
candidates for `c`.

This module proves both directions, over any lattice on a setoid, with the
intervals of [Lattices.Interval][] as the factors and the product of
[Classical.Structures.Lattice.Product][].

+  **Forward** (`Decomposition`{.AgdaModule}).  For `c` neutral with
   `c ∧ c' ≈ ⊥` and `c ∨ c' ≈ ⊤`, the map `φ x = (x ∧ c , x ∨ c)` is a
   homomorphism (`φ-hom`{.AgdaFunction}), because `c` is distributive and
   dually distributive; it is injective (`φ-injective`{.AgdaFunction}),
   because `c` cancels; and it is onto (`φ-surjective`{.AgdaFunction}), with
   `ψ (a , b) = a ∨ (b ∧ c')` as a right inverse, by Grätzer's two
   computations.  `Bijective→≅`{.AgdaFunction} of
   [Setoid.Homomorphisms.Isomorphisms][] then makes it an isomorphism
   (`decomposition`{.AgdaFunction}) without a separate proof that `ψ` is a
   homomorphism.  The three consequences of neutrality that the computations
   use are the lemmas of [Lattices.Central][]; nothing else about `c` is
   needed.
+  **Backward** (`Recomposition`{.AgdaModule}).  In `𝑳₁ ×ˡ 𝑳₂` with bounds,
   `(⊤₁ , ⊥₂)` is central with complement `(⊥₁ , ⊤₂)`
   (`×ˡ-central`{.AgdaFunction} of [Lattices.Central][]), and an isomorphism
   `𝑳 ≅ 𝑳₁ ×ˡ 𝑳₂` carries it to a central element of `𝑳`{.AgdaBound}
   (`centralElement`{.AgdaFunction}), which is not a bottom when
   `𝑳₁`{.AgdaBound} is nontrivial and not a top when `𝑳₂`{.AgdaBound} is;
   so `𝑳`{.AgdaBound} is not directly indecomposable
   (`decomposable`{.AgdaFunction}).

A finite lattice decomposes into directly indecomposable factors in exactly
one way, up to isomorphism and the order of the factors: every lattice is
congruence distributive (Funayama and Nakayama) and has one-element
subalgebras, so Jónsson's theorem applies, or, in the form agda-algebras
formalizes, a finite algebra with the strict refinement property decomposes
in exactly one way (`Setoid.Decompositions.StrictRefinement`, after ALV
Theorem 5.17; that a lattice has the property, through its distributive
congruence lattice, ALV Theorem 5.17, Corollary 1, is not formalized there).
In lattice-theoretic
terms the central elements of a bounded lattice form a Boolean algebra, the
*center* (Birkhoff, Chapter II, Theorem 9; Grätzer, Chapter III, Section 4),
and the decomposition of a finite lattice into indecomposable factors is the
decomposition along the atoms of its center: each atom `c` gives the factor
`[0, c]`, and the rest of the lattice is `[c, 1]`, to be decomposed in turn.
[Lattices.Examples.TwoByThree][] decomposes `2 × 3` with the factor-congruence
theory of `Setoid.Decompositions`; [Lattices.Examples.Central][] decomposes it
again along its central elements, with the decisions of [Lattices.Central][].

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Central.Decomposition where

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Patterns                using ( 0F ; 1F )
open import Data.Product                     using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                    using ( [_,_]′ )
open import Function                         using ( Func )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Nullary.Negation.Core   using ( ¬_ )

import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Operations                  using ( pair )
open import Classical.Properties.Lattice          using ( module Lattice-Order )
open import Classical.Signatures.Lattice          using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret        using ( interp-cong )
open import Classical.Structures.Lattice.Basic    using ( Lattice ; module Lattice-Op )
open import Classical.Structures.Lattice.Product  using ( _×ˡ_ )
open import Setoid.Algebras.Basic                 using ( 𝔻[_] ; 𝕌[_] ; _^_ )
open import Setoid.Congruences.Monolith           using ( Nontrivial )
open import Setoid.Functions                      using ( IsInjective ; IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms.Basic            using ( hom ; mkhom ; compatible-map )
open import Setoid.Homomorphisms.Isomorphisms     using ( _≅_ ; ≅-sym ; Bijective→≅ )

-- Imports from this library --------------------------------------------------------
open import Lattices.Central   using ( IsNeutral ; IsCentral ; ProperCentral ; IsDirectlyIndecomposable
                                     ; neutral-∨-distr ; neutral-∧-distr ; neutral-cancel
                                     ; ∨-absorb-≤ ; ∧-absorb-≤ ; complements-∧ ; complements-∨
                                     ; IsBottom-resp ; IsTop-resp ; IsBottom-I-invar ; IsTop-I-invar
                                     ; IsCentral-I-invar ; ×ˡ-central )
open import Lattices.Interval  using ( _[_,_] ; interval-nontrivial )

open Func renaming ( to to _⟨$⟩_ )
open _≅_

private variable α β γ ρ σ τ : Level
```
-->

#### Forward: a central element decomposes the lattice

Fix a lattice `𝑳`{.AgdaBound} with a bottom `⊥` and a top `⊤`, a neutral
element `c`, and an element `c'` with `c ∧ c' ≈ ⊥` and `c ∨ c' ≈ ⊤`.  The
computations are Grätzer's, in the proof of his Theorem 4.1.

+  `φ (x ∧ y) ≈ φ x ∧ φ y` reads, in the two components,
   `(x ∧ y) ∧ c ≈ (x ∧ c) ∧ (y ∧ c)`, which holds in every lattice, and
   `(x ∧ y) ∨ c ≈ (x ∨ c) ∧ (y ∨ c)`, the distributivity of `c`; and
   `φ (x ∨ y) ≈ φ x ∨ φ y` reads `(x ∨ y) ∧ c ≈ (x ∧ c) ∨ (y ∧ c)`, the dual
   distributivity of `c`, and `(x ∨ y) ∨ c ≈ (x ∨ c) ∨ (y ∨ c)`.
+  `φ x ≈ φ y` says `x ∧ c ≈ y ∧ c` and `x ∨ c ≈ y ∨ c`, so `x ≈ y` because
   `c` cancels.
+  For `a ≤ c ≤ b`, the first component of `φ (a ∨ (b ∧ c'))` is
   `(a ∨ (b ∧ c')) ∧ c ≈ (c ∧ a) ∨ (c ∧ (b ∧ c')) ≈ a ∨ ⊥ ≈ a`, by dual
   distributivity, since `a ≤ c` and `c ∧ (b ∧ c') ≤ c ∧ c' ≈ ⊥`; and the
   second is `(a ∨ (b ∧ c')) ∨ c ≈ c ∨ (b ∧ c') ≈ (c ∨ b) ∧ (c ∨ c') ≈ b ∧ ⊤ ≈ b`,
   by distributivity, since `a ≤ c ≤ b`.

```agda
module _ (𝑳 : Lattice α ρ) where
  open Lattice-Op 𝑳          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-comm-law ; ∨-comm-law ; ∨-assoc-law )
  open Lattice-Order 𝑳       using ( IsBottom ; IsTop ; ≤-trans ; ≤-antisym ; ≤-respʳ-≈ ; ≤-via-∨
                                   ; ∧-lowerˡ ; ∧-lowerʳ ; ∧-greatest ; ∨-upperˡ ; ∨-upperʳ ; ∨-least )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ; refl ; sym ; trans )
  open SetoidReasoning 𝔻[ proj₁ 𝑳 ]

  module Decomposition {⊥ ⊤ : 𝕌[ proj₁ 𝑳 ]} (⊥-bottom : IsBottom ⊥) (⊤-top : IsTop ⊤)
                       {c c' : 𝕌[ proj₁ 𝑳 ]} (c-neutral : IsNeutral 𝑳 c)
                       (c∧c'≈⊥ : c ∧ c' ≈ ⊥) (c∨c'≈⊤ : c ∨ c' ≈ ⊤) where
    private
      P : Lattice (α ⊔ ρ) ρ
      P = 𝑳 [ ⊥ , c ] ×ˡ 𝑳 [ c , ⊤ ]

      open Setoid 𝔻[ proj₁ P ]  using () renaming ( _≈_ to _≈ₓ_ ; sym to symₓ ; trans to transₓ )
      open Lattice-Op P         using () renaming ( _∧_ to _∧ₓ_ ; _∨_ to _∨ₓ_ )

    -- The map x ↦ (x ∧ c , x ∨ c), with the proofs that place its components.
    φ : 𝕌[ proj₁ 𝑳 ] → 𝕌[ proj₁ P ]
    φ x = (x ∧ c , ⊥-bottom (x ∧ c) , ∧-lowerʳ) , (x ∨ c , ∨-upperʳ , ⊤-top (x ∨ c))

    φ-cong : ∀ {x y} → x ≈ y → φ x ≈ₓ φ y
    φ-cong e = ∧-cong e refl , ∨-cong e refl

    -- φ commutes with meets: a lattice identity, and the distributivity of c.
    φ-∧ : ∀ x y → φ (x ∧ y) ≈ₓ φ x ∧ₓ φ y
    φ-∧ x y = ∧∧ , (begin
      (x ∧ y) ∨ c          ≈⟨ ∨-comm-law ⟩
      c ∨ (x ∧ y)          ≈⟨ neutral-∨-distr 𝑳 c-neutral x y ⟩
      (c ∨ x) ∧ (c ∨ y)    ≈⟨ ∧-cong ∨-comm-law ∨-comm-law ⟩
      (x ∨ c) ∧ (y ∨ c)    ∎)
      where
      ∧∧ : (x ∧ y) ∧ c ≈ (x ∧ c) ∧ (y ∧ c)
      ∧∧ = ≤-antisym
        (∧-greatest (∧-greatest (≤-trans ∧-lowerˡ ∧-lowerˡ) ∧-lowerʳ) (∧-greatest (≤-trans ∧-lowerˡ ∧-lowerʳ) ∧-lowerʳ))
        (∧-greatest (∧-greatest (≤-trans ∧-lowerˡ ∧-lowerˡ) (≤-trans ∧-lowerʳ ∧-lowerˡ)) (≤-trans ∧-lowerˡ ∧-lowerʳ))

    -- φ commutes with joins: the dual distributivity of c, and a lattice identity.
    φ-∨ : ∀ x y → φ (x ∨ y) ≈ₓ φ x ∨ₓ φ y
    φ-∨ x y = (begin
      (x ∨ y) ∧ c          ≈⟨ ∧-comm-law ⟩
      c ∧ (x ∨ y)          ≈⟨ neutral-∧-distr 𝑳 c-neutral x y ⟩
      (c ∧ x) ∨ (c ∧ y)    ≈⟨ ∨-cong ∧-comm-law ∧-comm-law ⟩
      (x ∧ c) ∨ (y ∧ c)    ∎) , ∨∨
      where
      ∨∨ : (x ∨ y) ∨ c ≈ (x ∨ c) ∨ (y ∨ c)
      ∨∨ = ≤-antisym
        (∨-least (∨-least (≤-trans ∨-upperˡ ∨-upperˡ) (≤-trans ∨-upperˡ ∨-upperʳ)) (≤-trans ∨-upperʳ ∨-upperˡ))
        (∨-least (∨-least (≤-trans ∨-upperˡ ∨-upperˡ) ∨-upperʳ) (∨-least (≤-trans ∨-upperʳ ∨-upperˡ) ∨-upperʳ))

    φ-hom : hom (proj₁ 𝑳) (proj₁ P)
    φ-hom = mkhom (proj₁ 𝑳) (proj₁ P) φ-map compatible
      where
      φ-map : Func 𝔻[ proj₁ 𝑳 ] 𝔻[ proj₁ P ]
      φ-map = record { to = φ ; cong = φ-cong }

      compatible : compatible-map (proj₁ 𝑳) (proj₁ P) φ-map
      -- The interpretation of a symbol at an argument tuple is the curried operation at its entries.
      interp-∧ : ∀ a → (∧-Op ^ proj₁ 𝑳) a ≈ a 0F ∧ a 1F
      interp-∧ a = interp-cong (proj₁ 𝑳) ∧-Op {a} {pair (a 0F) (a 1F)} λ { 0F → refl ; 1F → refl }

      interp-∨ : ∀ a → (∨-Op ^ proj₁ 𝑳) a ≈ a 0F ∨ a 1F
      interp-∨ a = interp-cong (proj₁ 𝑳) ∨-Op {a} {pair (a 0F) (a 1F)} λ { 0F → refl ; 1F → refl }

      compatible {∧-Op} {a} =
        transₓ {φ ((∧-Op ^ proj₁ 𝑳) a)} {φ (a 0F ∧ a 1F)} {φ (a 0F) ∧ₓ φ (a 1F)}
               (φ-cong {(∧-Op ^ proj₁ 𝑳) a} {a 0F ∧ a 1F} (interp-∧ a)) (φ-∧ (a 0F) (a 1F))
      compatible {∨-Op} {a} =
        transₓ {φ ((∨-Op ^ proj₁ 𝑳) a)} {φ (a 0F ∨ a 1F)} {φ (a 0F) ∨ₓ φ (a 1F)}
               (φ-cong {(∨-Op ^ proj₁ 𝑳) a} {a 0F ∨ a 1F} (interp-∨ a)) (φ-∨ (a 0F) (a 1F))

    -- φ is injective, because c cancels.
    φ-injective : IsInjective (proj₁ φ-hom)
    φ-injective (e₁ , e₂) =
      neutral-cancel 𝑳 c-neutral (trans ∧-comm-law (trans e₁ ∧-comm-law)) (trans ∨-comm-law (trans e₂ ∨-comm-law))

    -- The right inverse (a , b) ↦ a ∨ (b ∧ c').
    ψ : 𝕌[ proj₁ P ] → 𝕌[ proj₁ 𝑳 ]
    ψ (a , b) = proj₁ a ∨ (proj₁ b ∧ c')

    φ∘ψ : ∀ p → φ (ψ p) ≈ₓ p
    φ∘ψ ((a , _ , a≤c) , (b , c≤b , _)) = first , second
      where
      c∧b∧c'≈⊥ : c ∧ (b ∧ c') ≈ ⊥
      c∧b∧c'≈⊥ = ≤-antisym (≤-respʳ-≈ c∧c'≈⊥ (∧-greatest ∧-lowerˡ (≤-trans ∧-lowerʳ ∧-lowerʳ))) (⊥-bottom _)

      first : (a ∨ (b ∧ c')) ∧ c ≈ a
      first = begin
        (a ∨ (b ∧ c')) ∧ c          ≈⟨ ∧-comm-law ⟩
        c ∧ (a ∨ (b ∧ c'))          ≈⟨ neutral-∧-distr 𝑳 c-neutral a (b ∧ c') ⟩
        (c ∧ a) ∨ (c ∧ (b ∧ c'))    ≈⟨ ∨-cong (∧-absorb-≤ 𝑳 a≤c) c∧b∧c'≈⊥ ⟩
        a ∨ ⊥                       ≈⟨ ∨-absorb-≤ 𝑳 (⊥-bottom a) ⟩
        a                           ∎

      second : (a ∨ (b ∧ c')) ∨ c ≈ b
      second = begin
        (a ∨ (b ∧ c')) ∨ c     ≈⟨ ∨-comm-law ⟩
        c ∨ (a ∨ (b ∧ c'))     ≈˘⟨ ∨-assoc-law ⟩
        (c ∨ a) ∨ (b ∧ c')     ≈⟨ ∨-cong (∨-absorb-≤ 𝑳 a≤c) refl ⟩
        c ∨ (b ∧ c')           ≈⟨ neutral-∨-distr 𝑳 c-neutral b c' ⟩
        (c ∨ b) ∧ (c ∨ c')     ≈⟨ ∧-cong (≤-via-∨ c≤b) c∨c'≈⊤ ⟩
        b ∧ ⊤                  ≈⟨ ⊤-top b ⟩
        b                      ∎

    φ-surjective : IsSurjective (proj₁ φ-hom)
    φ-surjective {p} = Image_∋_.eq (ψ p) (symₓ {φ (ψ p)} {p} (φ∘ψ p))

    -- The decomposition: 𝑳 ≅ [⊥, c] × [c, ⊤].
    decomposition : proj₁ 𝑳 ≅ proj₁ (𝑳 [ ⊥ , c ] ×ˡ 𝑳 [ c , ⊤ ])
    decomposition = Bijective→≅ φ-hom φ-injective φ-surjective

    -- Both factors are nontrivial when c is neither the bottom nor the top.
    factors-nontrivial : ¬ IsBottom c → ¬ IsTop c
      → Nontrivial (proj₁ (𝑳 [ ⊥ , c ])) × Nontrivial (proj₁ (𝑳 [ c , ⊤ ]))
    factors-nontrivial ¬bottom ¬top =
        interval-nontrivial 𝑳 ⊥ c (⊥-bottom c) (λ ⊥≈c → ¬bottom (IsBottom-resp 𝑳 ⊥≈c ⊥-bottom))
      , interval-nontrivial 𝑳 c ⊤ (⊤-top c) (λ c≈⊤ → ¬top (IsTop-resp 𝑳 (sym c≈⊤) ⊤-top))
```

A central element, in the bound-free sense of [Lattices.Central][], gives the
same decomposition against any bounds: its complement meets it in `⊥` and
joins it in `⊤` by the uniqueness of bounds.

```agda
  module _ {⊥ ⊤ : 𝕌[ proj₁ 𝑳 ]} (⊥-bottom : IsBottom ⊥) (⊤-top : IsTop ⊤) where

    central-decomposition : ∀ {c} → IsCentral 𝑳 c → proj₁ 𝑳 ≅ proj₁ (𝑳 [ ⊥ , c ] ×ˡ 𝑳 [ c , ⊤ ])
    central-decomposition (c-neutral , c' , comp) =
      Decomposition.decomposition ⊥-bottom ⊤-top c-neutral
        (complements-∧ 𝑳 ⊥-bottom ⊤-top comp) (complements-∨ 𝑳 ⊥-bottom ⊤-top comp)
```

#### Backward: a decomposition gives a central element

Fix an isomorphism `φ : 𝑳 ≅ 𝑳₁ ×ˡ 𝑳₂` and bounds of both factors.  The
central element of `𝑳`{.AgdaBound} is the preimage of `(⊤₁ , ⊥₂)`.  If it
were a bottom of `𝑳`{.AgdaBound}, its image `(⊤₁ , ⊥₂)` would be a bottom of
the product, so `⊤₁ ≤ ⊥₁` and `𝑳₁`{.AgdaBound} would be trivial; dually for a
top and `𝑳₂`{.AgdaBound}.

```agda
module _ (𝑳 : Lattice α ρ) (𝑳₁ : Lattice β σ) (𝑳₂ : Lattice γ τ) (φ : proj₁ 𝑳 ≅ proj₁ (𝑳₁ ×ˡ 𝑳₂)) where
  open Lattice-Order 𝑳   using ( IsBottom ; IsTop )
  open Lattice-Order 𝑳₁  using () renaming ( IsBottom to IsBottom₁ ; IsTop to IsTop₁ ; ≤-antisym to ≤-antisym₁ )
  open Lattice-Order 𝑳₂  using () renaming ( IsBottom to IsBottom₂ ; IsTop to IsTop₂ ; ≤-antisym to ≤-antisym₂ )
  open Setoid 𝔻[ proj₁ 𝑳₁ ]  using () renaming ( _≈_ to _≈₁_ )
  open Setoid 𝔻[ proj₁ 𝑳₂ ]  using () renaming ( _≈_ to _≈₂_ )

  module Recomposition {⊥₁ ⊤₁ : 𝕌[ proj₁ 𝑳₁ ]} {⊥₂ ⊤₂ : 𝕌[ proj₁ 𝑳₂ ]}
                       (⊥₁-bottom : IsBottom₁ ⊥₁) (⊤₁-top : IsTop₁ ⊤₁)
                       (⊥₂-bottom : IsBottom₂ ⊥₂) (⊤₂-top : IsTop₂ ⊤₂) where

    -- The element of 𝑳 that corresponds to (⊤₁ , ⊥₂).
    centralElement : 𝕌[ proj₁ 𝑳 ]
    centralElement = proj₁ (from φ) ⟨$⟩ (⊤₁ , ⊥₂)

    centralElement-central : IsCentral 𝑳 centralElement
    centralElement-central =
      IsCentral-I-invar (𝑳₁ ×ˡ 𝑳₂) 𝑳 (≅-sym φ) (×ˡ-central 𝑳₁ 𝑳₂ ⊥₁-bottom ⊤₁-top ⊥₂-bottom ⊤₂-top)

    -- It is not a bottom when 𝑳₁ is nontrivial, nor a top when 𝑳₂ is.
    centralElement-not-bottom : ¬ (⊥₁ ≈₁ ⊤₁) → ¬ IsBottom centralElement
    centralElement-not-bottom ⊥₁≉⊤₁ b = ⊥₁≉⊤₁ (≤-antisym₁ (⊥₁-bottom ⊤₁) (proj₁ (bₓ (⊥₁ , ⊥₂))))
      where
      bₓ : Lattice-Order.IsBottom (𝑳₁ ×ˡ 𝑳₂) (⊤₁ , ⊥₂)
      bₓ = IsBottom-resp (𝑳₁ ×ˡ 𝑳₂) (to∼from φ (⊤₁ , ⊥₂)) (IsBottom-I-invar 𝑳 (𝑳₁ ×ˡ 𝑳₂) φ b)

    centralElement-not-top : ¬ (⊥₂ ≈₂ ⊤₂) → ¬ IsTop centralElement
    centralElement-not-top ⊥₂≉⊤₂ t = ⊥₂≉⊤₂ (≤-antisym₂ (⊥₂-bottom ⊤₂) (proj₂ (tₓ (⊤₁ , ⊤₂))))
      where
      tₓ : Lattice-Order.IsTop (𝑳₁ ×ˡ 𝑳₂) (⊤₁ , ⊥₂)
      tₓ = IsTop-resp (𝑳₁ ×ˡ 𝑳₂) (to∼from φ (⊤₁ , ⊥₂)) (IsTop-I-invar 𝑳 (𝑳₁ ×ˡ 𝑳₂) φ t)

    -- With both factors nontrivial, a proper central element.
    properCentralElement : ¬ (⊥₁ ≈₁ ⊤₁) → ¬ (⊥₂ ≈₂ ⊤₂) → ProperCentral 𝑳
    properCentralElement ⊥₁≉⊤₁ ⊥₂≉⊤₂ =
      centralElement , centralElement-central , centralElement-not-bottom ⊥₁≉⊤₁ , centralElement-not-top ⊥₂≉⊤₂

    -- A product of two nontrivial bounded lattices is not directly indecomposable.
    decomposable : ¬ (⊥₁ ≈₁ ⊤₁) → ¬ (⊥₂ ≈₂ ⊤₂) → ¬ IsDirectlyIndecomposable 𝑳
    decomposable ⊥₁≉⊤₁ ⊥₂≉⊤₂ (_ , bounds) =
      [ centralElement-not-bottom ⊥₁≉⊤₁ , centralElement-not-top ⊥₂≉⊤₂ ]′ (bounds centralElement centralElement-central)
```

--------------------------------------

[Lattices.Central.Decomposition]: Lattices.Central.Decomposition.html
[Lattices.Central]: Lattices.Central.html
[Lattices.Interval]: Lattices.Interval.html
[Lattices.Examples.Central]: Lattices.Examples.Central.html
[Lattices.Examples.TwoByThree]: Lattices.Examples.TwoByThree.html
[Classical.Structures.Lattice.Product]: Classical.Structures.Lattice.Product.html
[Setoid.Homomorphisms.Isomorphisms]: Setoid.Homomorphisms.Isomorphisms.html
[Birkhoff (1948)]: https://bookstore.ams.org/coll-25
[Grätzer (1998)]: https://doi.org/10.1007/978-3-0348-7633-9
