---
layout: default
file: "src/Lattices/Projective.lagda.md"
title: "Lattices.Projective module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Projective lattices

This is the [Lattices.Projective][] module of the [agda-lattices][] library.

A lattice `L` is *projective* if for every epimorphism `f : M ↠ N` and every
homomorphism `h : L → N` there is a homomorphism `g : L → M` with `f ∘ g = h`
([Freese, Ježek, and Nation (1995)][], Section V.1, p. 95; in the category of
lattices the epimorphisms are the onto homomorphisms).  A homomorphism
`f : K → L` is a *retraction* if it has a homomorphic *section* `g : L → K`,
`f ∘ g = id`, and `L` is a *retract* of `K` if some homomorphism `K → L` is a
retraction.  Theorem 5.1 of the book says that the following are equivalent for
a lattice `L`: (1) `L` is projective; (2) `L` is a retract of a free lattice;
(3) every epimorphism onto `L` is a retraction.  Corollary 5.2 adds that a
projective lattice is a sublattice of a free lattice, since a section is
injective.  This module proves the three implications and the corollary, at
explicit universe levels, for the lattices of the Setoid tree.

The three statements quantify over lattices, so they carry universe levels.
`IsProjective 𝑳 β ρᵇ γ ρᶜ`{.AgdaFunction} speaks of epimorphisms from lattices
at levels `β ρᵇ` onto lattices at levels `γ ρᶜ`.  Being a retract of a free
lattice `FL X`{.AgdaFunction} gives projectivity at *every* choice of levels
(`retractOfFree→projective`{.AgdaFunction}), which is the implication the rest
of the library uses: a finitely generated lattice that is a retract of
`FL (Fin n)`{.AgdaFunction} is projective in the strongest sense.  Conversely,
projectivity at the levels of `𝑳`{.AgdaBound} itself makes every epimorphism
onto `𝑳`{.AgdaBound} a retraction (`projective→hasSection`{.AgdaFunction}),
and that in turn, for any epimorphism from a free lattice `FL X` onto
`𝑳`{.AgdaBound}, makes `𝑳`{.AgdaBound} a retract of `FL X`
(`sections→retractOfFL`{.AgdaFunction}).  Only sources at the levels of
`FL X` are asked for, so a lattice presented by `n` generators needs them only
at the lowest level; the free lattice on the carrier of `𝑳`{.AgdaBound}
presents every lattice, at the level of its carrier
(`sections→retractOfFree`{.AgdaFunction}).

Kostinsky's theorem ([Lattices.Kostinsky][]) characterizes the finitely
generated projective lattices as the bounded lattices satisfying (W); this
module is the elementary part of that characterization.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Projective where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Product                           using ( Σ-syntax ; _,_ ; proj₁ )
open import Function                               using ( Func ; id )
open import Level                                  using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary                        using ( Setoid )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsSurjective ; IsInjective ; Image_∋_
                                                      ; SurjInv ; SurjInvIsInverseʳ )
open import Setoid.Homomorphisms.Basic          using ( hom ; 𝒾𝒹 )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Term       using ( LatTerm ; ℊ )
open import Lattices.Free.Universal  using ( FL ; FL-extend-hom ; FL-extend-unique )
open import Lattices.Nation          using ( Embeds )

open Func using ( cong ) renaming ( to to _⟨$⟩_ )

private variable α ρ β ρᵇ γ ρᶜ χ : Level
```
-->

#### Sections and retracts

Fix lattices `𝑲`{.AgdaBound} and `𝑳`{.AgdaBound}.  A homomorphism
`g : L → K` is a *section* of `f : K → L` when `f ∘ g` is the identity up to the
equality of `𝑳`{.AgdaBound} (`IsSection`{.AgdaFunction}); `f` is a retraction
when it has one (`HasSection`{.AgdaFunction}); and `𝑳`{.AgdaBound} is a
retract of `𝑲`{.AgdaBound} when some homomorphism `K → L` has one
(`_IsRetractOf_`{.AgdaFunction}).  A section is injective, since `g a ≈ g b`
gives `a ≈ f (g a) ≈ f (g b) ≈ b`, so a retract of `𝑲`{.AgdaBound} embeds in
`𝑲`{.AgdaBound} in the sense of [Lattices.Nation][]
(`section→Embeds`{.AgdaFunction}, `retractOf→Embeds`{.AgdaFunction}).

```agda
module _ (𝑲 : Lattice β ρᵇ) (𝑳 : Lattice α ρ) where
  open Setoid 𝔻[ proj₁ 𝑳 ]  using ( _≈_ ; sym ; trans )

  -- g is a section of f: f ∘ g is the identity on 𝑳.
  IsSection : hom (proj₁ 𝑲) (proj₁ 𝑳) → hom (proj₁ 𝑳) (proj₁ 𝑲) → Type (α ⊔ ρ)
  IsSection f g = ∀ a → proj₁ f ⟨$⟩ (proj₁ g ⟨$⟩ a) ≈ a

  -- f is a retraction: it has a homomorphic section.
  HasSection : hom (proj₁ 𝑲) (proj₁ 𝑳) → Type (α ⊔ ρ ⊔ β ⊔ ρᵇ)
  HasSection f = Σ[ g ∈ hom (proj₁ 𝑳) (proj₁ 𝑲) ] IsSection f g

  -- A section is injective.
  section-injective : (f : hom (proj₁ 𝑲) (proj₁ 𝑳)) (g : hom (proj₁ 𝑳) (proj₁ 𝑲))
                    → IsSection f g → IsInjective (proj₁ g)
  section-injective f g sec {a} {b} ga≈gb =
    trans (sym (sec a)) (trans (cong (proj₁ f) ga≈gb) (sec b))

  -- A section embeds 𝑳 in 𝑲.
  section→Embeds : (f : hom (proj₁ 𝑲) (proj₁ 𝑳)) → HasSection f → Embeds 𝑳 𝑲
  section→Embeds f (g , sec) = g , section-injective f g sec

-- 𝑳 is a retract of 𝑲: some homomorphism 𝑲 → 𝑳 has a section.
infix 4 _IsRetractOf_

_IsRetractOf_ : Lattice α ρ → Lattice β ρᵇ → Type (α ⊔ ρ ⊔ β ⊔ ρᵇ)
𝑳 IsRetractOf 𝑲 = Σ[ f ∈ hom (proj₁ 𝑲) (proj₁ 𝑳) ] HasSection 𝑲 𝑳 f

-- A retract of 𝑲 embeds in 𝑲.
retractOf→Embeds : (𝑳 : Lattice α ρ) (𝑲 : Lattice β ρᵇ) → 𝑳 IsRetractOf 𝑲 → Embeds 𝑳 𝑲
retractOf→Embeds 𝑳 𝑲 (f , hs) = section→Embeds 𝑲 𝑳 f hs
```

#### Projective lattices

`g : L → M` *lifts* `h : L → N` along `f : M → N` when `f ∘ g = h`
(`Lifts`{.AgdaFunction}), and `IsProjective 𝑳 β ρᵇ γ ρᶜ`{.AgdaFunction} is the
book's definition, for epimorphisms `f : M ↠ N` with `𝑴`{.AgdaBound} at levels
`β ρᵇ` and `𝑵`{.AgdaBound} at levels `γ ρᶜ`: every homomorphism `h : L → N`
has a lift along `f`.  Surjectivity is agda-algebras'
`IsSurjective`{.AgdaFunction}, which exhibits a preimage of each element.

```agda
module _ (𝑳 : Lattice α ρ) (𝑴 : Lattice β ρᵇ) (𝑵 : Lattice γ ρᶜ) where
  open Setoid 𝔻[ proj₁ 𝑵 ]  using ( _≈_ )

  -- g lifts h along f: f ∘ g is h.
  Lifts : hom (proj₁ 𝑴) (proj₁ 𝑵) → hom (proj₁ 𝑳) (proj₁ 𝑵) → hom (proj₁ 𝑳) (proj₁ 𝑴) → Type (α ⊔ ρᶜ)
  Lifts f h g = ∀ a → proj₁ f ⟨$⟩ (proj₁ g ⟨$⟩ a) ≈ proj₁ h ⟨$⟩ a

-- 𝑳 is projective: every homomorphism into the target of an epimorphism lifts along it.
IsProjective : Lattice α ρ → (β ρᵇ γ ρᶜ : Level) → Type (α ⊔ ρ ⊔ lsuc (β ⊔ ρᵇ ⊔ γ ⊔ ρᶜ))
IsProjective 𝑳 β ρᵇ γ ρᶜ =
  (𝑴 : Lattice β ρᵇ) (𝑵 : Lattice γ ρᶜ) (f : hom (proj₁ 𝑴) (proj₁ 𝑵)) → IsSurjective (proj₁ f)
  → (h : hom (proj₁ 𝑳) (proj₁ 𝑵)) → Σ[ g ∈ hom (proj₁ 𝑳) (proj₁ 𝑴) ] Lifts 𝑳 𝑴 𝑵 f h g
```

#### Theorem 5.1, (1) implies (3)

A projective lattice makes every epimorphism onto it a retraction: lift the
identity of `𝑳`{.AgdaBound} along the epimorphism.  Projectivity is needed
for targets at the levels of `𝑳`{.AgdaBound} itself and sources at the levels
of the epimorphism's domain.

```agda
module _ (𝑳 : Lattice α ρ) where

  -- (1) ⇒ (3): every epimorphism onto a projective lattice has a section.
  projective→hasSection : IsProjective 𝑳 β ρᵇ α ρ
                        → (𝑲 : Lattice β ρᵇ) (f : hom (proj₁ 𝑲) (proj₁ 𝑳)) → IsSurjective (proj₁ f)
                        → HasSection 𝑲 𝑳 f
  projective→hasSection proj 𝑲 f onto = proj 𝑲 𝑳 f onto 𝒾𝒹
```

#### Theorem 5.1, (3) implies (2)

If every epimorphism onto `𝑳`{.AgdaBound} is a retraction, then so is any
epimorphism `f : FL X ↠ L`, and `𝑳`{.AgdaBound} is a retract of `FL X`
(`sections→retractOfFL`{.AgdaFunction}).  The hypothesis is used once, for
the source `FL X`, so it is asked only at the levels of `FL X`.  Every lattice
is a homomorphic image of a free lattice: the free lattice on the carrier of
`𝑳`{.AgdaBound}, by the homomorphism that sends each generator to itself,
which is onto since the generator `ℊ a` evaluates to `a`.  With it,
`𝑳`{.AgdaBound} is a retract of `FL 𝕌[ 𝑳 ]` when the hypothesis holds at the
level of the carrier (`sections→retractOfFree`{.AgdaFunction}).

```agda
  -- (3) ⇒ (2): if every epimorphism onto 𝑳 from a lattice at the levels of FL X has a
  -- section, 𝑳 is a retract of FL X, for any free lattice FL X that maps onto 𝑳.
  sections→retractOfFL : {X : Type χ} (f : hom (proj₁ (FL X)) (proj₁ 𝑳)) → IsSurjective (proj₁ f)
                       → ((𝑲 : Lattice χ χ) (g : hom (proj₁ 𝑲) (proj₁ 𝑳)) → IsSurjective (proj₁ g)
                          → HasSection 𝑲 𝑳 g)
                       → 𝑳 IsRetractOf FL X
  sections→retractOfFL {X = X} f onto sections = f , sections (FL X) f onto

  -- The free lattice on the carrier of 𝑳 maps onto 𝑳.
  carrier-hom : hom (proj₁ (FL 𝕌[ proj₁ 𝑳 ])) (proj₁ 𝑳)
  carrier-hom = FL-extend-hom 𝑳 id

  carrier-onto : IsSurjective (proj₁ carrier-hom)
  carrier-onto {a} = Image_∋_.eq (ℊ a) refl
    where open Setoid 𝔻[ proj₁ 𝑳 ] using ( refl )

  -- (3) ⇒ (2) through the free lattice on the carrier of 𝑳.
  sections→retractOfFree : ((𝑲 : Lattice α α) (f : hom (proj₁ 𝑲) (proj₁ 𝑳)) → IsSurjective (proj₁ f)
                            → HasSection 𝑲 𝑳 f)
                         → 𝑳 IsRetractOf FL 𝕌[ proj₁ 𝑳 ]
  sections→retractOfFree = sections→retractOfFL carrier-hom carrier-onto
```

#### Theorem 5.1, (2) implies (1)

Let `f₀ : FL X ↠ L` have the section `g₀`, and let `f : M ↠ N` and `h : L → N`
be given.  For each generator `x` choose a preimage `h₀ x` under `f` of
`h (f₀ (ℊ x))`, which surjectivity supplies (`SurjInv`{.AgdaFunction} of
[Setoid.Functions.Surjective][]), and extend `h₀` to a homomorphism
`H : FL X → M`.  Then `f ∘ H` and `h ∘ f₀` are two homomorphisms `FL X → N` that
agree on the generators, so they agree everywhere, by the uniqueness half of
the universal property (`FL-extend-unique`{.AgdaFunction}); and
`g = H ∘ g₀ : L → M` satisfies `f ∘ g = h ∘ f₀ ∘ g₀ = h`.  Nothing restricts the
levels of `𝑴`{.AgdaBound} and `𝑵`{.AgdaBound}, so a retract of a free lattice
is projective at every choice of levels.

```agda
  module _ {X : Type χ} (f₀ : hom (proj₁ (FL X)) (proj₁ 𝑳)) (g₀ : hom (proj₁ 𝑳) (proj₁ (FL X)))
           (sec : IsSection (FL X) 𝑳 f₀ g₀)
           (𝑴 : Lattice β ρᵇ) (𝑵 : Lattice γ ρᶜ) (f : hom (proj₁ 𝑴) (proj₁ 𝑵))
           (onto : IsSurjective (proj₁ f)) (h : hom (proj₁ 𝑳) (proj₁ 𝑵)) where
    open Setoid 𝔻[ proj₁ 𝑵 ]  using ( _≈_ ; refl ; sym ; trans )

    private
      -- The values the lift must take on the generators.
      target : X → 𝕌[ proj₁ 𝑵 ]
      target x = proj₁ h ⟨$⟩ (proj₁ f₀ ⟨$⟩ ℊ x)

      -- A preimage under f of each target value.
      h₀ : X → 𝕌[ proj₁ 𝑴 ]
      h₀ x = SurjInv (proj₁ f) onto (target x)

      h₀-lifts : ∀ x → proj₁ f ⟨$⟩ h₀ x ≈ target x
      h₀-lifts x = SurjInvIsInverseʳ (proj₁ f) onto

      -- The extension of h₀ to the free lattice.
      H : hom (proj₁ (FL X)) (proj₁ 𝑴)
      H = FL-extend-hom 𝑴 h₀

      -- f ∘ H and h ∘ f₀ agree on the generators, hence everywhere.
      agree : (t : LatTerm X) → proj₁ f ⟨$⟩ (proj₁ H ⟨$⟩ t) ≈ proj₁ h ⟨$⟩ (proj₁ f₀ ⟨$⟩ t)
      agree t = trans (FL-extend-unique 𝑵 target (⊙-hom H f) h₀-lifts t)
                      (sym (FL-extend-unique 𝑵 target (⊙-hom f₀ h) (λ _ → refl) t))

    -- The lift of h along f.
    lift : hom (proj₁ 𝑳) (proj₁ 𝑴)
    lift = ⊙-hom g₀ H

    lift-factors : Lifts 𝑳 𝑴 𝑵 f h lift
    lift-factors a = trans (agree (proj₁ g₀ ⟨$⟩ a)) (cong (proj₁ h) (sec a))

  -- (2) ⇒ (1): a retract of a free lattice is projective, at every choice of levels.
  retractOfFree→projective : {X : Type χ} → 𝑳 IsRetractOf FL X → IsProjective 𝑳 β ρᵇ γ ρᶜ
  retractOfFree→projective (f₀ , g₀ , sec) 𝑴 𝑵 f onto h =
    lift f₀ g₀ sec 𝑴 𝑵 f onto h , lift-factors f₀ g₀ sec 𝑴 𝑵 f onto h
```

#### Corollary 5.2

A projective lattice is a sublattice of a free lattice: by (1) implies (3) any
epimorphism `f : FL X ↠ L` has a section, which is an embedding
(`projective→EmbedsFL`{.AgdaFunction}).  The levels asked of projectivity are
those of `FL X` and of `𝑳`{.AgdaBound}; with the free lattice on the carrier,
which always maps onto `𝑳`{.AgdaBound}, they are the levels of the carrier and
of `𝑳`{.AgdaBound} (`projective→Embeds`{.AgdaFunction}).

```agda
  -- Corollary 5.2: a projective lattice embeds in any free lattice that maps onto it.
  projective→EmbedsFL : {X : Type χ} (f : hom (proj₁ (FL X)) (proj₁ 𝑳)) → IsSurjective (proj₁ f)
                      → IsProjective 𝑳 χ χ α ρ → Embeds 𝑳 (FL X)
  projective→EmbedsFL {X = X} f onto proj =
    section→Embeds (FL X) 𝑳 f (projective→hasSection proj (FL X) f onto)

  -- In particular, in the free lattice on its carrier.
  projective→Embeds : IsProjective 𝑳 α α α ρ → Embeds 𝑳 (FL 𝕌[ proj₁ 𝑳 ])
  projective→Embeds = projective→EmbedsFL carrier-hom carrier-onto
```

The module checks in well under a second of its own.
