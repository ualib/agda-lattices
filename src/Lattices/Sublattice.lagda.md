---
layout: default
file: "src/Lattices/Sublattice.lagda.md"
title: "Lattices.Sublattice module"
date: "2026-10-28"
author: "the agda-algebras development team"
---

### Sublattices carried by subuniverses, and ranges of embeddings

This is the [Lattices.Sublattice][] module of the [agda-lattices][] library.

agda-algebras says that `𝑨` is a subalgebra of `𝑴` when there is an injective
homomorphism from `𝑨` into `𝑴` ([Setoid.Subalgebras.Basic][]), and it calls a
subset of the carrier of `𝑴` that is closed under the operations a
*subuniverse* (`Subuniverses`{.AgdaFunction} of
[Setoid.Subalgebras.Subuniverses][]).  The two meet in this module, for
lattices.  A subuniverse `U` of a lattice `𝑴` carries a lattice, the
*sublattice* `sublattice 𝑴 U closed`{.AgdaFunction}, whose members are the
elements of `U`, equal when they are equal in `𝑴`, with the meet and the join
of `𝑴`; and its inclusion in `𝑴` is an embedding
(`sublatticeSub`{.AgdaFunction}).  The range of a homomorphism is a subuniverse
(`range-subuniverse`{.AgdaFunction}), and an embedding is an isomorphism onto
any subuniverse that is its range (`corestriction-≅`{.AgdaFunction}), so the
two notions of sublattice agree up to isomorphism.  Finally, an embedding whose
range lies in the range of another embedding factors through it
(`factor-hom`{.AgdaFunction}, `factor-commutes`{.AgdaFunction}), by an
embedding when the first map is one (`factor-embedding`{.AgdaFunction}): the
factor sends `a` to the preimage, under the second map, of the image of `a`
under the first.

An interval of a lattice ([Lattices.Interval][]) is the sublattice carried by
a particular subuniverse, built there directly.  Every fact here except the
lattice laws of the sublattice holds for algebras of any signature, with the
same proofs; the module states them for the lattices of this library, where
they are used.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Sublattice where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Patterns                using ( 0F ; 1F )
open import Data.Product                     using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Function                         using ( Func )
open import Level                            using ( Level ; _⊔_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Unary                   using ( Pred ; _∈_ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Operations                using ( pair )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Interpret      using ( interp-cong )
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op ; setoidEqsToLattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] ; _^_ )
open import Setoid.Functions                    using ( IsInjective ; IsSurjective ; IsInRange
                                                      ; IsInRange→IsInImage )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map ; IsHom )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; Bijective→≅ )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )
open import Setoid.Subalgebras.Subuniverses     using ( Subuniverses )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρᵃ β ρ γ ρᶜ ℓ : Level
```
-->

#### The sublattice carried by a subuniverse

A subuniverse `U` of `𝑴`{.AgdaBound} contains the meet and the join of any two
of its members (`∧-closed`{.AgdaFunction}, `∨-closed`{.AgdaFunction}): they are
the operations of `𝑴`{.AgdaBound} applied to the pair of them.  A member of the
sublattice is an element with a proof that it lies in `U`, and two members are
equal when their elements are, so the proofs never matter to equality.  The
eight lattice equations hold because they hold in `𝑴`{.AgdaBound} on the
elements, and `setoidEqsToLattice`{.AgdaFunction} of
[Classical.Structures.Lattice.Basic][] accepts the proofs of `𝑴`{.AgdaBound}
unchanged.  The first projection is a homomorphism into `𝑴`{.AgdaBound}
(`sublatticeHom`{.AgdaFunction}), injective by the definition of the
sublattice's equality (`sublatticeSub`{.AgdaFunction}).

```agda
module _ (𝑴 : Lattice β ρ) where
  open Lattice-Op 𝑴          using ( _∧_ ; _∨_ ; ∧-cong ; ∨-cong ; ∧-assoc-law ; ∧-comm-law ; ∧-idem-law
                                   ; ∨-assoc-law ; ∨-comm-law ; ∨-idem-law ; absorbˡ-law ; absorbʳ-law )
  open Setoid 𝔻[ proj₁ 𝑴 ]   using ( _≈_ ; refl ; sym ; trans )

  module _ (U : Pred 𝕌[ proj₁ 𝑴 ] ℓ) (closed : U ∈ Subuniverses (proj₁ 𝑴)) where

    -- A subuniverse contains the meet and the join of two of its members.
    ∧-closed : {x y : 𝕌[ proj₁ 𝑴 ]} → x ∈ U → y ∈ U → x ∧ y ∈ U
    ∧-closed {x} {y} xU yU = closed ∧-Op (pair x y) λ { 0F → xU ; 1F → yU }

    ∨-closed : {x y : 𝕌[ proj₁ 𝑴 ]} → x ∈ U → y ∈ U → x ∨ y ∈ U
    ∨-closed {x} {y} xU yU = closed ∨-Op (pair x y) λ { 0F → xU ; 1F → yU }

    -- The elements of U, with their proofs.
    Member : Type (β ⊔ ℓ)
    Member = Σ[ x ∈ 𝕌[ proj₁ 𝑴 ] ] x ∈ U

    -- Two members are equal when their elements are.
    sublatticeSetoid : Setoid (β ⊔ ℓ) ρ
    sublatticeSetoid = record
      { Carrier        = Member
      ; _≈_            = λ p q → proj₁ p ≈ proj₁ q
      ; isEquivalence  = record { refl = refl ; sym = sym ; trans = trans }
      }

    infixl 7 _∧ˢ_ _∨ˢ_

    -- The meet and join of 𝑴, which stay in U.
    _∧ˢ_ _∨ˢ_ : Member → Member → Member
    p ∧ˢ q = proj₁ p ∧ proj₁ q , ∧-closed (proj₂ p) (proj₂ q)
    p ∨ˢ q = proj₁ p ∨ proj₁ q , ∨-closed (proj₂ p) (proj₂ q)

    -- The sublattice carried by U: the laws of 𝑴, read on the elements.
    sublattice : Lattice (β ⊔ ℓ) ρ
    sublattice = setoidEqsToLattice sublatticeSetoid _∧ˢ_ _∨ˢ_
      (λ {p} {q} {u} {v} → ∧-cong {proj₁ p} {proj₁ q} {proj₁ u} {proj₁ v})
      (λ {p} {q} {u} {v} → ∨-cong {proj₁ p} {proj₁ q} {proj₁ u} {proj₁ v})
      ∧-assoc-law ∧-comm-law ∧-idem-law ∨-assoc-law ∨-comm-law ∨-idem-law absorbˡ-law absorbʳ-law

    -- The inclusion of the sublattice in 𝑴.
    sublatticeHom : hom (proj₁ sublattice) (proj₁ 𝑴)
    sublatticeHom = mkhom (proj₁ sublattice) (proj₁ 𝑴) incl compatible
      where
      incl : Func sublatticeSetoid 𝔻[ proj₁ 𝑴 ]
      incl = record { to = proj₁ ; cong = λ e → e }

      compatible : compatible-map (proj₁ sublattice) (proj₁ 𝑴) incl
      compatible {∧-Op} {a} = interp-cong (proj₁ 𝑴) ∧-Op λ { 0F → refl ; 1F → refl }
      compatible {∨-Op} {a} = interp-cong (proj₁ 𝑴) ∨-Op λ { 0F → refl ; 1F → refl }

    -- The sublattice is a subalgebra of 𝑴.
    sublatticeSub : proj₁ sublattice IsSubalgebraOf proj₁ 𝑴
    sublatticeSub = sublatticeHom , λ e → e
```

#### Ranges

The range of a homomorphism `h` into `𝑴`{.AgdaBound} is a subuniverse: if each
argument of an operation is the image of some element, the result is the image
of the operation applied to those elements, since `h` commutes with it.

```agda
  module _ (𝑨 : Lattice α ρᵃ) (h : hom (proj₁ 𝑨) (proj₁ 𝑴)) where

    -- The range of a homomorphism is a subuniverse.
    range-subuniverse : IsInRange (proj₁ h) ∈ Subuniverses (proj₁ 𝑴)
    range-subuniverse f t t∈ =
      (f ^ proj₁ 𝑨) (λ i → proj₁ (t∈ i))
      , trans (IsHom.compatible (proj₂ h)) (interp-cong (proj₁ 𝑴) f λ i → proj₂ (t∈ i))
```

#### An embedding is an isomorphism onto its range

Let `h` be an embedding of `𝑨`{.AgdaBound} in `𝑴`{.AgdaBound} whose values lie
in a subuniverse `U`.  Then `h` is a homomorphism into the sublattice carried
by `U` (`corestriction`{.AgdaFunction}), injective as `h` is, and if every
member of `U` is a value of `h`, it is surjective too, hence an isomorphism
(`corestriction-≅`{.AgdaFunction}), by `Bijective→≅`{.AgdaFunction} of
[Setoid.Homomorphisms.Isomorphisms][].

```agda
  module _ (U : Pred 𝕌[ proj₁ 𝑴 ] ℓ) (closed : U ∈ Subuniverses (proj₁ 𝑴))
           (𝑨 : Lattice α ρᵃ) (h : proj₁ 𝑨 IsSubalgebraOf proj₁ 𝑴)
           (into : (a : 𝕌[ proj₁ 𝑨 ]) → proj₁ (proj₁ h) ⟨$⟩ a ∈ U) where

    -- An embedding with its values in U, as a homomorphism into the sublattice.
    corestriction : hom (proj₁ 𝑨) (proj₁ (sublattice U closed))
    corestriction = mkhom (proj₁ 𝑨) (proj₁ (sublattice U closed)) cor compatible
      where
      cor : Func 𝔻[ proj₁ 𝑨 ] (sublatticeSetoid U closed)
      cor = record { to = λ a → proj₁ (proj₁ h) ⟨$⟩ a , into a ; cong = cong (proj₁ (proj₁ h)) }

      compatible : compatible-map (proj₁ 𝑨) (proj₁ (sublattice U closed)) cor
      compatible {∧-Op} {t} =
        trans (IsHom.compatible (proj₂ (proj₁ h))) (interp-cong (proj₁ 𝑴) ∧-Op λ { 0F → refl ; 1F → refl })
      compatible {∨-Op} {t} =
        trans (IsHom.compatible (proj₂ (proj₁ h))) (interp-cong (proj₁ 𝑴) ∨-Op λ { 0F → refl ; 1F → refl })

    -- The corestriction is injective.
    corestriction-injective : IsInjective (proj₁ corestriction)
    corestriction-injective = proj₂ h

    module _ (onto : {y : 𝕌[ proj₁ 𝑴 ]} → y ∈ U → IsInRange (proj₁ (proj₁ h)) y) where

      -- If every member of U is a value of h, the corestriction is surjective.
      corestriction-surjective : IsSurjective (proj₁ corestriction)
      corestriction-surjective {y , yU} = IsInRange→IsInImage (onto yU)

      -- An embedding is an isomorphism onto a sublattice that is its range.
      corestriction-≅ : proj₁ 𝑨 ≅ proj₁ (sublattice U closed)
      corestriction-≅ = Bijective→≅ corestriction corestriction-injective corestriction-surjective
```

#### Factoring through an embedding

Let `g` embed `𝑩`{.AgdaBound} in `𝑴`{.AgdaBound}, and let `h` be a homomorphism
from `𝑨`{.AgdaBound} into `𝑴`{.AgdaBound} whose range lies in the range of
`g`.  The factor (`factor-map`{.AgdaFunction}) sends `a` to the element of
`𝑩`{.AgdaBound} that `g` sends to `h a`, which the containment of ranges
supplies, so `g` after the factor is `h` (`factor-commutes`{.AgdaFunction}).
Everything else about the factor follows from that equation and the
injectivity of `g`: it respects equality and commutes with the operations,
since `g` turns each such equation into one that holds because `h` and `g`
commute with the operations, so it is a homomorphism
(`factor-hom`{.AgdaFunction}); and it is injective when `h` is
(`factor-injective`{.AgdaFunction}), since `g` after it is `h`.

```agda
  module _ (𝑨 : Lattice α ρᵃ) (𝑩 : Lattice γ ρᶜ)
           (g : proj₁ 𝑩 IsSubalgebraOf proj₁ 𝑴) (h : hom (proj₁ 𝑨) (proj₁ 𝑴))
           (range⊆ : {y : 𝕌[ proj₁ 𝑴 ]} → IsInRange (proj₁ h) y → IsInRange (proj₁ (proj₁ g)) y) where
    open Setoid 𝔻[ proj₁ 𝑨 ]  using () renaming ( _≈_ to _≈ᴬ_ )
    open Setoid 𝔻[ proj₁ 𝑩 ]  using () renaming ( _≈_ to _≈ᴮ_ )

    -- The factor: the preimage under g of the image under h.
    factor-map : 𝕌[ proj₁ 𝑨 ] → 𝕌[ proj₁ 𝑩 ]
    factor-map a = proj₁ (range⊆ (a , refl))

    -- g after the factor is h.
    factor-commutes : (a : 𝕌[ proj₁ 𝑨 ]) → proj₁ (proj₁ g) ⟨$⟩ factor-map a ≈ proj₁ h ⟨$⟩ a
    factor-commutes a = proj₂ (range⊆ (a , refl))

    -- The factor respects equality.
    factor-cong : {a a′ : 𝕌[ proj₁ 𝑨 ]} → a ≈ᴬ a′ → factor-map a ≈ᴮ factor-map a′
    factor-cong {a} {a′} e =
      proj₂ g (trans (factor-commutes a) (trans (cong (proj₁ h) e) (sym (factor-commutes a′))))

    -- The factor as a setoid map.
    factor-func : Func 𝔻[ proj₁ 𝑨 ] 𝔻[ proj₁ 𝑩 ]
    factor-func = record { to = factor-map ; cong = factor-cong }

    -- The factor commutes with the operations.
    factor-compatible : compatible-map (proj₁ 𝑨) (proj₁ 𝑩) factor-func
    factor-compatible {f} {t} = proj₂ g
      (trans (factor-commutes ((f ^ proj₁ 𝑨) t))
      (trans (IsHom.compatible (proj₂ h))
      (trans (interp-cong (proj₁ 𝑴) f λ i → sym (factor-commutes (t i)))
             (sym (IsHom.compatible (proj₂ (proj₁ g)))))))

    -- The factor is a homomorphism.
    factor-hom : hom (proj₁ 𝑨) (proj₁ 𝑩)
    factor-hom = mkhom (proj₁ 𝑨) (proj₁ 𝑩) factor-func factor-compatible

    -- The factor of an injective map is injective.
    factor-injective : IsInjective (proj₁ h) → IsInjective factor-func
    factor-injective inj {a} {a′} e =
      inj (trans (sym (factor-commutes a)) (trans (cong (proj₁ (proj₁ g)) e) (factor-commutes a′)))

    -- The factor of an embedding is an embedding.
    factor-embedding : IsInjective (proj₁ h) → proj₁ 𝑨 IsSubalgebraOf proj₁ 𝑩
    factor-embedding inj = factor-hom , factor-injective inj
```

--------------------------------------

[Lattices.Sublattice]: Lattices.Sublattice.html
[Lattices.Interval]: Lattices.Interval.html
[Classical.Structures.Lattice.Basic]: Classical.Structures.Lattice.Basic.html
[Setoid.Subalgebras.Basic]: Setoid.Subalgebras.Basic.html
[Setoid.Subalgebras.Subuniverses]: Setoid.Subalgebras.Subuniverses.html
[Setoid.Homomorphisms.Isomorphisms]: Setoid.Homomorphisms.Isomorphisms.html
