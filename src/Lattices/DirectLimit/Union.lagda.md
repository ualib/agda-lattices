---
layout: default
file: "src/Lattices/DirectLimit/Union.lagda.md"
title: "Lattices.DirectLimit.Union module"
date: "2026-10-28"
author: "the agda-algebras development team"
---

### Unions of chains of sublattices as direct limits

This is the [Lattices.DirectLimit.Union][] module of the [agda-lattices][]
library.

The union of an ascending chain `S₀ ⊆ S₁ ⊆ ⋯` of sublattices of a lattice `M`
is a sublattice of `M`, and it is the direct limit of the inclusions
`Sₖ → Sₖ₊₁`: the inclusions of the links in `M` form a cocone, the
homomorphism it induces on the limit ([Lattices.DirectLimit][]) is injective
because each inclusion is, and its range is the union, so the limit is
isomorphic to the union ([Lattices.Sublattice][],
`corestriction-≅`{.AgdaFunction}).
The module proves this in three forms, as follows:

+  for a chain of subuniverses `S k` of `𝑴`{.AgdaBound}, each contained in
   the next: the union `chainUnion`{.AgdaFunction} is isomorphic to the direct
   limit `chainLimit`{.AgdaFunction} of the inclusions of the links
   (`chainUnion≅chainLimit`{.AgdaFunction});
+  for any cocone of embeddings `f k` of a sequence into `𝑴`{.AgdaBound}: the
   union of their ranges, `rangeUnion`{.AgdaFunction}, is isomorphic to the
   direct limit (`rangeUnion≅limit`{.AgdaFunction});
+  for a chain given by embeddings `φ k` of lattices `𝑳 k` into `𝑴`{.AgdaBound}
   whose ranges ascend: each `φ k` factors through `φ (suc k)` by an embedding
   `step k`{.AgdaFunction} (`step-commutes`{.AgdaFunction}), and the union of
   the ranges, `rangeChainUnion`{.AgdaFunction}, is isomorphic to the direct
   limit of the steps (`rangeChainUnion≅stepLimit`{.AgdaFunction}), which
   embeds in `𝑴`{.AgdaBound} (`stepLimit-embedding`{.AgdaFunction}).

In the third form the links are lattices in their own right, each identified
with its copy in `𝑴`{.AgdaBound} by its embedding, and `step k` is the
inclusion of the `k`-th copy in the next read through those identifications.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.DirectLimit.Union where

-- Imports from the Agda Standard Library -----------------------------------------
open import Data.Fin.Base                    using ( Fin )
open import Data.Fin.Patterns                using ( 0F ; 1F )
open import Data.Nat.Base                    using ( ℕ ; suc ; _⊔_ ; _≤′_ ; ≤′-step ; ≤′-refl )
open import Data.Product                     using ( Σ-syntax ; _,_ ; proj₁ ; proj₂ )
open import Function                         using ( Func )
open import Level                            using ( Level ) renaming ( _⊔_ to _⊔ˡ_ )
open import Relation.Binary                  using ( Setoid )
open import Relation.Unary                   using ( Pred ; _∈_ ; _⊆_ ; ⋃ )

-- Imports from the Agda Universal Algebra Library --------------------------------
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Lattice.Basic  using ( Lattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsInjective ; IsInRange )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map )
open import Setoid.Homomorphisms.Isomorphisms   using ( _≅_ ; ≅-sym )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )
open import Setoid.Subalgebras.Subuniverses     using ( Subuniverses )

open import Lattices.DirectLimit                using ( DirectLimit ; Staged ; Cocone ; ≤′-⊔ˡ ; ≤′-⊔ʳ
                                                      ; limit-extend-embedding )
open import Lattices.Sublattice                 using ( sublattice ; sublatticeSetoid ; sublatticeHom
                                                      ; range-subuniverse ; corestriction-≅
                                                      ; factor-hom ; factor-commutes ; factor-injective )

open Func renaming ( to to _⟨$⟩_ )

private variable α ρ β ρᵇ ℓ : Level
```
-->

#### Chains of sublattices

Fix a lattice `𝑴`{.AgdaBound} and a sequence `S`{.AgdaBound} of subuniverses
of it, each contained in the next, and so in every later one
(`ascends*`{.AgdaFunction}).  The `k`-th link is the sublattice carried by
`S k` (`link`{.AgdaFunction}), and the inclusion of each link in the next keeps
the element and moves its proof of membership up the chain
(`link-inclusion`{.AgdaFunction}).  The union `⋃ ℕ S` is a subuniverse
(`chainUnion-closed`{.AgdaFunction}): the two arguments of a meet or a join lie
in some `S k` and `S m`, so both lie in `S (k ⊔ m)`, which contains the
result.

```agda
module _ (𝑴 : Lattice β ρ) (S : ℕ → Pred 𝕌[ proj₁ 𝑴 ] ℓ)
         (closed : (k : ℕ) → S k ∈ Subuniverses (proj₁ 𝑴))
         (ascends : (k : ℕ) → S k ⊆ S (suc k)) where
  open Setoid 𝔻[ proj₁ 𝑴 ]  using ( refl )

  -- Each set of the chain is contained in every later one.
  ascends* : {k n : ℕ} → k ≤′ n → S k ⊆ S n
  ascends* ≤′-refl          s = s
  ascends* (≤′-step {n} p)  s = ascends n (ascends* p s)

  -- The links of the chain, as lattices.
  link : ℕ → Lattice (β ⊔ˡ ℓ) ρ
  link k = sublattice 𝑴 (S k) (closed k)

  -- The inclusion of each link in the next.
  link-inclusion : (k : ℕ) → hom (proj₁ (link k)) (proj₁ (link (suc k)))
  link-inclusion k = mkhom (proj₁ (link k)) (proj₁ (link (suc k))) incl (λ {f} {a} → compatible {f} {a})
    where
    incl : Func (sublatticeSetoid 𝑴 (S k) (closed k)) (sublatticeSetoid 𝑴 (S (suc k)) (closed (suc k)))
    incl = record { to = λ p → proj₁ p , ascends k (proj₂ p) ; cong = λ e → e }

    compatible : compatible-map (proj₁ (link k)) (proj₁ (link (suc k))) incl
    compatible {∧-Op} = refl
    compatible {∨-Op} = refl

  -- Each inclusion is injective.
  link-inclusion-injective : (k : ℕ) → IsInjective (proj₁ (link-inclusion k))
  link-inclusion-injective k e = e

  private
    -- Two members of the union lie in one set of the chain.
    common : (t : Fin 2 → 𝕌[ proj₁ 𝑴 ]) → ((i : Fin 2) → t i ∈ ⋃ ℕ S)
      → Σ[ n ∈ ℕ ] ((i : Fin 2) → t i ∈ S n)
    common t t∈ = k ⊔ m , λ { 0F → ascends* (≤′-⊔ˡ k m) (proj₂ (t∈ 0F))
                            ; 1F → ascends* (≤′-⊔ʳ k m) (proj₂ (t∈ 1F)) }
      where
      k m : ℕ
      k = proj₁ (t∈ 0F)
      m = proj₁ (t∈ 1F)

  -- The union of the chain is a subuniverse.
  chainUnion-closed : ⋃ ℕ S ∈ Subuniverses (proj₁ 𝑴)
  chainUnion-closed ∧-Op t t∈ = proj₁ (common t t∈) , closed (proj₁ (common t t∈)) ∧-Op t (proj₂ (common t t∈))
  chainUnion-closed ∨-Op t t∈ = proj₁ (common t t∈) , closed (proj₁ (common t t∈)) ∨-Op t (proj₂ (common t t∈))
```

The union is the sublattice it carries (`chainUnion`{.AgdaFunction}), and the
direct limit of the links is `chainLimit`{.AgdaFunction}.  The inclusions of the
links in `𝑴`{.AgdaBound} form a cocone, definitionally, since the inclusion of a
link in the next keeps the element; each is injective, so the cocone extends to
an embedding of the limit in `𝑴`{.AgdaBound}
(`chainLimit-embedding`{.AgdaFunction}), which sends `(k , x)` to the element
of `x`.  Its values lie in the union, and every member of the union is one,
which is the isomorphism (`chainUnion≅chainLimit`{.AgdaFunction}).

```agda
  -- The union of the chain, as a sublattice of 𝑴.
  chainUnion : Lattice (β ⊔ˡ ℓ) ρ
  chainUnion = sublattice 𝑴 (⋃ ℕ S) chainUnion-closed

  -- The direct limit of the inclusions of the links.
  chainLimit : Lattice (β ⊔ˡ ℓ) ρ
  chainLimit = DirectLimit link link-inclusion

  -- The inclusions of the links in 𝑴.
  link-in : (k : ℕ) → hom (proj₁ (link k)) (proj₁ 𝑴)
  link-in k = sublatticeHom 𝑴 (S k) (closed k)

  -- They form a cocone.
  link-in-cocone : Cocone link link-inclusion 𝑴 link-in
  link-in-cocone k x = refl

  -- The limit of the inclusions embeds in 𝑴.
  chainLimit-embedding : proj₁ chainLimit IsSubalgebraOf proj₁ 𝑴
  chainLimit-embedding = limit-extend-embedding link link-inclusion 𝑴 link-in link-in-cocone (λ k e → e)

  -- The union of the chain is the direct limit of the inclusions.
  chainUnion≅chainLimit : proj₁ chainUnion ≅ proj₁ chainLimit
  chainUnion≅chainLimit = ≅-sym (corestriction-≅ 𝑴 (⋃ ℕ S) chainUnion-closed chainLimit chainLimit-embedding into onto)
    where
    into : (a : Staged link link-inclusion) → proj₁ (proj₁ chainLimit-embedding) ⟨$⟩ a ∈ ⋃ ℕ S
    into (k , x) = k , proj₂ x

    onto : {y : 𝕌[ proj₁ 𝑴 ]} → y ∈ ⋃ ℕ S → IsInRange (proj₁ (proj₁ chainLimit-embedding)) y
    onto {y} (k , s) = (k , (y , s)) , refl
```

#### Cocones of embeddings

Now let `𝑳`{.AgdaBound} and `θ`{.AgdaBound} be any sequence of lattices and
homomorphisms, and `f` a cocone of embeddings over it into `𝑴`{.AgdaBound}.
The union of the ranges of the `f k` (`rangeUnion`{.AgdaFunction}) is the range
of the embedding of the limit that `f` induces, up to the grouping of the
witnesses, so it is a subuniverse (`rangeUnion-closed`{.AgdaFunction}) and the
limit is isomorphic to it (`rangeUnion≅limit`{.AgdaFunction}).  Nothing is
asked of the `θ`{.AgdaBound}: they are injective because `f (suc k) ∘ θ k` is
`f k`, which is.

```agda
module _ (𝑳 : ℕ → Lattice α ρ) (θ : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ (𝑳 (suc k))))
         (𝑴 : Lattice β ρᵇ) (f : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ 𝑴)) (cocone : Cocone 𝑳 θ 𝑴 f)
         (f-injective : (k : ℕ) → IsInjective (proj₁ (f k))) where
  open Setoid 𝔻[ proj₁ 𝑴 ]  using ( refl )

  -- The range of each map of the cocone.
  coconeRange : ℕ → Pred 𝕌[ proj₁ 𝑴 ] (α ⊔ˡ ρᵇ)
  coconeRange k = IsInRange (proj₁ (f k))

  private
    -- The embedding of the limit that the cocone induces.
    extend : proj₁ (DirectLimit 𝑳 θ) IsSubalgebraOf proj₁ 𝑴
    extend = limit-extend-embedding 𝑳 θ 𝑴 f cocone f-injective

    -- A value of the induced map lies in the range of one map of the cocone, and conversely.
    regroup : {y : 𝕌[ proj₁ 𝑴 ]} → IsInRange (proj₁ (proj₁ extend)) y → y ∈ ⋃ ℕ coconeRange
    regroup ((k , x) , e) = k , x , e

    ungroup : {y : 𝕌[ proj₁ 𝑴 ]} → y ∈ ⋃ ℕ coconeRange → IsInRange (proj₁ (proj₁ extend)) y
    ungroup (k , x , e) = (k , x) , e

  -- The union of the ranges is a subuniverse.
  rangeUnion-closed : ⋃ ℕ coconeRange ∈ Subuniverses (proj₁ 𝑴)
  rangeUnion-closed g t t∈ =
    regroup (range-subuniverse 𝑴 (DirectLimit 𝑳 θ) (proj₁ extend) g t λ i → ungroup (t∈ i))

  -- The union of the ranges, as a sublattice of 𝑴.
  rangeUnion : Lattice (β ⊔ˡ α ⊔ˡ ρᵇ) ρᵇ
  rangeUnion = sublattice 𝑴 (⋃ ℕ coconeRange) rangeUnion-closed

  -- The union of the ranges of a cocone of embeddings is the direct limit.
  rangeUnion≅limit : proj₁ rangeUnion ≅ proj₁ (DirectLimit 𝑳 θ)
  rangeUnion≅limit = ≅-sym (corestriction-≅ 𝑴 (⋃ ℕ coconeRange) rangeUnion-closed (DirectLimit 𝑳 θ) extend into ungroup)
    where
    into : (a : Staged 𝑳 θ) → proj₁ (proj₁ extend) ⟨$⟩ a ∈ ⋃ ℕ coconeRange
    into (k , x) = k , x , refl
```

#### Chains of embeddings

Finally, let `φ k` embed `𝑳 k` in `𝑴`{.AgdaBound} for each `k`, with each
range contained in the next.  Then `φ k` factors through `φ (suc k)`
([Lattices.Sublattice][], `factor-hom`{.AgdaFunction}): `step k`{.AgdaFunction}
sends `x` to the element of `𝑳 (suc k)` that `φ (suc k)` sends to `φ k x`.  So
`φ (suc k) ∘ step k` is `φ k` (`step-commutes`{.AgdaFunction}), each step is an
embedding (`step-injective`{.AgdaFunction}), the `φ k` form a cocone of
embeddings over the steps, so the direct limit of the steps embeds in
`𝑴`{.AgdaBound} (`stepLimit-embedding`{.AgdaFunction}), and the union of the
ranges (`rangeChainUnion`{.AgdaFunction}) is isomorphic to it
(`rangeChainUnion≅stepLimit`{.AgdaFunction}).

```agda
module _ (𝑳 : ℕ → Lattice α ρ) (𝑴 : Lattice β ρᵇ)
         (φ : (k : ℕ) → proj₁ (𝑳 k) IsSubalgebraOf proj₁ 𝑴)
         (ascends : (k : ℕ) → IsInRange (proj₁ (proj₁ (φ k))) ⊆ IsInRange (proj₁ (proj₁ (φ (suc k))))) where

  -- Each embedding factors through the next.
  step : (k : ℕ) → hom (proj₁ (𝑳 k)) (proj₁ (𝑳 (suc k)))
  step k = factor-hom 𝑴 (𝑳 k) (𝑳 (suc k)) (φ (suc k)) (proj₁ (φ k)) (ascends k)

  -- The next embedding after the step is the embedding.
  step-commutes : Cocone 𝑳 step 𝑴 (λ k → proj₁ (φ k))
  step-commutes k = factor-commutes 𝑴 (𝑳 k) (𝑳 (suc k)) (φ (suc k)) (proj₁ (φ k)) (ascends k)

  -- Each step is injective.
  step-injective : (k : ℕ) → IsInjective (proj₁ (step k))
  step-injective k = factor-injective 𝑴 (𝑳 k) (𝑳 (suc k)) (φ (suc k)) (proj₁ (φ k)) (ascends k) (proj₂ (φ k))

  -- The direct limit of the steps.
  stepLimit : Lattice α ρ
  stepLimit = DirectLimit 𝑳 step

  -- The direct limit of the steps embeds in 𝑴.
  stepLimit-embedding : proj₁ stepLimit IsSubalgebraOf proj₁ 𝑴
  stepLimit-embedding = limit-extend-embedding 𝑳 step 𝑴 (λ k → proj₁ (φ k)) step-commutes (λ k → proj₂ (φ k))

  -- The union of the ranges of the chain, as a sublattice of 𝑴.
  rangeChainUnion : Lattice (β ⊔ˡ α ⊔ˡ ρᵇ) ρᵇ
  rangeChainUnion = rangeUnion 𝑳 step 𝑴 (λ k → proj₁ (φ k)) step-commutes (λ k → proj₂ (φ k))

  -- The union of the ranges of the chain is the direct limit of the steps.
  rangeChainUnion≅stepLimit : proj₁ rangeChainUnion ≅ proj₁ stepLimit
  rangeChainUnion≅stepLimit = rangeUnion≅limit 𝑳 step 𝑴 (λ k → proj₁ (φ k)) step-commutes (λ k → proj₂ (φ k))
```

--------------------------------------

[Lattices.DirectLimit.Union]: Lattices.DirectLimit.Union.html
[Lattices.DirectLimit]: Lattices.DirectLimit.html
[Lattices.Sublattice]: Lattices.Sublattice.html
