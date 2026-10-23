---
layout: default
file: "src/Lattices/Bounded/Sublattice.lagda.md"
title: "Lattices.Bounded.Sublattice module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Corollaries 2.15 and 2.16: a finitely generated sublattice of a free lattice has `D(L) = L`

This is the [Lattices.Bounded.Sublattice][] module of the [agda-lattices][] library.

[Freese, Ježek, and Nation (1995)][], Corollary 2.15 (p. 34): if `e : S → L`
embeds a finitely generated lattice into a lower bounded lattice, then
`u ∈ D_k(L)` implies `β_e(u) ∈ D_k(S)` for every `u` below the image of the top
of `S`, so `D(S) = S`.  Corollary 2.16 applies it with `L` a free lattice, where
`D(FL(X)) = FL(X)` by Corollary 2.11: every finitely generated sublattice of a
free lattice has `D(L) = L`, and dually `Dᵈ(L) = L`.  This module proves both,
for a lattice `𝑳`{.AgdaBound} presented by `η : Fin n → L` and embedded by
`e` in `FL(Y)`, `Y` with decidable equality.  It completes the comparison of the
two readings of "bounded": for a lattice with a decided order, the data of a
bounded presentation ([Lattices.Bounded.Homomorphism][]) and the book's
`D(L) = L = Dᵈ(L)` ([Lattices.Bounded.Covers][]) are equivalent in the presence
of (W), since each is equivalent to being a sublattice of `FL(n)`
(`embedsFLn⇔D×Dᵈ×W`{.AgdaFunction}, with [Lattices.Kostinsky][] and
[Lattices.Bounded.Preimage][]).

The least preimage `β_e(u)` of an element `u` of `FL(Y)` below some image
is the value under `f : FL(n) → L` of the least term `a` with `u ≤ a [ σ ]`,
where `σ` is the substitution `e ∘ f` and the least `a` comes from Kostinsky's
Lemma 3.1 ([Lattices.Free.Bounded][]).  Corollary 2.15's induction then runs on
`k`: for `u ∈ D_k(FL(Y))` below an image, a nontrivial join cover `S` of
`β_e(u)` in `𝑳`{.AgdaBound} has `e(S)` a nontrivial join cover of `u`, which
refines to a cover `T` inside `D_{k-1}(FL(Y))`; each `t ∈ T` lies below some
`e(s)`, so `β_e(t)` is defined, lies in `D_{k-1}(L)` by induction and below
`s`; and `β_e(u)` lies below the join of the `β_e(t)`, since `u` lies below the
join of `T`, which lies below the image of the join of the least terms.  For
`u = e(b)` the least preimage is `b` itself.  The dual statement is the same
theorem for the dual lattice, embedded in `FL(Y)` by the dual of `e`.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Bounded.Sublattice where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Empty                             using ( ⊥-elim )
open import Data.Fin.Base                          using ( Fin ; suc )
open import Data.Fin.Patterns                      using ( 0F ; 1F )
open import Data.Fin.Properties                    using ( _≟_ )
open import Data.List.Base                         using ( List ; [] ; _∷_ ; map )
open import Data.List.Membership.Propositional     using ( _∈_ ; find ; lose )
open import Data.List.Membership.Propositional.Properties
                                                   using ( ∈-map⁻ )
open import Data.List.Relation.Unary.All           using ( All ; [] ; _∷_ )
open import Data.List.Relation.Unary.All.Properties using ( map⁺ )
open import Data.List.Relation.Unary.Any           using ( Any ; here ; there )
open import Data.Nat.Base                          using ( ℕ ; zero ; suc )
open import Data.Product                           using ( Σ-syntax ; _×_ ; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base                          using ( inj₁ ; inj₂ ; [_,_]′ ) renaming ( map to ⊎-map )
open import Function                               using ( Func ; id ; _⇔_ ; mk⇔ )
open import Level                                  using ( Level )
open import Relation.Binary                        using ( Setoid )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( refl ; subst )
open import Relation.Nullary                       using ( Dec )

import Data.List.Relation.Unary.All as All

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Properties.Lattice        using ( module Lattice-Order )
open import Classical.Signatures.Lattice        using ( ∧-Op ; ∨-Op )
open import Classical.Structures.Lattice.Basic  using ( Lattice )
open import Classical.Structures.Lattice.Dual   using ( dualLattice )
open import Setoid.Algebras.Basic               using ( 𝔻[_] ; 𝕌[_] )
open import Setoid.Functions                    using ( IsSurjective ; Image_∋_ )
open import Setoid.Homomorphisms.Basic          using ( hom ; mkhom ; compatible-map )
open import Setoid.Homomorphisms.Properties     using ( ⊙-hom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Covers        using ( D ; D-total ; Dᵈ-total ; D-resp ; Nontrivial ; _≪_
                                                 ; FL-D-total )
open import Lattices.Bounded.Preimage      using ( bounded ; module Dual )
open import Lattices.Free.Bounded          using ( LeastAbove ; leastAbove? )
open import Lattices.Free.Canonical.Basic  using ( ≈ʷ-refl ; ≈ʷ-trans ; ∨̇-cong )
open import Lattices.Free.Duality          using ( dual ; dual-cong ; dual-reflects-≈ )
open import Lattices.Free.Substitution     using ( Sub ; _[_] ; hom-induced )
open import Lattices.Free.Term             using ( LatTerm ; _∨̇_ ; module Evaluation )
open import Lattices.Free.Universal        using ( FL ; FL-extend ; FL-extend-hom ; ≤ʷ→≤ ; ≤→≤ʷ )
open import Lattices.Free.Whitman          using ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ≤ʷ-refl ; ≤ʷ-trans ; ≤∨ˡ ; ≤∨ʳ )
open import Lattices.Generation            using ( _≤⋁_ ; ≤⋁⁺ ; ≤-≤⋁ ; ∨-≤⋁ ; ≤⋁-⊆ ; ∈→≤⋁ )
                                           renaming ( ⋁⁺ to ⋁⁺ᴸ )
open import Lattices.Kostinsky             using ( module HardDirection )
open import Lattices.Nation                using ( Embeds ; embeds→SatisfiesW )
open import Lattices.Semidistributive      using ( SatisfiesW ; hom-preserves-≤ ; hom-preserves-∧
                                                 ; hom-preserves-∨ ; hom-reflects-≤ )

open Func using () renaming ( to to _⟨$⟩_ )

private variable αᴸ ρᴸ υ : Level
```
-->

#### The least preimage under an embedding

Fix a lattice `𝑳`{.AgdaBound} presented by `η : Fin n → L` with `f` onto,
and an embedding `e` of it in `FL(Y)`.  An element `u` of `FL(Y)` is *below an
image* when some term `a` of `FL(n)` has `u ≤ a [ σ ]`
(`BelowImage`{.AgdaFunction}); every `e b` is, by a preimage of `b`.  For such a
`u`, Lemma 3.1 gives the least `a` with `u ≤ a [ σ ]`, and `β_e(u) = f a` is the
least element of `𝑳`{.AgdaBound} whose image lies above `u`
(`βᵉ-above`{.AgdaFunction}, `βᵉ-least`{.AgdaFunction}), since `e` reflects the
order.

```agda
module Reflect {n : ℕ} {Y : Type υ} (_≟ʸ_ : DecidableEquality Y) (𝑳 : Lattice αᴸ ρᴸ)
               (η : Fin n → 𝕌[ proj₁ 𝑳 ]) (onto : IsSurjective (FL-extend 𝑳 η))
               (emb : Embeds 𝑳 (FL Y)) where
  open Evaluation 𝑳          using ( ⟦_⟧ )
  open Lattice-Order 𝑳       using ( _≤_ ; ≤-refl ; ≤-trans ; ≤-reflexive ; ≤-antisym )
  open Lattice-Order (FL Y)  using () renaming ( _≤_ to _≤ʸ_ )
  open Setoid 𝔻[ proj₁ 𝑳 ]   using ( _≈_ ) renaming ( sym to ≈sym )

  private
    L : Type αᴸ
    L = 𝕌[ proj₁ 𝑳 ]

    f : LatTerm (Fin n) → L
    f w = ⟦ w ⟧ η

    fhom : hom (proj₁ (FL (Fin n))) (proj₁ 𝑳)
    fhom = FL-extend-hom 𝑳 η

    e : hom (proj₁ 𝑳) (proj₁ (FL Y))
    e = proj₁ emb

    e′ : L → LatTerm Y
    e′ b = proj₁ e ⟨$⟩ b

    -- The composite e ∘ f, as a substitution.
    σ : Sub (Fin n) Y
    σ x = e′ (η x)

    e-f : ∀ w → e′ (f w) ≈ʷ w [ σ ]
    e-f = hom-induced (⊙-hom fhom e)

    -- e of a list join is the list join of the images.
    e-⋁⁺ : ∀ s ss → e′ (⋁⁺ᴸ 𝑳 s ss) ≈ʷ ⋁⁺ᴸ (FL Y) (e′ s) (map e′ ss)
    e-⋁⁺ s []         = ≈ʷ-refl
    e-⋁⁺ s (s' ∷ ss)  =
      ≈ʷ-trans (hom-preserves-∨ 𝑳 (FL Y) e s (⋁⁺ᴸ 𝑳 s' ss)) (∨̇-cong ≈ʷ-refl (e-⋁⁺ s' ss))

  -- u lies below the image of some term of FL(n).
  BelowImage : LatTerm Y → Type υ
  BelowImage u = Σ[ a ∈ LatTerm (Fin n) ] u ≤ʷ a [ σ ]

  -- Every e b does, by a preimage of b.
  below-image : ∀ b → BelowImage (e′ b)
  below-image b with onto {b}
  ... | Image_∋_.eq w b≈fw = w , ≤ʷ-trans (proj₁ (Func.cong (proj₁ e) b≈fw)) (proj₁ (e-f w))

  -- The least term whose image lies above u, by Lemma 3.1.
  least : ∀ u → BelowImage u → LeastAbove σ u
  least u (a , p) = [ id , (λ none → ⊥-elim (none a p)) ]′ (leastAbove? _≟ʸ_ σ u)

  -- The least preimage of u.
  βᵉ : ∀ u → BelowImage u → L
  βᵉ u bi = f (LeastAbove.elt (least u bi))

  -- u ≤ e (βᵉ u).
  βᵉ-above : ∀ u bi → u ≤ʷ e′ (βᵉ u bi)
  βᵉ-above u bi = ≤ʷ-trans (LeastAbove.above (least u bi)) (proj₂ (e-f (LeastAbove.elt (least u bi))))

  -- βᵉ u lies below every element whose image lies above u.
  βᵉ-least : ∀ u bi b → u ≤ʷ e′ b → βᵉ u bi ≤ b
  βᵉ-least u bi b p with onto {b}
  ... | Image_∋_.eq w b≈fw =
    ≤-trans (hom-preserves-≤ (FL (Fin n)) 𝑳 fhom (≤ʷ→≤ (LeastAbove.least (least u bi) w
              (≤ʷ-trans p (≤ʷ-trans (proj₁ (Func.cong (proj₁ e) b≈fw)) (proj₁ (e-f w)))))))
            (≤-reflexive (≈sym b≈fw))
```

#### Corollary 2.15

For `u ∈ D_k(FL(Y))` below an image, `β_e(u) ∈ D_k(L)`, by induction on `k`.
For `k = 0`, `β_e(u) ≤ a₁ ∨ a₂` gives `u ≤ e a₁ ∨ e a₂`, so `u ≤ e aᵢ` by
primality, so `β_e(u) ≤ aᵢ`.  For `k + 1`, a nontrivial cover `S` of `β_e(u)`
becomes the nontrivial cover `e(S)` of `u`, refined inside `D_k(FL(Y))` to
`T`; the helper `refine`{.AgdaFunction} walks `T`, collecting the least
preimages `β_e(t)` (each in `D_k(L)` by induction, each below the member of `S`
whose image lies above `t`), together with the join `A` of the least terms,
whose image lies above the join of `T`; then `β_e(u) ≤ f A`, which lies below
the join of the collected preimages.

```agda
  -- Corollary 2.15: the least preimage of an element of D_k(FL(Y)) lies in D_k(L).
  D-reflect : ∀ k u (bi : BelowImage u) → D (FL Y) k u → D 𝑳 k (βᵉ u bi)
  D-reflect zero u bi jp {a₁} {a₂} p =
    [ (λ q → inj₁ (βᵉ-least u bi a₁ q)) , (λ q → inj₂ (βᵉ-least u bi a₂ q)) ]′
    (⊎-map ≤→≤ʷ ≤→≤ʷ (jp (≤ʷ→≤ (≤ʷ-trans (βᵉ-above u bi)
      (≤ʷ-trans (≤→≤ʷ (hom-preserves-≤ 𝑳 (FL Y) e p)) (proj₁ (hom-preserves-∨ 𝑳 (FL Y) e a₁ a₂)))))))
  D-reflect (suc k) u bi d S (≤⋁⁺ {s} {ss} p) nt = from-refinement (d (map e′ (s ∷ ss)) cover′ nt′)
    where
    -- The images of S cover u, nontrivially.
    cover′ : _≤⋁_ (FL Y) u (map e′ (s ∷ ss))
    cover′ = ≤⋁⁺ (≤ʷ→≤ (≤ʷ-trans (βᵉ-above u bi)
               (≤ʷ-trans (≤→≤ʷ (hom-preserves-≤ 𝑳 (FL Y) e p)) (proj₁ (e-⋁⁺ s ss)))))

    nt′ : Nontrivial (FL Y) u (map e′ (s ∷ ss))
    nt′ = map⁺ (All.map (λ {s'} ¬β≤s' u≤es' → ¬β≤s' (βᵉ-least u bi s' (≤→≤ʷ u≤es'))) nt)

    -- A member of the refinement lies below the image of a member of S, hence below an image.
    member : ∀ {t} → Any (t ≤ʸ_) (map e′ (s ∷ ss)) → Σ[ s' ∈ L ] (s' ∈ (s ∷ ss)) × (t ≤ʷ e′ s')
    member {t} any =
      let (v , v∈ , t≤v) = find any
          (s' , s'∈ , v≡) = ∈-map⁻ e′ {xs = s ∷ ss} v∈
      in s' , s'∈ , subst (t ≤ʷ_) v≡ (≤→≤ʷ t≤v)

    below-image′ : ∀ {t} → Any (t ≤ʸ_) (map e′ (s ∷ ss)) → BelowImage t
    below-image′ any =
      let (s' , _ , t≤es') = member any
          (w , es'≤w) = below-image s'
      in w , ≤ʷ-trans t≤es' es'≤w

    -- The least preimages of the members of a refinement, and the join of the least terms.
    refine : ∀ t ts → All (λ t' → Any (t' ≤ʸ_) (map e′ (s ∷ ss))) (t ∷ ts) → All (D (FL Y) k) (t ∷ ts)
           → Σ[ R ∈ List L ] (_≪_ 𝑳 R (s ∷ ss)) × All (D 𝑳 k) R
             × Σ[ A ∈ LatTerm (Fin n) ] (⋁⁺ᴸ (FL Y) t ts ≤ʷ A [ σ ]) × _≤⋁_ 𝑳 (f A) R
    refine t []         (any ∷ [])    (dt ∷ [])   =
      let bi′ = below-image′ any
          (s' , s'∈ , t≤es') = member any
      in βᵉ t bi′ ∷ [] , (lose s'∈ (βᵉ-least t bi′ s' t≤es') ∷ []) , (D-reflect k t bi′ dt ∷ [])
       , LeastAbove.elt (least t bi′) , LeastAbove.above (least t bi′) , ≤⋁⁺ ≤-refl
    refine t (t' ∷ ts)  (any ∷ anys)  (dt ∷ dts)  =
      let bi′ = below-image′ any
          (s' , s'∈ , t≤es') = member any
          (R' , R'≪S , allR' , A' , T'≤A' , fA'≤R') = refine t' ts anys dts
      in βᵉ t bi′ ∷ R' , (lose s'∈ (βᵉ-least t bi′ s' t≤es') ∷ R'≪S) , (D-reflect k t bi′ dt ∷ allR')
       , LeastAbove.elt (least t bi′) ∨̇ A'
       , ∨≤ (≤∨ˡ (LeastAbove.above (least t bi′))) (≤∨ʳ T'≤A')
       , ∨-≤⋁ 𝑳 (∈→≤⋁ 𝑳 (here refl)) (≤⋁-⊆ 𝑳 fA'≤R' there)

    -- The refinement of e(S), read back in 𝑳.
    from-refinement : Σ[ T ∈ List (LatTerm Y) ] (_≪_ (FL Y) T (map e′ (s ∷ ss)))
                                                × All (D (FL Y) k) T × _≤⋁_ (FL Y) u T
                    → Σ[ R ∈ List L ] (_≪_ 𝑳 R (s ∷ ss)) × All (D 𝑳 k) R × _≤⋁_ 𝑳 (βᵉ u bi) R
    from-refinement (T , T≪S′ , allT , ≤⋁⁺ {t} {ts} u≤T) =
      let (R , R≪S , allR , A , T≤A , fA≤R) = refine t ts T≪S′ allT
      in R , R≪S , allR
       , ≤-≤⋁ 𝑳 (hom-preserves-≤ (FL (Fin n)) 𝑳 fhom
                   (≤ʷ→≤ (LeastAbove.least (least u bi) A (≤ʷ-trans (≤→≤ʷ u≤T) T≤A)))) fA≤R
```

#### Corollary 2.16

Every `b` is the least preimage of its own image, and `e b` lies in some
`D_k(FL(Y))` by Corollary 2.11: so `D(L) = L`.

```agda
  -- The least preimage of e b is b.
  βᵉ-e : ∀ b (bi : BelowImage (e′ b)) → βᵉ (e′ b) bi ≈ b
  βᵉ-e b bi = ≤-antisym (βᵉ-least (e′ b) bi b ≤ʷ-refl)
                        (hom-reflects-≤ 𝑳 (FL Y) e (proj₂ emb) (≤ʷ→≤ (βᵉ-above (e′ b) bi)))

  -- Corollary 2.16: a finitely generated sublattice of FL(Y) has D(L) = L.
  embeds→D-total : D-total 𝑳
  embeds→D-total b =
    let (k , d) = FL-D-total _≟ʸ_ (e′ b)
    in k , D-resp 𝑳 k (βᵉ-e b (below-image b)) (D-reflect k (e′ b) (below-image b) d)
```

#### The dual

The dual of `𝑳`{.AgdaBound} embeds in `FL(Y)` by `b ↦ dual (e b)`, since
`dual` exchanges the formal operations and reflects equality
([Lattices.Free.Duality][]); so Corollary 2.16 for the dual lattice, with the
same assignment (onto by `Dual.ontoᵈ`{.AgdaFunction} of
[Lattices.Bounded.Preimage][]), gives `Dᵈ(L) = L`.

```agda
module _ {Y : Type υ} (𝑳 : Lattice αᴸ ρᴸ) (emb : Embeds 𝑳 (FL Y)) where
  private
    e : hom (proj₁ 𝑳) (proj₁ (FL Y))
    e = proj₁ emb

    e′ : 𝕌[ proj₁ 𝑳 ] → LatTerm Y
    e′ b = proj₁ e ⟨$⟩ b

    g : Func 𝔻[ proj₁ (dualLattice 𝑳) ] 𝔻[ proj₁ (FL Y) ]
    g = record { to = λ b → dual (e′ b) ; cong = λ b≈b' → dual-cong (Func.cong (proj₁ e) b≈b') }

    g-compatible : compatible-map (proj₁ (dualLattice 𝑳)) (proj₁ (FL Y)) g
    g-compatible {∧-Op} {a} = dual-cong (hom-preserves-∨ 𝑳 (FL Y) e (a 0F) (a 1F))
    g-compatible {∨-Op} {a} = dual-cong (hom-preserves-∧ 𝑳 (FL Y) e (a 0F) (a 1F))

  -- The dual lattice embeds in FL(Y) by the dual of the embedding.
  dual-embeds : Embeds (dualLattice 𝑳) (FL Y)
  dual-embeds = mkhom (proj₁ (dualLattice 𝑳)) (proj₁ (FL Y)) g (λ {f} {a} → g-compatible {f} {a})
              , λ e≈ → proj₂ emb (dual-reflects-≈ e≈)

  -- Corollary 2.16, dualized: a finitely generated sublattice of FL(Y) has Dᵈ(L) = L.
  embeds→Dᵈ-total : {n : ℕ} (η : Fin n → 𝕌[ proj₁ 𝑳 ]) → IsSurjective (FL-extend 𝑳 η)
                  → DecidableEquality Y → Dᵈ-total 𝑳
  embeds→Dᵈ-total η onto _≟ʸ_ =
    Reflect.embeds→D-total _≟ʸ_ (dualLattice 𝑳) η (Dual.ontoᵈ 𝑳 η onto) dual-embeds
```

#### The two readings of "bounded" agree

For a lattice presented by `suc m` generators with a decided order, being a
sublattice of `FL(suc m)` is equivalent to `D(L) = L = Dᵈ(L)` with (W): one
direction is this module with (W) inherited, the other is Theorem 2.6
([Lattices.Bounded.Preimage][]) followed by Kostinsky's hard direction.  With
`embedsFLn⇔bounded×W`{.AgdaFunction} of [Lattices.Kostinsky][], the data of a
bounded presentation and the book's condition agree in the presence of (W).

```agda
module _ {m : ℕ} (𝑳 : Lattice αᴸ ρᴸ) (_≤?_ : ∀ a b → Dec (Lattice-Order._≤_ 𝑳 a b))
         (η : Fin (suc m) → 𝕌[ proj₁ 𝑳 ]) (onto : IsSurjective (FL-extend 𝑳 η)) where

  -- A sublattice of FL(suc m) iff D(L) = L = Dᵈ(L) with (W), for a decided order.
  embedsFLn⇔D×Dᵈ×W : Embeds 𝑳 (FL (Fin (suc m))) ⇔ (D-total 𝑳 × Dᵈ-total 𝑳 × SatisfiesW 𝑳)
  embedsFLn⇔D×Dᵈ×W = mk⇔
    (λ emb → Reflect.embeds→D-total _≟_ 𝑳 η onto emb , embeds→Dᵈ-total 𝑳 emb η onto _≟_ , embeds→SatisfiesW 𝑳 emb)
    (λ (dt , dtᵈ , W) → HardDirection.embeds 𝑳 η onto (bounded 𝑳 _≤?_ η onto dt dtᵈ) W)
```

The module checks in about a second of its own.
