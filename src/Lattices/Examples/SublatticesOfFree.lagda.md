---
layout: default
file: "src/Lattices/Examples/SublatticesOfFree.lagda.md"
title: "Lattices.Examples.SublatticesOfFree module"
date: "2026-10-16"
author: "the agda-algebras development team"
---

### Worked example: which five-element lattices are sublattices of a free lattice

This is the [Lattices.Examples.SublatticesOfFree][] module of the [agda-lattices][] library.

The decision `isSublatticeOfFree?`{.AgdaFunction} of [Lattices.Nation][]
answers, for a finite lattice, whether it is semidistributive and satisfies
Whitman's condition (W), which by Nation's theorem ([Freese, Ježek, and Nation
(1995)][], Theorem 5.55) is whether it is a sublattice of a free lattice.  This
module runs it on the two five-element lattices that are not distributive,
the diamond `M₃`{.AgdaFunction} of [Lattices.Examples.M3][] and the pentagon
`N₅`{.AgdaFunction} of [Lattices.Examples.N5][].

+  **`M₃`**: no.  `M₃`{.AgdaFunction} satisfies (W) but neither
   semidistributive law, so by the easy direction it is a sublattice of no free
   lattice, with no hypothesis (`M₃-not-embeds`{.AgdaFunction}).
+  **`N₅`**: yes.  Under the record `NationsTheorem`{.AgdaRecord},
   `N₅`{.AgdaFunction} therefore embeds in `FL(3)` (`N₅-embeds`{.AgdaFunction}).
   For `N₅`{.AgdaFunction} the hypothesis is not needed:
   `N₅↪FL3`{.AgdaFunction} is an explicit embedding, and the easy direction
   applied to it confirms the positive verdict independently of the sweep.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.SublatticesOfFree where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                          using ( Fin )
open import Data.Fin.Patterns                      using ( 0F ; 1F ; 2F ; 3F ; 4F )
open import Data.Fin.Properties                    using ( _≟_ ; all? )
open import Data.Product                           using ( _×_ ; _,_ ; proj₁ ; proj₂ )
open import Function                               using ( Func )
open import Level                                  using ( Level ; 0ℓ )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ ; refl )
open import Relation.Nullary.Decidable.Core        using ( from-yes ; from-no ; _→-dec_ )
open import Relation.Nullary.Negation.Core         using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Signatures.Lattice           using ( ∧-Op ; ∨-Op )
open import Setoid.Algebras.Basic                  using ( 𝔻[_] )
open import Setoid.Homomorphisms.Basic             using ( compatible-map ; mkhom )

-- Imports from this library ----------------------------------------------------
open import Lattices.Bounded.Finite                using ( bounded? )
open import Lattices.Examples.M3                   using ( M₃ ; M₃-finite )
open import Lattices.Examples.N5                   using ( N₅ ; N₅-finite ; N₅-laws )
                                                   renaming ( _∧_ to _∧⁵_ ; _∨_ to _∨⁵_ )
open import Lattices.Free.Canonical.Basic          using ( ≈ʷ-refl )
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Universal                using ( FL )
open import Lattices.Free.Whitman                  using ( _≈ʷ_ ; module Decision )
open import Lattices.Kostinsky.Finite              using ( table-embedsFL3 )
open import Lattices.Nation
  using  ( Embeds ; NationsTheorem ; ¬S×W→¬embeds ; embedsFL3→S×W
         ; isSublatticeOfFree? ; embedsFL3? )
open import Lattices.Semidistributive              using ( IsSemidistributive ; SatisfiesW )

private variable χ : Level
```
-->

#### The diamond

The sweep stops at the first failure of the join semidistributive law, so the
negative verdict costs a handful of instances (`M₃-not-S×W`{.AgdaFunction}).
Through the contrapositive of the easy direction it refutes every embedding of
`M₃`{.AgdaFunction} into a free lattice whose generators have decidable
equality, `FL(3)` among them.  This half of the verdict is unconditional.

```agda
-- M₃ fails the hypothesis: it is not semidistributive.
M₃-not-S×W : ¬ (IsSemidistributive M₃ × SatisfiesW M₃)
M₃-not-S×W = from-no (isSublatticeOfFree? M₃ M₃-finite)

-- M₃ is a sublattice of no free lattice.
M₃-not-embeds : {X : Type χ} → DecidableEquality X → ¬ Embeds M₃ (FL X)
M₃-not-embeds _≟ˣ_ = ¬S×W→¬embeds M₃ _≟ˣ_ M₃-not-S×W
```

#### The pentagon

The positive verdict sweeps every instance: `2 · 5³` for the semidistributive
laws and `5⁴` for (W).  Read through the record, it is an embedding of
`N₅`{.AgdaFunction} into `FL(3)`, obtained here by `embedsFL3?`{.AgdaFunction},
the decision of embeddability under the hypothesis; this is how a development
that takes `NationsTheorem 0ℓ 0ℓ`{.AgdaRecord} as its parameter obtains the
embedding of any finite lattice that the sweep accepts.

```agda
-- N₅ satisfies the hypothesis.
N₅-S×W : IsSemidistributive N₅ × SatisfiesW N₅
N₅-S×W = from-yes (isSublatticeOfFree? N₅ N₅-finite)

-- Under the record, N₅ embeds in FL(3).
N₅-embeds : NationsTheorem 0ℓ 0ℓ → Embeds N₅ (FL (Fin 3))
N₅-embeds nation = from-yes (embedsFL3? N₅ N₅-finite nation)
```

#### An explicit embedding of the pentagon

For `N₅`{.AgdaFunction} the record can be avoided, because a pentagon in
`FL(3)` can be written down.  Any triple `u ≤ w`, `v` at which the modular law
fails yields one: `u ∨ (v ∧ w) < (u ∨ v) ∧ w` are the middle elements of a
pentagon whose third element is `v`.  With `u = x`, `w = x ∨ z` and `v = y`,
the five elements are as follows:

+  `⊥ ↦ y ∧ (x ∨ z)`;
+  `a ↦ x ∨ (y ∧ (x ∨ z))`;
+  `b ↦ y`;
+  `c ↦ (x ∨ y) ∧ (x ∨ z)`;
+  `⊤ ↦ x ∨ y`.

The map `ι`{.AgdaFunction} sends the elements of `N₅`{.AgdaFunction}, numbered
as in [Lattices.Examples.N5][], to these terms.  That it preserves both
operations and is injective is checked by Whitman's decision procedure
(`_≈ʷ?_`{.AgdaFunction} of [Lattices.Free.Whitman][]) on all 25 pairs for
each property, by evaluation.

```agda
x y z : LatTerm (Fin 3)
x = ℊ 0F
y = ℊ 1F
z = ℊ 2F

open Decision (_≟_ {n = 3}) using ( _≈ʷ?_ )

-- The images of ⊥, a, b, c, ⊤.
ι : Fin 5 → LatTerm (Fin 3)
ι 0F = y ∧̇ (x ∨̇ z)
ι 1F = x ∨̇ (y ∧̇ (x ∨̇ z))
ι 2F = y
ι 3F = (x ∨̇ y) ∧̇ (x ∨̇ z)
ι 4F = x ∨̇ y

-- ι preserves meets.
ι-∧ : ∀ i j → ι (i ∧⁵ j) ≈ʷ ι i ∧̇ ι j
ι-∧ = from-yes (all? λ i → all? λ j → ι (i ∧⁵ j) ≈ʷ? ι i ∧̇ ι j)

-- ι preserves joins.
ι-∨ : ∀ i j → ι (i ∨⁵ j) ≈ʷ ι i ∨̇ ι j
ι-∨ = from-yes (all? λ i → all? λ j → ι (i ∨⁵ j) ≈ʷ? ι i ∨̇ ι j)

-- ι is injective.
ι-injective : ∀ i j → ι i ≈ʷ ι j → i ≡ j
ι-injective = from-yes (all? λ i → all? λ j → ι i ≈ʷ? ι j →-dec i ≟ j)
```

The carrier of `N₅`{.AgdaFunction} is `Fin 5` with propositional equality,
so `ι`{.AgdaFunction} respects it trivially, and the interpretation of each
operation symbol in either lattice applies the binary operation to the two
arguments, so compatibility is `ι-∧`{.AgdaFunction} or `ι-∨`{.AgdaFunction}
at those arguments.  The resulting embedding `N₅↪FL3`{.AgdaFunction} makes the
membership of `N₅`{.AgdaFunction} among the sublattices of `FL(3)` a theorem
with no hypothesis, and the easy direction applied to it re-derives the
sweep's positive verdict by a different route
(`N₅-S×W-by-embedding`{.AgdaFunction}).

```agda
-- ι as a map of setoids.
ι-func : Func 𝔻[ proj₁ N₅ ] 𝔻[ proj₁ (FL (Fin 3)) ]
ι-func = record { to = ι ; cong = λ { refl → ≈ʷ-refl } }

-- ι commutes with both operations.
ι-compatible : compatible-map (proj₁ N₅) (proj₁ (FL (Fin 3))) ι-func
ι-compatible {∧-Op} {a} = ι-∧ (a 0F) (a 1F)
ι-compatible {∨-Op} {a} = ι-∨ (a 0F) (a 1F)

-- N₅ is a sublattice of FL(3), with no hypothesis.
N₅↪FL3 : Embeds N₅ (FL (Fin 3))
N₅↪FL3 = mkhom (proj₁ N₅) (proj₁ (FL (Fin 3))) ι-func (λ {f} {a} → ι-compatible {f} {a})
       , λ {i} {j} → ι-injective i j

-- The easy direction, applied to the embedding, confirms the sweep's verdict.
N₅-S×W-by-embedding : IsSemidistributive N₅ × SatisfiesW N₅
N₅-S×W-by-embedding = embedsFL3→S×W N₅ N₅↪FL3
```

#### The pentagon through Kostinsky's theorem

The finite case of Kostinsky's theorem ([Lattices.Kostinsky.Finite][]) gives
a third proof that `N₅`{.AgdaFunction} is a sublattice of `FL(3)`, again with no
hypothesis: the pentagon is bounded, that is, has no D-cycle and no dual cycle,
which `bounded?`{.AgdaFunction} of [Lattices.Bounded.Finite][] decides, and it
satisfies (W), so the least and greatest preimages computed from the sets
`D_k` make the map from `FL(5)` onto it a retraction, and the section embeds
it in `FL(5)`, hence in `FL(3)`.  Where `N₅↪FL3`{.AgdaFunction} was written
down and checked, this embedding is computed from the theorem.

```agda
-- N₅ is a sublattice of FL(3), by the finite case of Kostinsky's theorem.
N₅↪FL3-bounded : Embeds N₅ (FL (Fin 3))
N₅↪FL3-bounded = table-embedsFL3 N₅-laws (from-yes (bounded? N₅-laws)) (proj₂ N₅-S×W)
```
