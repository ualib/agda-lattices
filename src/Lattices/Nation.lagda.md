---
layout: default
file: "src/Lattices/Nation.lagda.md"
title: "Lattices.Nation module"
date: "2026-10-16"
author: "the agda-algebras development team"
---

### Nation's theorem as a hypothesis

This is the [Lattices.Nation][] module of the [agda-lattices][] library.

*Nation's theorem* ([Freese, Ježek, and Nation (1995)][], Theorem 5.55) says
that a finite lattice is a sublattice of a free lattice if and only if it is
semidistributive and satisfies Whitman's condition (W).  One direction is
elementary: a free lattice satisfies (W) (Whitman, 1941; Theorem 1.8 of the
book) and both semidistributive laws (Jónsson and Kiefer; Theorem 1.21), and
the three conditions pass to sublattices.  The other is deep.  Jónsson and
Kiefer proposed it in 1962 ("Finite sublattices of a free lattice",
*Canadian Journal of Mathematics* 14, 487–497), and Nation proved it twenty
years later ("Finite sublattices of a free lattice", *Transactions of the
American Mathematical Society* 269 (1982), 311–337); the book's proof, which
follows Nation's, fills Chapter V, Section 3, and rests on the theory of
bounded homomorphisms of Chapter II.

This module states the theorem once, so that every development that uses it
assumes the same statement.  The hard direction is not proved here.  It is
the record `NationsTheorem`{.AgdaRecord}, which a module that needs it takes
as a parameter; it is not a postulate, which `--safe` forbids, and every
theorem proved from it says so in its type.  The module then proves the easy
direction (`embeds→S×W`{.AgdaFunction}), which with the record gives the
characterization, and decides the record's hypothesis for a finite lattice
(`isSublatticeOfFree?`{.AgdaFunction}).

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Nation where

open import Agda.Primitive  using ( Setω ) renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Fin.Base                    using ( Fin )
open import Data.Fin.Properties              using ( _≟_ )
open import Data.Product                     using ( _×_ ; _,_ ; proj₁ ; uncurry )
open import Data.Sum.Base                    using ( _⊎_ )
open import Function                         using ( _⇔_ ; mk⇔ )
open import Level                            using ( Level ; _⊔_ ) renaming ( suc to lsuc )
open import Relation.Binary                  using ( Setoid )
open import Relation.Binary.Definitions      using ( DecidableEquality )
open import Relation.Nullary.Decidable       using () renaming ( map to Dec-map )
open import Relation.Nullary.Decidable.Core  using ( Dec ; _×-dec_ )
open import Relation.Nullary.Negation.Core   using ( ¬_ )

-- Imports from the Agda Universal Algebra Library ------------------------------
open import Classical.Structures.Lattice.Basic  using ( Lattice ; module Lattice-Op )
open import Setoid.Algebras.Basic               using ( 𝔻[_] )
open import Setoid.Algebras.Finite              using ( FiniteAlgebra )
open import Setoid.Subalgebras.Basic            using ( _IsSubalgebraOf_ )

-- Imports from this library ----------------------------------------------------
open import Lattices.Free.Semidistributive  using ( FL-satisfiesW ; FL-isSemidistributive )
open import Lattices.Free.Universal         using ( FL )
open import Lattices.Semidistributive
  using  ( IsSemidistributive ; SatisfiesW ; IsSemidistributive-S-invar ; SatisfiesW-S-invar
         ; isSemidistributive? ; satisfiesW? ; W-irreducible )

private variable α ρ β ρᵃ ρᵇ χ : Level
```
-->

#### Embeddings

A lattice `𝑲`{.AgdaBound} *embeds* in a lattice `𝑳`{.AgdaBound} if there is an
injective homomorphism from `𝑲`{.AgdaBound} to `𝑳`{.AgdaBound}; its image is
then a sublattice of `𝑳`{.AgdaBound} isomorphic to `𝑲`{.AgdaBound}.  A lattice
homomorphism is a homomorphism of the underlying algebras over
`Sig-Lattice`{.AgdaFunction}, so an embedding is exactly agda-algebras'
subalgebra relation `_IsSubalgebraOf_`{.AgdaFunction} on the underlying
algebras ([Setoid.Subalgebras.Basic][]): a homomorphism paired with a proof that
it is injective with respect to the two setoid equalities.
`Embeds`{.AgdaFunction} is that relation, read on lattices, so that the
invariance lemmas of [Lattices.Semidistributive][], which take the same witness,
apply to it as they stand.

```agda
-- 𝑲 embeds in 𝑳: an injective homomorphism of the underlying algebras.
Embeds : Lattice α ρᵃ → Lattice β ρᵇ → Type (α ⊔ ρᵃ ⊔ β ⊔ ρᵇ)
Embeds 𝑲 𝑳 = proj₁ 𝑲 IsSubalgebraOf proj₁ 𝑳
```

#### The easy direction

A sublattice of a free lattice is semidistributive and satisfies (W).  Each
condition holds in `FL X`{.AgdaFunction} ([Lattices.Free.Semidistributive][]:
`FL-satisfiesW`{.AgdaFunction} and `FL-isSemidistributive`{.AgdaFunction}) and
passes to a sublattice along the embedding (`SatisfiesW-S-invar`{.AgdaFunction}
and `IsSemidistributive-S-invar`{.AgdaFunction} of
[Lattices.Semidistributive][]).  Neither step needs finiteness, so the lemmas
hold for any lattice `𝑲`{.AgdaBound}.  (W) holds for any type of generators;
semidistributivity is proved for `FL X`{.AgdaFunction} through canonical forms,
which compare generators, so it assumes that their equality is decidable, an
explicit argument `_≟ˣ_`{.AgdaBound}.

`embeds→S×W`{.AgdaFunction} states the result with the two conditions paired,
the form in which the record's field takes them, so that the two together
give the characterization below.  Its contrapositive,
`¬S×W→¬embeds`{.AgdaFunction}, refutes an embedding outright: a lattice that
fails either condition is a sublattice of no free lattice, with no hypothesis
at all.

```agda
module _ (𝑲 : Lattice α ρ) {X : Type χ} where

  -- A sublattice of a free lattice satisfies (W).
  embeds→SatisfiesW : Embeds 𝑲 (FL X) → SatisfiesW 𝑲
  embeds→SatisfiesW sub = SatisfiesW-S-invar 𝑲 (FL X) sub FL-satisfiesW

  module _ (_≟ˣ_ : DecidableEquality X) where

    -- A sublattice of a free lattice is semidistributive.
    embeds→IsSemidistributive : Embeds 𝑲 (FL X) → IsSemidistributive 𝑲
    embeds→IsSemidistributive sub =
      IsSemidistributive-S-invar 𝑲 (FL X) sub (FL-isSemidistributive _≟ˣ_)

    -- The easy direction of Nation's theorem, for any lattice.
    embeds→S×W : Embeds 𝑲 (FL X) → IsSemidistributive 𝑲 × SatisfiesW 𝑲
    embeds→S×W sub = embeds→IsSemidistributive sub , embeds→SatisfiesW sub

    -- A lattice failing either condition embeds in no free lattice.
    ¬S×W→¬embeds : ¬ (IsSemidistributive 𝑲 × SatisfiesW 𝑲) → ¬ Embeds 𝑲 (FL X)
    ¬S×W→¬embeds ¬sw sub = ¬sw (embeds→S×W sub)
```

The instance for `FL(3)`, the target of the record, takes the decidable
equality of `Fin 3`{.AgdaDatatype} from the standard library.

```agda
-- The easy direction for FL(3).
embedsFL3→S×W : (𝑲 : Lattice α ρ)
  → Embeds 𝑲 (FL (Fin 3)) → IsSemidistributive 𝑲 × SatisfiesW 𝑲
embedsFL3→S×W 𝑲 = embeds→S×W 𝑲 _≟_
```

#### The hypothesis

The theorem's hard direction is stated in its strongest finite form: a finite,
semidistributive lattice satisfying (W) embeds in the free lattice on three
generators.  Nation's theorem gives an embedding into *some* free lattice (the
proof produces one into the free lattice generated by the elements of the
lattice); since the lattice is finite, finitely many generators suffice, and
the free lattice on countably many generators embeds in `FL(3)`
([Freese, Ježek, and Nation (1995)][], Theorem 1.28, after Whitman), so `FL(3)`
can always be the target.  Conversely, an embedding into `FL(3)` is one into a
free lattice.  So the record is equivalent to the hard direction of Theorem
5.55 as the book states it.

Finiteness is a `FiniteAlgebra`{.AgdaRecord} of the lattice's algebra
([Setoid.Algebras.Finite][]): a surjective enumeration `Fin card → 𝕌` and a
decision procedure for the lattice's equality.  It is the hypothesis that the
decision procedures `isSemidistributive?`{.AgdaFunction} and
`satisfiesW?`{.AgdaFunction} already take, so a lattice whose conditions are
decided is one the record applies to, with nothing more to supply.

The record is level-polymorphic, with the levels of the lattices it speaks of.
The table lattices of [Lattices.Table][] (`M₃`{.AgdaFunction},
`N₅`{.AgdaFunction}, the quotients of a finite table lattice) live at
`Lattice 0ℓ 0ℓ`{.AgdaFunction}, so `NationsTheorem 0ℓ 0ℓ`{.AgdaRecord} is the
hypothesis a development about them takes as its parameter.  The field's type
at those levels lies in `Type₁`: the subalgebra relation carries the levels of
the signature `Sig-Lattice`{.AgdaFunction}, which are `0ℓ`, besides those of
the two algebras, and `FL (Fin 3)`{.AgdaFunction} is a
`Lattice 0ℓ 0ℓ`{.AgdaFunction}.  A consumer opens it as follows:

    module _ (nation : NationsTheorem 0ℓ 0ℓ) where
      open NationsTheorem nation using ( embed )

```agda
-- The hard direction of Nation's theorem (FJN Theorem 5.55), as a hypothesis:
-- a finite semidistributive lattice satisfying (W) embeds in FL(3).
record NationsTheorem (α ρ : Level) : Type (lsuc (α ⊔ ρ)) where
  field
    embed : (𝑲 : Lattice α ρ) → FiniteAlgebra (proj₁ 𝑲)
          → IsSemidistributive 𝑲 → SatisfiesW 𝑲 → Embeds 𝑲 (FL (Fin 3))
```

#### The characterization, modulo the hypothesis

Under the record, the two directions meet: a finite lattice embeds in `FL(3)`
if and only if it is semidistributive and satisfies (W).  This is Theorem 5.55
for the lattices the record speaks of, with `FL(3)` as the free lattice, and it
is a theorem whose type names its hypothesis.

```agda
module _ (nation : NationsTheorem α ρ)
         (𝑲 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑲)) where
  open NationsTheorem nation using ( embed )

  -- Nation's theorem for FL(3): its hard direction is the hypothesis.
  S×W⇔embedsFL3 : (IsSemidistributive 𝑲 × SatisfiesW 𝑲) ⇔ Embeds 𝑲 (FL (Fin 3))
  S×W⇔embedsFL3 = mk⇔ (uncurry (embed 𝑲 𝑭)) (embedsFL3→S×W 𝑲)
```

#### The decision, modulo the hypothesis

In a finite lattice the record's hypothesis is decidable: semidistributivity
and (W) are decided by the sweeps of [Lattices.Semidistributive][]
(`isSemidistributive?`{.AgdaFunction}, over triples, and
`satisfiesW?`{.AgdaFunction}, over quadruples), and
`isSublatticeOfFree?`{.AgdaFunction} is their conjunction.  Its name is the
question it answers *modulo Nation's theorem*: without the record it decides
the two conditions and nothing more.  A negative answer needs no hypothesis to
mean what the name says, since by the easy direction a lattice failing either
condition is a sublattice of no free lattice (`¬S×W→¬embeds`{.AgdaFunction}).
A positive answer means that the lattice is a sublattice of a free lattice
only through the hard direction, which is the record.  Under the record the
same sweep decides embeddability in `FL(3)` itself
(`embedsFL3?`{.AgdaFunction}), transported along the characterization; a
positive answer then yields the embedding the record supplies, not one built
from the lattice.

A lattice with `n` enumerated elements costs `2n³` instances for the
semidistributive laws and `n⁴` for (W); in a closed lattice, `from-yes` or
`from-no` of the answer is a proof by evaluation, as in
[Lattices.Examples.SublatticesOfFree][].

```agda
module _ (𝑲 : Lattice α ρ) (𝑭 : FiniteAlgebra (proj₁ 𝑲)) where

  -- The record's hypothesis, decided in a finite lattice.
  isSublatticeOfFree? : Dec (IsSemidistributive 𝑲 × SatisfiesW 𝑲)
  isSublatticeOfFree? = isSemidistributive? 𝑲 𝑭 ×-dec satisfiesW? 𝑲 𝑭

  -- Under the record, embeddability in FL(3), decided by the same sweep.
  embedsFL3? : NationsTheorem α ρ → Dec (Embeds 𝑲 (FL (Fin 3)))
  embedsFL3? nation = Dec-map (S×W⇔embedsFL3 nation 𝑲 𝑭) isSublatticeOfFree?
```

#### What the hard direction rests on

The record stands in for the following chain of results of [Freese, Ježek, and
Nation (1995)][], read for a finite lattice `L`; the page numbers are the
book's.  An *S-lattice* is a finite semidistributive lattice satisfying (W).

+  **Theorem 5.55** (p. 126) is Lemma 5.35 combined with Lemma 5.54.
+  **Lemma 5.35** (p. 109): for a finite lattice, being projective, being a
   sublattice of a free lattice, being bounded and satisfying (W), and being an
   S-lattice with no *C-cycle* are equivalent.  The hard direction uses the
   last implies the third (Lemma 2.62 and its dual, through Day's theorem,
   Theorem 2.64 and Corollary 2.65, pp. 53 to 54), and the third implies the
   second (Kostinsky's Corollary 5.9, p. 100, which applies the Freese and
   Nation characterization of projective lattices, Theorem 5.7, p. 99, and
   Theorem 5.1, p. 96).
+  **Lemma 5.54** (p. 125): an S-lattice contains no C-cycle.  This is the
   whole of Nation's argument, Lemmas 5.36 to 5.53 (pp. 111 to 125): the
   configurations that (W) excludes from a finite lattice (Lemmas 5.38 to 5.40),
   *B-type sequences* (p. 113), and a case analysis on a minimal C-cycle.
+  **Chapter II** supplies the vocabulary: the map `κ` from join irreducible
   to meet irreducible elements in a finite semidistributive lattice (Theorems
   2.54 and 2.56, p. 50); the relations `A`, `B` and `C` on join irreducible
   elements (p. 51) with Lemmas 2.57, 2.58 and the duality Lemma 2.63 (p. 53);
   the sets `Dₖ(L)` (p. 31) and the `D` relation (p. 39), with lower
   boundedness as `D(L) = L` (Theorem 2.13, p. 33) and, for finite `L`, as the
   absence of a `D`-cycle (Corollary 2.39, p. 42); and the general form of
   Theorem 1.21, the semidistributive law for finite joins in every join
   semidistributive lattice, which Lemma 2.58 uses.
+  **Theorem 1.28** (p. 23, after Whitman): `FL(ω)` is a sublattice of `FL(3)`,
   which moves the embedding into `FL(3)`.

Chapter IV (Day's theorem revisited) is not used.  Of all this, the library
has (W) and semidistributivity with their invariance and their decisions, the
free lattice with its universal property and Whitman's decision procedure,
Corollary 1.13 (free generation) in [Lattices.Free.Generation][], the
relation `D` and boundedness as the absence of a D-cycle, for table lattices
([Lattices.Bounded.Finite][]), the sets `Dₖ(L)` and `D(L)`
([Lattices.Bounded.Covers][]), bounded homomorphisms and bounded lattices
([Lattices.Bounded.Homomorphism][]), projectivity and Theorem 5.1
([Lattices.Projective][]), Corollary 5.9 ([Lattices.Kostinsky][]), and the
step of Lemma 5.35 from the third condition to the second
([Lattices.Kostinsky.Finite][]).  On table lattices it also has `κ` with the
relations `A`, `B` and `C` and Lemmas 2.57, 2.58 and 2.63
([Lattices.Nation.Kappa][]), the general form of Theorem 1.21
([Lattices.Semidistributive.FiniteJoins][]), Lemma 2.62 and Corollary 2.65
([Lattices.Nation.Bounded][]), and Lemma 5.54 through Lemmas 5.36 to 5.53,
with its consequence that an S-lattice is bounded
([Lattices.Nation.Lemma554][]).  What the record still stands in for is their
assembly: the passage from a finite lattice to a table lattice, and Theorem
5.55 itself.

The forbidden-sublattice form of the theorem (Theorems 5.56 and 5.58,
pp. 126 to 128, after Davey, Poguntke and Rival, and Antonius and Rival) says
that a finite lattice is a sublattice of a free lattice if and only if none of
eight small lattices is a sublattice of it, `M₃` among them.  Its proof is
Theorem 5.55 together with elementary arguments, so as a hypothesis it is no
weaker, and it is not cheaper to state: it needs the eight lattices and the
sublattice relation, where the record needs two predicates the library already
has and decides.

#### The statement of Corollary 1.9

Corollary 1.9 of [Freese, Ježek, and Nation (1995)][] is one definition whose
type is the statement, `FJN-1·9`{.AgdaFunction}, a record in `Setω` with one
field for each of its two sentences; [Lattices.Free.FJN][] lists it with the
rest of Chapter I.  (1) Every sublattice of a free lattice satisfies (W): a
lattice that embeds in `FL(X)` satisfies (W), for binary meets and joins as in
[Lattices.Semidistributive][], which is equivalent to the book's n-ary (W).
(2) Every element of a lattice satisfying (W) is join irreducible or meet
irreducible.  Read constructively, as `W-irreducible`{.AgdaFunction} states
it: if an element is both a join `b ∨ c` and a meet `d ∧ e`, it equals one of
the four, so it is not both a proper join and a proper meet.  Classically the
two readings agree.

```agda
-- FJN Corollary 1.9: sublattices of free lattices satisfy (W), and in a lattice
-- with (W) no element is both a proper join and a proper meet.
record FJN-1·9 : Setω where
  field
    part-1 : ∀ {α ρ χ} (𝑲 : Lattice α ρ) {X : Type χ} → Embeds 𝑲 (FL X) → SatisfiesW 𝑲
    part-2 : ∀ {α ρ} (𝑳 : Lattice α ρ) → SatisfiesW 𝑳
             → let open Lattice-Op 𝑳 using ( _∧_ ; _∨_ )
                   open Setoid 𝔻[ 𝑳 .proj₁ ] using ( _≈_ )
               in
               ∀ {a b c d e} → a ≈ b ∨ c → a ≈ d ∧ e → (a ≈ d ⊎ a ≈ e) ⊎ (a ≈ b ⊎ a ≈ c)

fjn-1·9 : FJN-1·9
fjn-1·9 = record  { part-1 = embeds→SatisfiesW
                  ; part-2 = W-irreducible
                  }
```
