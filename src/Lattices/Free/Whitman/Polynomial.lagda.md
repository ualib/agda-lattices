---
layout: default
file: "src/Lattices/Free/Whitman/Polynomial.lagda.md"
title: "Lattices.Free.Whitman.Polynomial module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Whitman's procedure with a table of subproblems

This is the [Lattices.Free.Whitman.Polynomial][] module of the [agda-lattices][] library.

Whitman's recursion, as [Lattices.Free.Whitman][] decides it
(`Decision._≤ʷ?_`{.AgdaFunction}), is exponential in the worst case.
[Freese, Ježek, and Nation (1995)][], Example 11.32, give a family of pairs
`vₙ ≤ uₙ` on which the recursion tests `vₙ₋₁ ≤ uₙ₋₁` twice at every level, once
through a meetand of `vₙ` and once through a joinand of `uₙ`, so that its cost
doubles with `n`.  The reason is not the rules but the repetition: the questions
the recursion asks are pairs `(v, u)` of a subterm of `s` and a subterm of `t`,
of which there are only `ℓ(s) · ℓ(t)` (the product of the two ranks, which the
book calls lengths), and Section 8 of Chapter XI shows that keeping a table of
the pairs already decided makes the procedure polynomial.  The value of a pair
is determined by Theorem 1.11 from the values of pairs in which one term is kept
and the other replaced by one of its children; so filling a table over all pairs
bottom up costs `O(ℓ(s) · ℓ(t))`, and also never less; while the recursion run
top down with a table only at the nodes of type (meet, join), (generator, join)
and (meet, generator) visits each node at most twice (Lemmas 11.33 to 11.37),
which gives Listing 11.16 its `O(ℓ(s) · ℓ(t))` worst case with constant minimum
time (Theorem 11.38).  Skolem's closure of a relational structure on the
subterms is a third polynomial route, which the same section recounts.

This module decides `_≤ʷ_`{.AgdaDatatype} a second time, by a table, and proves
nothing about it beyond its type: every entry of the table is a
`Dec`{.AgdaDatatype} of the inequality it answers, built from the constructors
and inversion lemmas of the rules exactly as `_≤ʷ?_`{.AgdaFunction} builds its
answer, so the root entry `s ≤ᵖ? t`{.AgdaFunction} is a decision of `s ≤ʷ t` by
construction, with no separate soundness or completeness proof; and since any
two decisions of one proposition agree, its verdict is
`_≤ʷ?_`{.AgdaFunction}'s (`≤ᵖ?-agrees`{.AgdaFunction}).

**The representation**.  The table is shaped by the terms, so that no positions,
indices, well-founded recursion or fuel appear.  A `Row v t`{.AgdaDatatype} is a
tree with the shape of `t` carrying, at the node of each subterm `u` of `t`, a
`Dec (v ≤ʷ u)`; the table for `s` against `t` is the row of `s`, built from the
rows of the subterms of `s` by recursion on `s`, and each row by recursion on `t`.
The entry for `(v, u)` is built, following the rule for the shapes of `v` and
`u`, from entries that are either in the rows of the children of `v` at the same
`u` (rules 2 and 5, and the first half of rule 6) or earlier in the same row, at
the children of `u` (rules 3 and 4, and the second half of rule 6); rule 1 is
the decidable equality of generators.  The rows of the children of `v` are
consumed in step with `t`, node for node, as the row of `v` is produced, so no
lookup function exists.  Termination is Agda's structural one, on `t` for the row
of a generator and on the rows for the row of a meet or a join.  The
alternatives, Listing 11.16 with its table at three node types (whose
minimum time is compared with this table's below) and Skolem's closure
(whose soundness and completeness would need their own proofs, through partial
lattices), both separate the computation from its correctness; the shaped table
makes them one thing.

**The bound**.  The table has one entry per pair of subterms, `ℓ(s) · ℓ(t)` in
all, and each entry is built from at most four others in a bounded number of
steps, so the whole table costs `O(ℓ(s) · ℓ(t))`, the bound of Chapter XI,
Section 8.  What the type checker pays is less: the entries are thunks of
Agda's compile-time evaluator, a call-by-need machine
(`Agda.TypeChecking.Reduce.Fast`), built when first demanded and shared
between the two nodes that can demand them (Lemma 11.36's two parents of a
node), and the verdict of the root demands, through the short-circuit
conjunctions and disjunctions of `_×-dec_`{.AgdaFunction} and
`_⊎-dec_`{.AgdaFunction}, only the verdicts Whitman's own order reaches.  The
rows themselves are less lazy than their verdicts: `row∧`{.AgdaFunction} and
`row∨`{.AgdaFunction} match the rows of both children of a node on the left
before either verdict is read, so deciding `s ≤ t` builds the outermost node
of the row of every subterm of `s`, one for each node of `s`, even when the
first verdict settles the question.  Nothing is built for a
subterm of `t` that the order does not reach.  So the minimum time is linear
in `ℓ(s)` and independent of `t`: `x ∧ v ≤ x ∨ u` is decided without building
any entry for `u`, but not without traversing `v`.  Measured 2026-10-22 (one
decision per module, pinned to a performance core, under the heap cap), with
`v` a nested meet of 250,001 nodes: `x ∧ v ≤ x ∨ y` took 4.6 s and `x ≤ x ∨ v`
1.6 s, the cost of loading the imported interfaces alone.  One detail makes
the sharing real.  A
`Dec`{.AgdaDatatype} built by `map′`{.AgdaFunction} or
`_⊎-dec_`{.AgdaFunction} is a record defined by copatterns, whose verdict is
recomputed at every projection of `does`{.AgdaField}; so each entry stores its
verdict as a literal (`store`{.AgdaFunction}), computed once when the entry is
first demanded.  Measured on the family of Example 11.32 (2026-10-22, one
decision per module, pinned to a performance core, under the build's heap cap
`+RTS -M6G -A128M`): without the stored verdicts, `n = 10` took two seconds and
`n = 20` four minutes, the doubling of the naive recursion in a different
dress; with them, `n = 5` to `n = 40` cost nothing measurable beyond the
second and a half the imported interfaces take to load, and `n = 80` about a
quarter of a second more; the recursion `_≤ʷ?_`{.AgdaFunction} takes 2.5 s of
processor time at `n = 10` and exhausts the 6 GB heap at `n = 15`.  [Lattices.Examples.WhitmanTable][] keeps the family and
three of those decisions.

**What the proofs cost**.  Nothing, at check time.  A theorem stated as
`from-yes (s ≤ᵖ? t)` makes the type checker evaluate the verdict, which is a
Boolean computed from Booleans; the derivations and refutations inside the
entries are never forced, and share their subderivations through the table
rather than copying them.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Free.Whitman.Polynomial where

open import Agda.Primitive  using () renaming ( Set to Type )

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Bool.Base                         using ( Bool ; true ; false )
open import Data.Product                           using ( uncurry )
open import Data.Sum.Base                          using ( [_,_]′ )
open import Level                                  using ( Level )
open import Relation.Binary.Definitions            using ( DecidableEquality )
open import Relation.Binary.PropositionalEquality  using ( _≡_ )
open import Relation.Nullary.Decidable.Core        using ( Dec ; _because_ ; does ; proof ; map′
                                                         ; _×-dec_ ; _⊎-dec_ )
open import Relation.Nullary.Reflects              using ( Reflects )

-- Imports from the agda-lattices library ---------------------------------------
open import Lattices.Free.Term     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman
  using  ( _≤ʷ_ ; _≈ʷ_ ; ∨≤ ; ℊ≤∧ ; ∧≤∧ ; ℊ≤ℊ ; ℊ≤∨ˡ ; ℊ≤∨ʳ ; ∧ˡ≤ℊ ; ∧ʳ≤ℊ ; ∧ˡ≤∨ ; ∧ʳ≤∨
         ; ∧≤∨ˡ ; ∧≤∨ʳ ; ∨≤-inv ; ≤∧-inv ; ℊ≤ℊ-inv ; ℊ≤∨-inv ; ∧≤ℊ-inv ; ∧≤∨-inv
         ; does-unique ; module Decision )

private variable
  χ ℓ : Level
  P : Type ℓ
  X : Type χ
  x y : X
  v v₁ v₂ t t₁ t₂ u : LatTerm X
```
-->

#### Rows

A `Row v t`{.AgdaDatatype} follows the shape of `t`: a leaf for a generator, and
a node with two subtrees for a meet or a join, each carrying the decision for
`v` against the subterm at that node.  `root`{.AgdaFunction} reads the decision
at the top of a row, the one for `v` against `t` itself.

```agda
data Row {X : Type χ} (v : LatTerm X) : LatTerm X → Type χ where
  leaf  : Dec (v ≤ʷ ℊ y) → Row v (ℊ y)
  meet  : Row v t₁ → Row v t₂ → Dec (v ≤ʷ t₁ ∧̇ t₂) → Row v (t₁ ∧̇ t₂)
  join  : Row v t₁ → Row v t₂ → Dec (v ≤ʷ t₁ ∨̇ t₂) → Row v (t₁ ∨̇ t₂)

-- The entry at the root of a row: the decision for the whole right-hand term.
root : Row v t → Dec (v ≤ʷ t)
root (leaf d)      = d
root (meet _ _ d)  = d
root (join _ _ d)  = d
```

#### Storing a verdict

`store`{.AgdaFunction} rebuilds a decision as a record whose
`does`{.AgdaField} field is a literal: `store′`{.AgdaFunction} matches on the
Boolean, which computes it once, and keeps the proof as it was.  Every entry of
the table goes through it, for the reason the header gives: a decision built by
the combinators is a record defined by copatterns, and projecting its verdict
runs the combinators again at every projection, which on a shared entry is the
repetition the table exists to remove.

```agda
-- Rebuild a decision as a constructor whose verdict is a literal: matching on
-- the Boolean computes it once, and the proof is left as it was.
store′ : (b : Bool) → Reflects P b → Dec P
store′ true   r = true   because r
store′ false  r = false  because r

store : Dec P → Dec P
store d = store′ (does d) (proof d)
```

#### The entries, one rule each

The six rules of Theorem 1.11 fall into nine cases by the shapes of the two
sides.  Each helper below builds one node of a row from the entries its rule
names, transporting the answer along the rule and its inversion with
`map′`{.AgdaFunction} as `_≤ʷ?_`{.AgdaFunction} does, and storing the verdict.
`∨≤-entry`{.AgdaFunction} is rule 2 at a single entry, from the entries of the
two joinands' rows at the same `u`; `meetℊ`{.AgdaFunction} and
`meet∧`{.AgdaFunction} are rule 3, and `joinℊ`{.AgdaFunction} rule 4, each from
the row's own entries at the two children of `u`, which are the roots of the
two subtrees; `join∧`{.AgdaFunction} is rule 6, Whitman's condition, from the
entries of the two meetands' rows at the whole join (its first two arguments)
and the row's own entries at the two joinands.  Rules 1 and 5 produce leaves and
are written where the rows are filled.

```agda
-- Rule 2 at one entry: a join on the left is below u iff both joinands are.
∨≤-entry : Dec (v₁ ≤ʷ u) → Dec (v₂ ≤ʷ u) → Dec (v₁ ∨̇ v₂ ≤ʷ u)
∨≤-entry d₁ d₂ = store (map′ (uncurry ∨≤) ∨≤-inv (d₁ ×-dec d₂))

-- Rule 3 for a generator on the left, from the rows at the two meetands.
meetℊ : Row (ℊ x) t₁ → Row (ℊ x) t₂ → Row (ℊ x) (t₁ ∧̇ t₂)
meetℊ r₁ r₂ = meet r₁ r₂ (store (map′ (uncurry ℊ≤∧) ≤∧-inv (root r₁ ×-dec root r₂)))

-- Rule 3 for a meet on the left.
meet∧ : Row (v₁ ∧̇ v₂) t₁ → Row (v₁ ∧̇ v₂) t₂ → Row (v₁ ∧̇ v₂) (t₁ ∧̇ t₂)
meet∧ r₁ r₂ = meet r₁ r₂ (store (map′ (uncurry ∧≤∧) ≤∧-inv (root r₁ ×-dec root r₂)))

-- Rule 4: a generator below a join, from the rows at the two joinands.
joinℊ : Row (ℊ x) t₁ → Row (ℊ x) t₂ → Row (ℊ x) (t₁ ∨̇ t₂)
joinℊ r₁ r₂ = join r₁ r₂ (store (map′ [ ℊ≤∨ˡ , ℊ≤∨ʳ ]′ ℊ≤∨-inv (root r₁ ⊎-dec root r₂)))

-- Rule 6, Whitman's condition: from the entries of the meetands' rows at the
-- whole join, and the row's own entries at the two joinands.
join∧ : Dec (v₁ ≤ʷ t₁ ∨̇ t₂) → Dec (v₂ ≤ʷ t₁ ∨̇ t₂)
      → Row (v₁ ∧̇ v₂) t₁ → Row (v₁ ∧̇ v₂) t₂ → Row (v₁ ∧̇ v₂) (t₁ ∨̇ t₂)
join∧ d₁ d₂ r₁ r₂ =
  join r₁ r₂ (store (map′ [ [ ∧ˡ≤∨ , ∧ʳ≤∨ ]′ , [ ∧≤∨ˡ , ∧≤∨ʳ ]′ ]′ ∧≤∨-inv
                          ((d₁ ⊎-dec d₂) ⊎-dec (root r₁ ⊎-dec root r₂))))
```

#### Filling the table

`Decisionᵖ`{.AgdaModule} takes the decidable equality of generators as its
parameter, as `Decision`{.AgdaModule} does.  `rowℊ x t`{.AgdaFunction} is the
row of a generator, by recursion on `t`: rule 1 at a generator, and rules 3
and 4 at a meet and a join.  `row∧`{.AgdaFunction} builds the row of a meet
from the rows of its two meetands, which have the shape of the same `t`, so
the recursion matches the two rows node for node: at a generator it is rule 5,
from the two leaves; at a meet, rule 3, from its own two subtrees; at a join,
rule 6, from the two roots of the meetands' subtrees and its own.
`row∨`{.AgdaFunction} builds the row of a join the same way, with rule 2 at
every node.  `table s t`{.AgdaFunction} is then the row of `s`, by recursion on
`s`, and `s ≤ᵖ? t`{.AgdaFunction} is its root; `_≈ᵖ?_`{.AgdaFunction} decides
equality in the free lattice by two tables.

Sharing lives in the arguments.  A row built for the row of a meet, say
`row∧ r₁₁ r₂₁`, is passed to the helper that places it, which uses it twice,
as a subtree and for its root; the evaluator binds the argument once, so the
two uses are one thunk.  A `let` would not do: Agda substitutes a
`let`-bound term into each of its uses before evaluation.

```agda
module Decisionᵖ {X : Type χ} (_≟_ : DecidableEquality X) where
  infix 4 _≤ᵖ?_ _≈ᵖ?_

  -- The row of a generator, by recursion on the right-hand term: rules 1, 3, 4.
  rowℊ : (x : X) (t : LatTerm X) → Row (ℊ x) t
  rowℊ x (ℊ y)      = leaf (store (map′ ℊ≤ℊ ℊ≤ℊ-inv (x ≟ y)))
  rowℊ x (t₁ ∧̇ t₂)  = meetℊ (rowℊ x t₁) (rowℊ x t₂)
  rowℊ x (t₁ ∨̇ t₂)  = joinℊ (rowℊ x t₁) (rowℊ x t₂)

  -- The row of a meet, from the rows of its meetands: rules 5, 3, 6.
  row∧ : Row v₁ t → Row v₂ t → Row (v₁ ∧̇ v₂) t
  row∧ (leaf d₁)          (leaf d₂)          =
    leaf (store (map′ [ ∧ˡ≤ℊ , ∧ʳ≤ℊ ]′ ∧≤ℊ-inv (d₁ ⊎-dec d₂)))
  row∧ (meet r₁₁ r₁₂ _)   (meet r₂₁ r₂₂ _)   = meet∧ (row∧ r₁₁ r₂₁) (row∧ r₁₂ r₂₂)
  row∧ (join r₁₁ r₁₂ d₁)  (join r₂₁ r₂₂ d₂)  = join∧ d₁ d₂ (row∧ r₁₁ r₂₁) (row∧ r₁₂ r₂₂)

  -- The row of a join, from the rows of its joinands: rule 2 at every entry.
  row∨ : Row v₁ t → Row v₂ t → Row (v₁ ∨̇ v₂) t
  row∨ (leaf d₁)          (leaf d₂)          = leaf (∨≤-entry d₁ d₂)
  row∨ (meet r₁₁ r₁₂ d₁)  (meet r₂₁ r₂₂ d₂)  =
    meet (row∨ r₁₁ r₂₁) (row∨ r₁₂ r₂₂) (∨≤-entry d₁ d₂)
  row∨ (join r₁₁ r₁₂ d₁)  (join r₂₁ r₂₂ d₂)  =
    join (row∨ r₁₁ r₂₁) (row∨ r₁₂ r₂₂) (∨≤-entry d₁ d₂)

  -- The table: the row of s against t, from the rows of s's subterms.
  table : (s t : LatTerm X) → Row s t
  table (ℊ x)      t = rowℊ x t
  table (s₁ ∧̇ s₂)  t = row∧ (table s₁ t) (table s₂ t)
  table (s₁ ∨̇ s₂)  t = row∨ (table s₁ t) (table s₂ t)

  -- The decision: the root entry of the table.
  _≤ᵖ?_ : (s t : LatTerm X) → Dec (s ≤ʷ t)
  s ≤ᵖ? t = root (table s t)

  -- Equality in the free lattice, by two tables.
  _≈ᵖ?_ : (s t : LatTerm X) → Dec (s ≈ʷ t)
  s ≈ᵖ? t = s ≤ᵖ? t ×-dec t ≤ᵖ? s
```

#### Agreement with the direct recursion

Both procedures decide the same proposition, so their verdicts agree
(`≤ᵖ?-agrees`{.AgdaFunction}, `≈ᵖ?-agrees`{.AgdaFunction}), by
`does-unique`{.AgdaFunction} of [Lattices.Free.Whitman][], as the comparison of
canonical forms agrees with `_≈ʷ?_`{.AgdaFunction} in
[Lattices.Free.Canonical.Uniqueness][].

```agda
  open Decision _≟_ using ( _≤ʷ?_ ; _≈ʷ?_ )

  -- The table's verdict is the direct recursion's.
  ≤ᵖ?-agrees : (s t : LatTerm X) → does (s ≤ᵖ? t) ≡ does (s ≤ʷ? t)
  ≤ᵖ?-agrees s t = does-unique (s ≤ᵖ? t) (s ≤ʷ? t)

  ≈ᵖ?-agrees : (s t : LatTerm X) → does (s ≈ᵖ? t) ≡ does (s ≈ʷ? t)
  ≈ᵖ?-agrees s t = does-unique (s ≈ᵖ? t) (s ≈ʷ? t)
```
