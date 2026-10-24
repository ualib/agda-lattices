---
layout: default
file: "src/Lattices/Examples/WhitmanTable.lagda.md"
title: "Lattices.Examples.WhitmanTable module"
date: "2026-10-22"
author: "the agda-lattices development team"
---

### Worked example: the family on which Whitman's recursion is exponential

This is the [Lattices.Examples.WhitmanTable][] module of the [agda-lattices][] library.

[Freese, Ježek, and Nation (1995)][], Example 11.32, is the family of pairs on
which Whitman's recursion doubles its work at every level.  In the free lattice
on the generators `x₀, x₁, …` and `y₀, y₁, …`, let `v₀ = x₀ ∧ x₁` and
`u₀ = y₀ ∨ y₁`, and for `n ≥ 1`

    vₙ = xₙ ∧ xₙ₊₁ ∧ (yₙ ∨ vₙ₋₁)        uₙ = yₙ ∨ yₙ₊₁ ∨ (xₙ ∧ uₙ₋₁).

Testing `vₙ ≤ uₙ`, the first rule to apply is Whitman's condition.  Neither `xₙ`
nor `xₙ₊₁` is below `uₙ`, so the recursion asks whether `yₙ ∨ vₙ₋₁` is below
`uₙ`, which leads to `vₙ₋₁ ≤ uₙ`, which by Whitman's condition again leads to
`vₙ₋₁ ≤ uₙ₋₁`; that fails, and the recursion returns to its first application of
the condition and asks whether `vₙ` is below a joinand of `uₙ`, which leads to
`vₙ₋₁ ≤ uₙ₋₁` a second time.  So the recursion decides `vₙ₋₁ ≤ uₙ₋₁` twice to
decide `vₙ ≤ uₙ`, and its cost doubles with `n`, while the pairs of subterms
it asks about grow only linearly.  The table of
[Lattices.Free.Whitman.Polynomial][] decides each pair once.

This module writes the family down over `ℕ` as generators and decides three
members through the table, and one small member through the recursion as a
control on the verdict.  Measured 2026-10-22, one decision per scratch module,
pinned to a performance core under the build's heap cap (`+RTS -M6G -A128M`):
the recursion `_≤ʷ?_`{.AgdaFunction} spent 2.5 s of processor time on
`n = 10` (305 749 calls, as the engine counts them) and exhausted the heap on
`n = 15` (9.8 million calls); the table `_≤ᵖ?_`{.AgdaFunction} decided `n = 5`
to `n = 40` in no measurable time beyond the second and a half its imports take
to load, and `n = 80` in about a quarter of a second more.

<!--
```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module Lattices.Examples.WhitmanTable where

-- Imports from the Agda Standard Library ---------------------------------------
open import Data.Nat.Base                          using ( ℕ ; zero ; suc ; _*_ ; _+_ )
open import Data.Nat.Properties                    using ( _≟_ )
open import Relation.Nullary                       using ( ¬_ )
open import Relation.Nullary.Decidable.Core        using ( from-no )

-- Imports from the agda-lattices library ---------------------------------------
open import Lattices.Free.Term                     using ( LatTerm ; ℊ ; _∧̇_ ; _∨̇_ )
open import Lattices.Free.Whitman                  using ( _≤ʷ_ ; module Decision )
open import Lattices.Free.Whitman.Polynomial       using ( module Decisionᵖ )
```
-->

#### The family

The generators `xᵢ` and `yᵢ` are the even and the odd natural numbers, and
`v`{.AgdaFunction} and `u`{.AgdaFunction} are the book's recursions, with the
meets and joins of three terms nested to the left.

```agda
x y : ℕ → LatTerm ℕ
x i = ℊ (2 * i)
y i = ℊ (2 * i + 1)

v u : ℕ → LatTerm ℕ
v zero     = x 0 ∧̇ x 1
v (suc n)  = x (suc n) ∧̇ x (suc (suc n)) ∧̇ (y (suc n) ∨̇ v n)
u zero     = y 0 ∨̇ y 1
u (suc n)  = y (suc n) ∨̇ y (suc (suc n)) ∨̇ (x (suc n) ∧̇ u n)
```

#### The decisions

In every member of the family `vₙ` is not below `uₙ`, as the book's analysis
says; the three decisions through the table and the control through the
recursion all answer `no`, and `from-no` turns each into the theorem.

```agda
open Decision   _≟_ using ( _≤ʷ?_ )
open Decisionᵖ  _≟_ using ( _≤ᵖ?_ )

v₅≰u₅ : ¬ (v 5 ≤ʷ u 5)
v₅≰u₅ = from-no (v 5 ≤ʷ? u 5)

v₁₀≰u₁₀ : ¬ (v 10 ≤ʷ u 10)
v₁₀≰u₁₀ = from-no (v 10 ≤ᵖ? u 10)

v₂₀≰u₂₀ : ¬ (v 20 ≤ʷ u 20)
v₂₀≰u₂₀ = from-no (v 20 ≤ᵖ? u 20)

v₄₀≰u₄₀ : ¬ (v 40 ≤ʷ u 40)
v₄₀≰u₄₀ = from-no (v 40 ≤ᵖ? u 40)
```
