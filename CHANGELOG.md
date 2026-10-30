<!-- File: CHANGELOG.md -->

# Changelog

The releases of the library, newest first.  The README's section on releases
says how versions are numbered.  Each section lists the modules the release
added, changed and removed, and names the commit of the library's source
repository whose modules `src/` holds, byte for byte.

## v0.2.0 (2026-10-30)

Since v0.1.0.  `src/` holds, byte for byte, the library's 91 modules at commit
`38fa97152304b0fc12091e912374cb416a5a3b81` of its source repository.

+  **Added** (10): `Lattices.DirectLimit`, `Lattices.DirectLimit.Union`,
   `Lattices.Free.Canonical.LeastRank`, `Lattices.Free.Extrema`,
   `Lattices.Free.FJN`, `Lattices.Free.Membership`, `Lattices.Free.Prime`,
   `Lattices.Free.Small`, `Lattices.Prime`, `Lattices.Sublattice`.
+  **Changed** (14): `Lattices.Breadth`, `Lattices.Free`,
   `Lattices.Free.Canonical`, `Lattices.Free.Canonical.JoinIrreducible`,
   `Lattices.Free.Countable`, `Lattices.Free.Embedding`,
   `Lattices.Free.FixedPointFree`, `Lattices.Free.Generation`,
   `Lattices.Free.Semidistributive`, `Lattices.Free.Universal`,
   `Lattices.Free.WhitmanChains`, `Lattices.Generation`, `Lattices.Nation`,
   `Lattices.Semidistributive.FiniteJoins`.
+  **Removed**: none.

## v0.1.0 (2026-10-28)

The first release.  `src/` holds, byte for byte, the library's 81 modules at
commit `1d1607dd633d75042ef49700749578725fea3df2` of its source repository.
The README lists them.

This is the library as it stood when releases began: the modules of its setup
(pull request 1), the lattice theory moved from the Agda Universal Algebra
Library (pull request 4), that library pinned at commit `b4d0ab6c`, and the
documentation site (pull request 7).
