import Lightlike.PL.Euler

/-!
# Task T-DT4-P5

The Euler characteristic of a vertex link in a closed combinatorial manifold.

The statement is `Lightlike.PL.SComplex.IsClosedCombManifold.euler_link`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. `isClosedCombManifold_succ_iff` gives that the link is a PL n-sphere; then `IsPLSphere.euler`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.verts`, `PL.SComplex.link`
* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`
* `Lightlike/PL/Euler.lean`: `PL.SComplex.euler`

Lemmas about them, which a proof may use:

* `PL.SComplex.isClosedCombManifold_iff` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.isClosedCombManifold_succ_iff` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.isClosedCombManifold_iff_plHomeomorphic` (`Lightlike/PL/PachnerPL.lean`)
* `PL.SComplex.link_join` (`Lightlike/PL/Boundary.lean`)
* `PL.SComplex.link_exch` (`Lightlike/PL/Exchange.lean`)
* `PL.octahedron_link_of` (`Lightlike/PL/Tests.lean`)
* `PL.SComplex.starAt_weld` (`Lightlike/PL/Stellar.lean`)
* `PL.SComplex.isExch_starAt` (`Lightlike/PL/Exchange.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.IsClosedCombManifold.euler_link

## References

Milestone DT4 (Dynamical triangulations in 3D and 4D on finite triangulations), ROADMAP section
"Dynamical triangulations".
Source: J. Ambjorn, J. Jurkiewicz and R. Loll, Dynamically Triangulating Lorentzian Quantum Gravity,
Nucl.Phys. B610 (2001) 347-382; J. Ambjørn, B. Durhuus and T. Jonsson, Quantum Geometry: A
Statistical Field Theory Approach, Cambridge University Press (1997), Chapter: Gravity in higher
dimensions; R. Loll, Quantum Gravity from Causal Dynamical Triangulations: A Review,
arXiv:1905.08669 (2019) (`ambjorn-jurkiewicz-loll-2001`, `adj-1997`, `loll-2019` in
docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- In a closed combinatorial `(n + 1)`-manifold the link of every vertex has Euler characteristic
`1 + (−1)ⁿ`, that of a PL `n`-sphere. -/
theorem IsClosedCombManifold.euler_link {n : ℕ} {K : SComplex V}
    (hK : IsClosedCombManifold (n + 1) K) {v : V} (hv : v ∈ K.verts) :
    (K.link {v}).euler = 1 + (-1) ^ n := by
  sorry

end SComplex

end Lightlike.PL
