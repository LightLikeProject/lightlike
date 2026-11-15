import Tasks.DT.T_DT4_P4
import Tasks.DT.T_DT4_P5
import Tasks.DT.T_DT4_P6

/-!
# Task T-DT4-P7

In a closed combinatorial 4-manifold, 2N₁ − 3N₂ + 4N₃ − 5N₄ = 0.

The statement is `Lightlike.PL.SComplex.IsClosedCombManifold.dehnSommerville_link`, at the end of
this file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md). It builds on T-DT4-P4 (`PL.SComplex.sum_card_link`),
T-DT4-P5 (`PL.SComplex.IsClosedCombManifold.euler_link`) and T-DT4-P6
(`PL.SComplex.euler_eq_sum_card`): a proof may use their statements.

Hint. Sum T-DT4-P5 (n = 3, each link has Euler characteristic 0) over the vertices, expand each
link's Euler characteristic by T-DT4-P6 (links have `maxCard` 4 by `IsPLSphere.maxCard`) and regroup
by T-DT4-P4.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`
* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`

Lemmas about them, which a proof may use:

* `PL.SComplex.sum_card_link` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.IsClosedCombManifold.euler_link` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.euler_eq_sum_card` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.euler_eq_sum_range` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.euler_eq_card_verts` (`Lightlike/PL/Euler.lean`)
* `PL.SComplex.isClosedCombManifold_iff` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.isClosedCombManifold_succ_iff` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.IsClosedCombManifold.dehnSommerville3` (`Lightlike/DynamicalTriangulations/DehnSommerville3.lean`)

Everything they depend on, with 20 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.IsClosedCombManifold.dehnSommerville_link

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

/-- In a closed combinatorial 4-manifold, `2N₁ − 3N₂ + 4N₃ − 5N₄ = 0`, where `N_k` is the number of
faces with `k + 1` vertices: the vertex links are PL 3-spheres, of Euler characteristic 0. -/
theorem IsClosedCombManifold.dehnSommerville_link {K : SComplex V} (hK : IsClosedCombManifold 4 K) :
    2 * (#(K.faces.filter fun s => #s = 2) : ℤ) - 3 * #(K.faces.filter fun s => #s = 3) +
      4 * #(K.faces.filter fun s => #s = 4) - 5 * #(K.faces.filter fun s => #s = 5) = 0 := by
  sorry

end SComplex

end Lightlike.PL
