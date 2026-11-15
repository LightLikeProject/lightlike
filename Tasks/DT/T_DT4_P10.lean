import Lightlike.PL.Complex

/-!
# Task T-DT4-P10

Trust check: two 4-simplices glued along a 3-face violate 2N₃ = 5N₄.

The statement is `Lightlike.PL.Tasks.twoSimplices_not_dehnSommerville`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. A finite computation; `decide` hits the recursion limit, `decide +kernel` works.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex.faces`, `PL.SComplex.closure`

Lemmas about them, which a proof may use:

* `DynamicalTriangulations.twoSimplices_not_dehnSommerville` (`Lightlike/DynamicalTriangulations/Tests.lean`)
* `PL.SComplex.ext` (`Lightlike/PL/Complex.lean`)
* `PL.closure_bdry` (`Lightlike/PL/Complex3.lean`)
* `PL.isSphere2_iff` (`Lightlike/PL/Surface.lean`)
* `PL.SComplex.down` (`Lightlike/PL/Complex.lean`)
* `PL.verts_closure` (`Lightlike/PL/Surface.lean`)
* `PL.euler_closure` (`Lightlike/PL/Surface.lean`)
* `PL.link_ofComplex3` (`Lightlike/PL/Complex3.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.Tasks.twoSimplices_not_dehnSommerville

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

open Finset Lightlike.PL SComplex

namespace Lightlike.PL.Tasks

/-- **Wrong model.** Two 4-simplices `01234` and `12345` glued along the 3-face `1234` violate the
relation `2N₃ = 5N₄` of closed combinatorial 4-manifolds. -/
theorem twoSimplices_not_dehnSommerville :
    2 * #((closure {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}} : SComplex (Fin 6)).faces.filter
        fun s => #s = 4) ≠
      5 * #((closure {{0, 1, 2, 3, 4}, {1, 2, 3, 4, 5}} : SComplex (Fin 6)).faces.filter
        fun s => #s = 5) := by
  sorry

end Lightlike.PL.Tasks
