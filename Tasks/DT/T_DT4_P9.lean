import Lightlike.PL.Manifold

/-!
# Task T-DT4-P9

Non-vacuity: the boundary of the 5-simplex has N = (6, 15, 20, 15, 6).

The statement is `Lightlike.PL.Tasks.boundary_fin6_dehnSommerville`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. The manifold part is `isClosedCombManifold_boundary`; the counts are a finite computation
(`decide`).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`
* `Lightlike/PL/Complex.lean`: `PL.SComplex.boundary`, `PL.SComplex.faces`

Lemmas about them, which a proof may use:

* `PL.SComplex.exch_faces` (`Lightlike/PL/Exchange.lean`)
* `PL.SComplex.isClosedCombManifold_iff` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.isClosedCombManifold_boundary` (`Lightlike/PL/Manifold.lean`)
* `PL.SComplex.IsClosedCombManifold.link_face` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.bistellarEquiv_of_iso` (`Lightlike/PL/PachnerMain.lean`)
* `PL.ren₁` (`Lightlike/PL/TestsPachner.lean`)
* `PL.oct₂` (`Lightlike/PL/TestsPachner.lean`)
* `PL.oct₁` (`Lightlike/PL/TestsPachner.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.Tasks.boundary_fin6_dehnSommerville

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

/-- **Non-vacuity.** The boundary of the 5-simplex is a closed combinatorial 4-manifold with face
counts `N = (6, 15, 20, 15, 6)`. -/
theorem boundary_fin6_dehnSommerville :
    IsClosedCombManifold 4 (boundary (univ : Finset (Fin 6))) ∧
      (List.range 5).map (fun k => #((boundary (univ : Finset (Fin 6))).faces.filter
        fun s => #s = k + 1)) = [6, 15, 20, 15, 6] := by
  sorry

end Lightlike.PL.Tasks
