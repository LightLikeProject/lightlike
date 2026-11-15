import Tasks.DT.T_DT4_P3
import Tasks.DT.T_DT4_P7

/-!
# Task T-DT4-P8

The Dehn–Sommerville relation 2N₁ − 3N₂ + 6N₃ − 10N₄ = 0 for closed combinatorial 4-manifolds.

The statement is `Lightlike.PL.SComplex.IsClosedCombManifold.dehnSommerville`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md). It builds on T-DT4-P3
(`PL.SComplex.IsClosedCombManifold.two_mul_card_eq`) and T-DT4-P7
(`PL.SComplex.IsClosedCombManifold.dehnSommerville_link`): a proof may use their statements.

Hint. Add `2N₃ − 5N₄ = 0` (T-DT4-P3 with n = 4, cast to ℤ) to T-DT4-P7; `linarith` or `omega` after
`push_cast`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`
* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`

Lemmas about them, which a proof may use:

* `PL.SComplex.IsClosedCombManifold.two_mul_card_eq` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.IsClosedCombManifold.dehnSommerville_link` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.IsClosedCombManifold.card_cofaces` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.IsClosedCombManifold.dehnSommerville3` (`Lightlike/DynamicalTriangulations/DehnSommerville3.lean`)
* `PL.SComplex.IsClosedCombManifold.dehnSommerville3_link` (`Lightlike/DynamicalTriangulations/DehnSommerville3.lean`)
* `PL.SComplex.IsClosedCombManifold.bistellarEquiv_of_iso` (`Lightlike/PL/PachnerMain.lean`)
* `PL.SComplex.ext` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.down` (`Lightlike/PL/Complex.lean`)

Everything they depend on, with 19 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.IsClosedCombManifold.dehnSommerville

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

/-- **Dehn–Sommerville relation** for closed combinatorial 4-manifolds:
`2N₁ − 3N₂ + 6N₃ − 10N₄ = 0`, where `N_k` is the number of faces with `k + 1` vertices. -/
theorem IsClosedCombManifold.dehnSommerville {K : SComplex V} (hK : IsClosedCombManifold 4 K) :
    2 * (#(K.faces.filter fun s => #s = 2) : ℤ) - 3 * #(K.faces.filter fun s => #s = 3) +
      6 * #(K.faces.filter fun s => #s = 4) - 10 * #(K.faces.filter fun s => #s = 5) = 0 := by
  sorry

end SComplex

end Lightlike.PL
