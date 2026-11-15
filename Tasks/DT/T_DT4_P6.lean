import Lightlike.PL.Euler

/-!
# Task T-DT4-P6

The Euler characteristic as an alternating sum of face counts.

The statement is `Lightlike.PL.SComplex.euler_eq_sum_card`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Split the sum defining `euler` by the number of vertices (`Finset.sum_fiberwise_of_maps_to`);
every nonempty face has between 1 and `maxCard` vertices (`card_le_maxCard`).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`
* `Lightlike/PL/Euler.lean`: `PL.SComplex.euler`
* `Lightlike/PL/Invariants.lean`: `PL.SComplex.maxCard`

Lemmas about them, which a proof may use:

* `PL.SComplex.euler_eq_sum_range` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.euler_eq_card_verts` (`Lightlike/PL/Euler.lean`)
* `PL.SComplex.ext` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.down` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.ext_iff` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.mem_faces` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.maxCard_le` (`Lightlike/PL/Invariants.lean`)
* `PL.SComplex.exch_faces` (`Lightlike/PL/Exchange.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.euler_eq_sum_card

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

/-- The Euler characteristic is the alternating sum `N₀ − N₁ + N₂ − ⋯` of the numbers `N_k` of faces
with `k + 1` vertices. -/
theorem euler_eq_sum_card (K : SComplex V) :
    K.euler = ∑ k ∈ range K.maxCard, (-1 : ℤ) ^ k * #(K.faces.filter fun s => #s = k + 1) := by
  sorry

end SComplex

end Lightlike.PL
