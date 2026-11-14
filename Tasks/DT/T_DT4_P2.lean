import Lightlike.PL.Euler

/-!
# Task T-DT4-P2

Double counting of faces and their cofaces.

The statement is `Lightlike.PL.SComplex.card_mul_eq_sum_cofaces`, at the end of this file. Replace
its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. Count the pairs (σ, s) with σ ⊆ s both ways (`Finset.sum_comm`, `Finset.card_eq_sum_ones`); a
face with k + 2 vertices has k + 2 subsets with k + 1 vertices, all faces (`down_mem`).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`

Lemmas about them, which a proof may use:

* `PL.SComplex.ext` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.down` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.ext_iff` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.mem_faces` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.exch_faces` (`Lightlike/PL/Exchange.lean`)
* `PL.SComplex.StellarEquiv.of_iso` (`Lightlike/PL/Stellar.lean`)
* `PL.SComplex.sum_filter_superset` (`Lightlike/PL/Euler.lean`)
* `PL.SComplex.exists_perm_eq_of_iso` (`Lightlike/PL/Stellar.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.card_mul_eq_sum_cofaces

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

/-- **Double counting.** Each face with `k + 2` vertices has `k + 2` faces with `k + 1` vertices, so
`(k + 2)` times the number of faces with `k + 2` vertices is the sum, over faces `σ` with `k + 1`
vertices, of the number of faces with `k + 2` vertices containing `σ`. -/
theorem card_mul_eq_sum_cofaces (K : SComplex V) (k : ℕ) :
    (k + 2) * #(K.faces.filter fun s => #s = k + 2) =
      ∑ σ ∈ K.faces.filter (fun s => #s = k + 1),
        #(K.faces.filter fun s => σ ⊆ s ∧ #s = k + 2) := by
  sorry

end SComplex

end Lightlike.PL
