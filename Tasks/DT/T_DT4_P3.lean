import Tasks.DT.T_DT4_P1
import Tasks.DT.T_DT4_P2

/-!
# Task T-DT4-P3

In a closed combinatorial n-manifold, 2 N_{n-1} = (n + 1) N_n (for n = 4, 2N₃ = 5N₄).

The statement is `Lightlike.PL.SComplex.IsClosedCombManifold.two_mul_card_eq`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md). It builds on T-DT4-P1
(`PL.SComplex.IsClosedCombManifold.card_cofaces`) and T-DT4-P2
(`PL.SComplex.card_mul_eq_sum_cofaces`): a proof may use their statements.

Hint. Apply T-DT4-P2 with k = n − 1 and rewrite every summand by T-DT4-P1.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`
* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`

Lemmas about them, which a proof may use:

* `PL.SComplex.IsClosedCombManifold.card_cofaces` (`Tasks/DT/T_DT4_P1.lean`)
* `PL.SComplex.card_mul_eq_sum_cofaces` (`Tasks/DT/T_DT4_P2.lean`)
* `PL.SComplex.mem_faces` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.IsClosedCombManifold.card_le` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.link_face` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.isPLSphere_link` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.bistellarEquiv_of_iso` (`Lightlike/PL/PachnerMain.lean`)
* `PL.SComplex.ext` (`Lightlike/PL/Complex.lean`)

Everything they depend on, with 19 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.IsClosedCombManifold.two_mul_card_eq

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

/-- In a closed combinatorial `n`-manifold with `1 ≤ n`, twice the number of faces with `n` vertices
equals `n + 1` times the number of faces with `n + 1` vertices. For `n = 4`: `2N₃ = 5N₄`. -/
theorem IsClosedCombManifold.two_mul_card_eq {n : ℕ} (hn : 1 ≤ n) {K : SComplex V}
    (hK : IsClosedCombManifold n K) :
    2 * #(K.faces.filter fun s => #s = n) = (n + 1) * #(K.faces.filter fun s => #s = n + 1) := by
  sorry

end SComplex

end Lightlike.PL
