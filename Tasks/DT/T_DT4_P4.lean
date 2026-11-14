import Lightlike.PL.Euler

/-!
# Task T-DT4-P4

Summed over the vertices, the face counts of the vertex links.

The statement is `Lightlike.PL.SComplex.sum_card_link`, at the end of this file. Replace its `sorry`
by a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

Hint. A face u of `link {v}` with k + 1 vertices corresponds to the face `insert v u` with k + 2
vertices containing v (`mem_link'`); exchange the sums and use that a face s has

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.verts`, `PL.SComplex.faces`,
  `PL.SComplex.link`

Lemmas about them, which a proof may use:

* `PL.SComplex.link_exch` (`Lightlike/PL/Exchange.lean`)
* `PL.octahedron_link_of` (`Lightlike/PL/Tests.lean`)
* `PL.SComplex.starAt_weld` (`Lightlike/PL/Stellar.lean`)
* `PL.SComplex.link_union_eq` (`Lightlike/PL/PachnerMain.lean`)
* `PL.SComplex.isExch_starAt` (`Lightlike/PL/Exchange.lean`)
* `PL.SComplex.exch_eq_starAt` (`Lightlike/PL/Exchange.lean`)
* `PL.SComplex.link_cone_apex` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.link_join_right` (`Lightlike/PL/Exchange.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.sum_card_link

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

/-- Summed over the vertices `v`, the faces with `k + 1` vertices of the links of `{v}` count each
face of `K` with `k + 2` vertices once per vertex, that is `k + 2` times. -/
theorem sum_card_link (K : SComplex V) (k : ℕ) :
    ∑ v ∈ K.verts, #((K.link {v}).faces.filter fun u => #u = k + 1) =
      (k + 2) * #(K.faces.filter fun s => #s = k + 2) := by
  sorry

end SComplex

end Lightlike.PL
