import Lightlike.PL.Euler

/-!
# Task T-DT4-P1

In a closed combinatorial n-manifold, a face with n vertices lies in exactly two top faces.

The statement is `Lightlike.PL.SComplex.IsClosedCombManifold.card_cofaces`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. The link of the face is a PL 0-sphere (`IsClosedCombManifold.isPLSphere_link`), which has two
vertices (`IsPLSphere.card_verts_zero`); the cofaces correspond to the link's vertices.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/PL/Complex.lean`: `PL.SComplex`, `PL.SComplex.faces`
* `Lightlike/PL/Manifold.lean`: `PL.SComplex.IsClosedCombManifold`

Lemmas about them, which a proof may use:

* `PL.SComplex.mem_faces` (`Lightlike/PL/Complex.lean`)
* `PL.SComplex.chain_sup_mem` (`Lightlike/PL/OrderComplex.lean`)
* `PL.SComplex.pachner_plHomeomorphic` (`Lightlike/PL/PachnerPL.lean`)
* `PL.SComplex.IsClosedCombManifold.card_le` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.link_face` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.two_mul_card_eq` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)
* `PL.SComplex.IsClosedCombManifold.isPLSphere_link` (`Lightlike/PL/Links.lean`)
* `PL.SComplex.IsClosedCombManifold.dehnSommerville` (`Lightlike/DynamicalTriangulations/DehnSommerville.lean`)

Everything they depend on, with 17 more lemmas, in one block:

    scripts/context-pack Lightlike.PL.SComplex.IsClosedCombManifold.card_cofaces

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

/-- In a closed combinatorial `n`-manifold with `1 ≤ n`, every face with `n` vertices lies in
exactly two faces with `n + 1` vertices (the pseudomanifold property). -/
theorem IsClosedCombManifold.card_cofaces {n : ℕ} (hn : 1 ≤ n) {K : SComplex V}
    (hK : IsClosedCombManifold n K) {σ : Finset V} (hσ : σ ∈ K) (hcard : #σ = n) :
    #(K.faces.filter fun s => σ ⊆ s ∧ #s = n + 1) = 2 := by
  sorry

end SComplex

end Lightlike.PL
