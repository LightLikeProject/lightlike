import Lightlike.OperatorAlgebras.MomentumDeficiency

/-!
# Task T-OP1-P5

On L²[0,1], -i d/dx without boundary conditions has deficiency indices (1,1).

The statement is `Lightlike.OperatorAlgebras.momentumMin_deficiency`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. The adjoint of -i d/dx on C_c^∞(0,1) is -i d/dx on H¹(0,1) (weak derivative); ker(A† ∓ i) is
spanned by exp(∓x), found by solving the ODE for an absolutely continuous function; density of
C_c^∞(0,1) in L²(0,1) (Mathlib: density of compactly supported smooth functions in Lp).

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/MomentumInterval.lean`: `OperatorAlgebras.L2I`,
  `OperatorAlgebras.momentumMin`
* `Lightlike/OperatorAlgebras/Deficiency.lean`: `OperatorAlgebras.deficiencyDim`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.momentumMin_graph` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_add` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_zero` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_smul` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.classI_congr` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.momentumPair_add` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.momentumPair_smul` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)
* `OperatorAlgebras.momentumGraph_fun` (`Lightlike/OperatorAlgebras/MomentumInterval.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.momentumMin_deficiency

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
Source: B. C. Hall, Quantum Theory for Mathematicians, Graduate Texts in Mathematics 267, Springer
(2013), Chapter: Unbounded Self-Adjoint Operators; B. C. Hall, Quantum Theory for Mathematicians,
Graduate Texts in Mathematics 267, Springer (2013), Chapter: The Spectral Theorem for Unbounded
Self-Adjoint Operators (`hall-2013`, `hall-2013` in docs/tasks/sources.yaml).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

namespace Lightlike.OperatorAlgebras

/-- **Deficiency indices of `-i d/dx` on `L²[0, 1]`**: the operator `momentumMin` (`-i d/dx` on the `C²`
functions supported inside `(0, 1)`, no boundary condition) is densely defined and both its deficiency
spaces, the kernels of `A† - i` and `A† + i`, are one-dimensional. (The kernel of `A† ∓ i` is spanned by
`x ↦ exp (∓ x)`, which lies in the domain `H¹(0, 1)` of the adjoint.)

**Differences from the source** (not yet read at the cited location; the comparison is pending): the
milestone's operator `-i d/dx` on `L²[0, 1]` without boundary conditions is stated here as the operator on
`C²` functions with compact support inside `(0, 1)`, not on `C_c^∞(0, 1)`; both have the same closure, which
is not proved here, so the adjoint and the deficiency indices agree only if that is shown. `L²[0, 1]` is
`L²(0, 1)`, the endpoints being null sets. The difference is of kind representation, approved by the
owner, 17 November 2026; the equality of the two closures becomes a separate task, and until it is proved
this result counts as weaker. -/
theorem momentumMin_deficiency :
    Dense (momentumMin.domain : Set L2I) ∧ deficiencyDim momentumMin Complex.I = 1 ∧
      deficiencyDim momentumMin (-Complex.I) = 1 := by
  exact deficiency_indices_momentumMin

end Lightlike.OperatorAlgebras
