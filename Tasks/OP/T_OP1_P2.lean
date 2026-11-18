import Lightlike.OperatorAlgebras.YosidaLimit

/-!
# Task T-OP1-P2

Every self-adjoint operator generates a strongly continuous unitary group (Stone's theorem,
direction 2).

The statement is `Lightlike.OperatorAlgebras.stone_exists`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. The unbounded spectral theorem (Hall, Chapter 10) and the functional calculus `U t = ∫ e^{i t λ}
   dE(λ)`.
2. The Cayley transform and the spectral theorem for unitaries, or the Hille–Yosida resolvent route.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/UnitaryGroup.lean`: `OperatorAlgebras.UnitaryGroup`,
  `OperatorAlgebras.UnitaryGroup.generator`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.UnitaryGroup.dvec_eq` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.UnitaryGroup.generator_apply` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.phaseGroup_eq_of_generator_eq` (`Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.apply_eq_of_adjoint` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.UnitaryGroup.adjoint_le_generator` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.UnitaryGroup.generator_le_adjoint` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.UnitaryGroup.generator_isSelfAdjoint` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)
* `OperatorAlgebras.UnitaryGroup.hasDerivAt_inner_adjoint` (`Lightlike/OperatorAlgebras/StoneGenerator.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.stone_exists

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

/-- **Stone's theorem, existence**: every self-adjoint operator is the generator of a strongly continuous
one-parameter unitary group.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the
source states `U t = exp (i t A)`, with `exp (i t A)` defined by the spectral theorem; here the group is tied
to `A` through the generator (`U.generator = A`), since `exp (i t A)` is not defined in Mathlib for
unbounded `A`. The two forms are equivalent in the source's setting; this is not proved here. -/
theorem stone_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) : ∃ U : UnitaryGroup H, U.generator = A := by
  exact ⟨stoneGroup hA, generator_stoneGroup hA⟩

end Lightlike.OperatorAlgebras
