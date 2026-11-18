import Lightlike.OperatorAlgebras.StoneUnique

/-!
# Task T-OP1-P3

A strongly continuous unitary group is determined by its generator (Stone's theorem, uniqueness).

The statement is `Lightlike.OperatorAlgebras.stone_unique`, at the end of this file. Replace its
`sorry` by a proof and change nothing else in the file: the proof-task check rejects any other
change (CONTRIBUTING.md).

Hint. For `ψ` in the domain, `d/dt (V (-t) U t ψ) = 0`, so `V (-t) U t ψ` is constant; extend by
density of the domain (needs the domain to be invariant under the group).

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

    scripts/context-pack Lightlike.OperatorAlgebras.stone_unique

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

/-- **Stone's theorem, uniqueness**: two strongly continuous one-parameter unitary groups with the same
generator are equal. -/
theorem stone_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U V : UnitaryGroup H} (h : U.generator = V.generator) : U = V := by
  exact UnitaryGroup.eq_of_generator_eq h

end Lightlike.OperatorAlgebras
