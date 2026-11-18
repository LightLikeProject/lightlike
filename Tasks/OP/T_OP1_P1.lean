import Lightlike.OperatorAlgebras.StoneGenerator

/-!
# Task T-OP1-P1

The generator of a strongly continuous unitary group is self-adjoint (Stone's theorem, direction 1).

The statement is `Lightlike.OperatorAlgebras.stone_generator_isSelfAdjoint`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check
rejects any other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Show `A` is closed, densely defined (domain is invariant and mollified vectors lie in it) and
   symmetric, then `ran (A ± i) = H` by the integral `∫₀^∞ e^{-t} U (∓ t) ψ dt` (Hall, Chapter 10,
   the proof of Stone's theorem).
2. Reed–Simon I, Chapter VIII (Stone's theorem).

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/UnitaryGroup.lean`: `OperatorAlgebras.UnitaryGroup`,
  `OperatorAlgebras.UnitaryGroup.generator`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.UnitaryGroup.ext` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.mk.inj` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.phaseGroup_generator` (`Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.ext_iff` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.mk.injEq` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.map_add'` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.UnitaryGroup.map_zero'` (`Lightlike/OperatorAlgebras/UnitaryGroup.lean`)
* `OperatorAlgebras.phaseGroup_generator_ne` (`Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.stone_generator_isSelfAdjoint

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

/-- **Stone's theorem, generator is self-adjoint**: the generator of a strongly continuous one-parameter
unitary group (`A ψ = -i d/dt U t ψ` at `0`) is a self-adjoint operator.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the group
is a structure with the generator defined from it, while in the usual statement of Stone's theorem the
generator is the operator `A` with `U t = exp (i t A)`; here `A` is given by `-i d/dt` on the vectors where
the derivative exists. -/
theorem stone_generator_isSelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : UnitaryGroup H) : IsSelfAdjoint U.generator := by
  exact UnitaryGroup.generator_isSelfAdjoint U

end Lightlike.OperatorAlgebras
