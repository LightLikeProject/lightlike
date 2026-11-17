import Lightlike.OperatorAlgebras.GeneratorTranslation

/-!
# Task T-OP1-P4

The C² functions with compact support are a core of the generator of the translation group on L²(ℝ).

The statement is `Lightlike.OperatorAlgebras.translationGroup_core`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Routes, each welcome as a separate attempt:

1. Mollification: for ψ in the domain, ψ * ρ_ε is smooth and tends to ψ with its derivative;
   truncate by a cutoff and use that the generator commutes with convolution (Hall, Chapter 10).
2. A dense invariant subspace of the domain is a core (Reed–Simon I, Chapter VIII, on cores); the C²
   compactly supported functions are invariant under translation.

Partial results, as helper lemmas in separate pull requests, are welcome.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Translation.lean`: `OperatorAlgebras.L2R`,
  `OperatorAlgebras.translationGroup`
* `Lightlike/OperatorAlgebras/UnitaryGroup.lean`: `OperatorAlgebras.UnitaryGroup.generatorDomain`,
  `OperatorAlgebras.UnitaryGroup.generator`
* `Lightlike/OperatorAlgebras/GeneratorTranslation.lean`: `OperatorAlgebras.ofCS`,
  `OperatorAlgebras.continuous_deriv_of_two`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.translationGroup_generator_ne` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.translationGroup_generator_ofCS` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.error_eq` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.translationGroup_hasDerivAt` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.translate_ofCS` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.exists_core_ne_zero` (`Lightlike/OperatorAlgebras/GeneratorTranslation.lean`)
* `OperatorAlgebras.phaseGroup_domain` (`Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean`)
* `OperatorAlgebras.phaseGroup_generator` (`Lightlike/OperatorAlgebras/TestsUnitaryGroup.lean`)

Everything they depend on, and the further lemmas about them, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.translationGroup_core

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

open MeasureTheory Filter Topology

namespace Lightlike.OperatorAlgebras

/-- **A core of the momentum operator**: every vector `ψ` of the domain of the generator of the translation
group on `L²(ℝ)` is a limit of classes `ψₙ` of `C²` functions with compact support such that the generators
`-i ψₙ'` converge to the generator of `ψ`; so the closure of `-i d/dx` on these functions is the generator,
which is self-adjoint (Stone's theorem), and `-i d/dx` is essentially self-adjoint there.

**Differences from the source** (not yet read at the cited location; the comparison is pending): the
milestone's statement is for `C_c^∞(ℝ)`; the core is stated here for `C²` functions with compact support,
the class on which the derivative of the group is proved. -/
theorem translationGroup_core (ψ : L2R) (hψ : ψ ∈ translationGroup.generatorDomain) :
    ∃ (f : ℕ → ℝ → ℂ) (hf : ∀ n, ContDiff ℝ 2 (f n)) (hc : ∀ n, HasCompactSupport (f n)),
      Tendsto (fun n => ofCS (hf n).continuous (hc n)) atTop (𝓝 ψ) ∧
      Tendsto (fun n => ofCS (continuous_deriv_of_two (hf n)) (hc n).deriv) atTop
        (𝓝 (Complex.I • translationGroup.generator ⟨ψ, hψ⟩)) := by
  sorry

end Lightlike.OperatorAlgebras
