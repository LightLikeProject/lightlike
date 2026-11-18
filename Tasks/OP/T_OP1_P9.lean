import Lightlike.OperatorAlgebras.Semigroup.Generation

/-!
# Task T-OP1-P9

The converse of the Hille–Yosida generation theorem for contraction semigroups: the generator of a
strongly continuous semigroup of contractions on a Banach space has dense domain, and `λ - A` is
bounded below by `λ` and surjective for every `λ > 0`.

The statement is `Lightlike.OperatorAlgebras.contractionSemigroup_generator_hypotheses`, at the end
of this file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task
check rejects any other change (CONTRIBUTING.md).

Hint. Dissipativity: `‖(λ + t⁻¹) x - t⁻¹ S t x‖ ≥ λ ‖x‖` and let `t → 0` (this is
`ContractionSemigroup.norm_dissip`). Density: `t⁻¹ ∫₀ᵗ S s x ds` lies in the domain and converges to
`x`. Surjectivity: the resolvent is the Laplace transform `∫₀^∞ e^{-λ t} S t y dt` (Bochner integral);
it maps into the domain of the generator and inverts `λ - A`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Semigroup/Defs.lean`: `OperatorAlgebras.ContractionSemigroup`,
  `OperatorAlgebras.ContractionSemigroup.generator`

Lemmas about them, which a proof may use:

* `OperatorAlgebras.ContractionSemigroup.norm_dissip` (`Lightlike/OperatorAlgebras/Semigroup/Generation.lean`)

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
Source: Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4, Theorem 1.3 (the domain of
the generator is dense and the generator is closed) and Theorem 1.9
(https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open scoped LinearPMap

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- **The generator of a contraction semigroup satisfies the hypotheses of the Hille–Yosida
theorem**: dense domain, `λ - A` bounded below by `λ` and surjective for every `λ > 0`. (The other
half of the Hille–Yosida equivalence, with `hilleYosida_contraction_generation`.) -/
theorem contractionSemigroup_generator_hypotheses (S : ContractionSemigroup 𝕜 X) :
    Dense (S.generator.domain : Set X) ∧
    (∀ l : ℝ, 0 < l → ∀ x : S.generator.domain,
      l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - S.generator x‖) ∧
    (∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : S.generator.domain,
      (l : 𝕜) • (x : X) - S.generator x = y) := by
  sorry

end Lightlike.OperatorAlgebras
