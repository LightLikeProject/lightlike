import Lightlike.OperatorAlgebras.Semigroup.Generation

/-!
# Task T-OP1-P7

The Hille–Yosida generation theorem for contraction semigroups: a densely defined operator `A` on a
Banach space such that `λ - A` is bounded below by `λ` and surjective for every `λ > 0` is the
generator of a strongly continuous semigroup of contractions.

The statement is `Lightlike.OperatorAlgebras.hilleYosida_contraction_generation`, at the end of this
file. Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects
any other change (CONTRIBUTING.md).

Hint. The Yosida approximation: with `R(λ) = (λ - A)⁻¹` the operators `Y_λ = λ² R(λ) - λ` are bounded,
`exp (t Y_λ)` are contractions, `Y_λ x → A x` on the domain of `A`, and `exp (t Y_λ)` converges to the
semigroup, whose generator contains `A`; a contraction generator is dissipative, so it equals `A`.

## What the statement uses

Definitions the statement names (without the `Lightlike.` prefix), by file:

* `Lightlike/OperatorAlgebras/Semigroup/Defs.lean`: `OperatorAlgebras.ContractionSemigroup`,
  `OperatorAlgebras.ContractionSemigroup.generator`

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
Source: Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4, Theorem 1.9
(https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf).
Lock and dependencies: `docs/tasks/tasks.yaml`. This header is written by `scripts/tasks.py deps`
from the plan, the sources and the library.
-/

open scoped LinearPMap

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- **The Hille–Yosida generation theorem for contraction semigroups.** If `A` has dense domain and,
for every `λ > 0`, `λ - A` is bounded below by `λ` and surjective, then `A` is the generator of a
strongly continuous semigroup of contractions.

Source: the Math 7334 lecture notes (Georgia Tech, Spring 2017), Section 4, Theorem 1.9: "A closed operator
`A` is the generator of a contraction semi group if and only if `(0, ∞) ⊂ ρ(A)` and `‖R_λ(A)‖ ≤ 1/λ`,
`λ > 0`." Differences from the source, as approved by the maintainers on 18 November 2026:
representation (kind: representation): the hypotheses are bounded below by `λ` and surjective in place of
"closed, `(0, ∞) ⊂ ρ(A)` and `‖R_λ(A)‖ ≤ 1/λ`" (equivalent: bounded below and surjective is `λ - A`
bijective with an inverse of norm at most `λ⁻¹`, and a bounded inverse makes `A` closed); density of the
domain is a hypothesis, which the source's Lemma 1.6 and its proof of Theorem 1.9 assume (kind:
convention). The source states an equivalence; this theorem is the direction "the hypotheses imply that `A`
generates", and the converse is `contractionSemigroup_generator_hypotheses` in
`Lightlike/OperatorAlgebras/Semigroup/Converse.lean`, which together give `hilleYosida_contraction`. -/
theorem hilleYosida_contraction_generation (A : X →ₗ.[𝕜] X) (hdense : Dense (A.domain : Set X))
    (hdiss : ∀ l : ℝ, 0 < l → ∀ x : A.domain, l * ‖(x : X)‖ ≤ ‖(l : 𝕜) • (x : X) - A x‖)
    (hsurj : ∀ l : ℝ, 0 < l → ∀ y : X, ∃ x : A.domain, (l : 𝕜) • (x : X) - A x = y) :
    ∃ S : ContractionSemigroup 𝕜 X, S.generator = A := by
  exact hille_yosida_generation A hdense hdiss hsurj

end Lightlike.OperatorAlgebras
