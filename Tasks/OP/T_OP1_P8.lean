import Lightlike.OperatorAlgebras.SpectralUnbounded

/-!
# Task T-OP1-P8

The spectral theorem for unbounded self-adjoint operators: every self-adjoint operator has a unique
projection-valued measure whose spectral integral of the identity function is the operator.

The statement is `Lightlike.OperatorAlgebras.spectral_theorem`, at the end of this file.
Replace its `sorry` by a proof and change nothing else in the file: the proof-task check rejects any
other change (CONTRIBUTING.md).

Hint. Through the Cayley transform `U = (A - i)(A + i)⁻¹`, a unitary operator, its spectral measure on the
circle (continuous functional calculus and the Riesz–Markov theorem), transported to `ℝ` along the inverse Cayley
map; uniqueness from the resolvent `⟪ϕ, (A - z)⁻¹ ψ⟫ = ∫ (λ - z)⁻¹ d⟪ϕ, E ψ⟫`.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.OperatorAlgebras.spectral_theorem

## References

Milestone OP1 (Unbounded self-adjoint operators), ROADMAP section "Operator algebras and quantum
information".
Source: G. Teschl, Mathematical Methods in Quantum Mechanics, Graduate Studies in Mathematics 99, AMS (2009), online
edition: the definition of a projection-valued measure (3.5), the integral of an unbounded Borel function (3.25)–(3.27),
and Theorem 3.7 (spectral theorem): "To every self-adjoint operator A there corresponds a unique projection-valued
measure P_A such that A = ∫ λ dP_A(λ)". Read at those locations. Differences from the source, all of representation:
the operator is a Mathlib `LinearPMap` with `IsSelfAdjoint` (`A = A†` with equal domains, the definition of the
source); the projection-valued measure has the fields of (3.5) (a star projection for every set, `0` on non-measurable
sets, `P(ℝ) = 1`, strong `σ`-additivity); `pmapIntegral` is (3.25) and (3.27): the domain `{ψ | ∫ |f|² dμ_ψ < ∞}` and the
limit of the integrals of the truncations. The Lean definitions are ported from physicslib4
(github.com/physicslib/physicslib4, Apache-2.0); the proof of this statement there is
`existsUnique_spectralMeasure_unbounded`.
-/

namespace Lightlike.OperatorAlgebras

theorem spectral_theorem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    ∃! μ : Spectral.ProjectionValuedMeasure ℝ H,
      Spectral.Unbounded.pmapIntegral μ (fun x : ℝ => (x : ℂ)) = A := by
  exact Spectral.Unbounded.existsUnique_spectralMeasure_unbounded hA

end Lightlike.OperatorAlgebras
