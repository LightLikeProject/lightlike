import Lightlike.Gauge.Constraints

/-!
# Task T-GC4-P5

The orbit through a zero of the moment map is isotropic.

The statement is `Lightlike.Gauge.orbitDirections_le_momentTangent`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

For a linear action (`b = 0`) with moment zero at `x`, the orbit directions lie in their `σ`-orthogonal: this is the linear Marsden–Weinstein step.

Hint. Souriau's (11.17 d), `AffineSymplecticAction.sigma_vectorField_vectorField`: `σ(Z_E)(Z'_E) = μ[Z, Z'] + f(Z)(Z')`, with `f = 0` for `b = 0` (`cocycle_eq_zero_of_linear`).

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.orbitDirections_le_momentTangent

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Cannas da Silva, The Marsden–Weinstein–Meyer Theorem; Souriau (1970), chapter 11 (`cannas-da-silva-2001` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace

namespace Lightlike.Gauge

theorem orbitDirections_le_momentTangent {E : Type} [AddCommGroup E] [Module ℝ E]
    {g : Type} [LieRing g] [LieAlgebra ℝ g] {σ : LinearMap.BilinForm ℝ E}
    (hσ : IsSymplecticForm σ) (ρ : AffineSymplecticAction σ g) (hb : ρ.b = 0) (x : E)
    (hx : ∀ Z, ρ.moment x Z = 0) :
    orbitDirections ρ x ≤ momentTangent ρ x := by
  sorry

end Lightlike.Gauge
