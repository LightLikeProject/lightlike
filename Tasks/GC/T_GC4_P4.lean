import Lightlike.Gauge.Constraints

/-!
# Task T-GC4-P4

Dimension of the level set of a linear moment map.

The statement is `Lightlike.Gauge.finrank_orbit_add_momentTangent`, at the end of this file. Replace its `sorry` by
a proof and change nothing else in the file: the proof-task check rejects any other change
(CONTRIBUTING.md).

For a non-degenerate alternating `σ` on a finite-dimensional `E`, `dim (orbit directions) + dim (σ-orthogonal) = dim E`.

Hint. `LinearMap.BilinForm.finrank_add_finrank_orthogonal` for a non-degenerate form.

## What the statement uses

Everything the statement depends on, in one block:

    scripts/context-pack Lightlike.Gauge.finrank_orbit_add_momentTangent

## References

Milestone GC4 (constrained Hamiltonian systems), ROADMAP section "Gauge theory and constrained systems".
Source: Cannas da Silva, Lectures on Symplectic Geometry, The Marsden–Weinstein–Meyer Theorem (`cannas-da-silva-2001` in docs/tasks/sources.yaml).
-/

open ClassicalMechanics InnerProductSpace

namespace Lightlike.Gauge

theorem finrank_orbit_add_momentTangent {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    {g : Type} [LieRing g] [LieAlgebra ℝ g] {σ : LinearMap.BilinForm ℝ E}
    (hσ : IsSymplecticForm σ) (ρ : AffineSymplecticAction σ g) (x : E) :
    Module.finrank ℝ (orbitDirections ρ x) + Module.finrank ℝ (momentTangent ρ x) =
      Module.finrank ℝ E := by
  sorry

end Lightlike.Gauge
