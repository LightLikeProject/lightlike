import Mathlib
import Lightlike.Geometry.HeatKernel.HeatCoeffs
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: all heat-kernel coefficients

Non-vacuity of `Lightlike.exists_heatCoeffs` on the flat line and on Minkowski space: the coefficients exist with
`u₀(0, 0) = 1`, and the transport equation of order `1` holds at the centre `y = 0` of the slice of the base point `0`.
-/

open Set
noncomputable section
namespace Lightlike.HeatCoeffsTests

open Lightlike.LaplaceBeltramiTests

/-- On the line: `u₀(0, 0) = 1` and the transport equations up to order `1` hold on the slice of `0`. -/
example : ∃ (σ : (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ) (u : ℕ → (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ)
    (Ω : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ))), ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ)) ∈ Ω ∧ u 0 (0, 0) = 1 ∧
      IsTransport gLine {y | ((0 : Fin 1 → ℝ), y) ∈ Ω} (fun y => σ (0, y)) (fun k y => u k (0, y)) 1 := by
  obtain ⟨Ω, σ, u, -, h0, -, -, -, -, -, hdiag, htr⟩ := exists_heatCoeffs isCoordMetric_gLine (mem_univ 0)
  exact ⟨σ, u, Ω, h0, (hdiag 0 h0).2, htr 0 1⟩

/-- On Minkowski space (a Lorentzian metric, any dimension): the same, to every order `N`. -/
example (n N : ℕ) : ∃ (σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))), ((0 : Fin n → ℝ), (0 : Fin n → ℝ)) ∈ Ω ∧ u 0 (0, 0) = 1 ∧
      IsTransport ((minkowskiMetric n).coordMetric 0) {y | ((0 : Fin n → ℝ), y) ∈ Ω} (fun y => σ (0, y))
        (fun k y => u k (0, y)) N := by
  obtain ⟨Ω, σ, u, -, h0, -, -, -, -, -, hdiag, htr⟩ :=
    exists_heatCoeffs (minkowski_isCoordMetric (n := n) 0) (mem_univ 0)
  exact ⟨σ, u, Ω, h0, (hdiag 0 h0).2, htr 0 N⟩

end Lightlike.HeatCoeffsTests
