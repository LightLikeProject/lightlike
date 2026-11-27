import Mathlib
import Lightlike.Geometry.HeatKernel.HeatCoeffZero
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: the first heat-kernel coefficient

Non-vacuity of `Lightlike.exists_heatCoeff_zero`: its hypotheses hold for the flat line and for Minkowski space (a
Lorentzian coordinate metric on all of `ℝⁿ`), and its conclusion gives a domain containing the diagonal point `(0, 0)`
on which `u₀(0, 0) = 1` and the world function vanishes at `(0, 0)`.
-/

open Set
noncomputable section
namespace Lightlike.HeatCoeffZeroTests

open Lightlike.LaplaceBeltramiTests

/-- On the line: `u₀(0, 0) = 1` and `σ(0, 0) = 0` at the centre. -/
example : ∃ (σ u₀ : (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ), σ (0, 0) = 0 ∧ u₀ (0, 0) = 1 := by
  obtain ⟨Ω, σ, u₀, -, h0, -, -, -, -, hdiag, -⟩ := exists_heatCoeff_zero isCoordMetric_gLine (mem_univ 0)
  exact ⟨σ, u₀, hdiag 0 h0⟩

/-- On Minkowski space (any dimension): the same, for a Lorentzian metric. -/
example (n : ℕ) : ∃ (σ u₀ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ), σ (0, 0) = 0 ∧ u₀ (0, 0) = 1 := by
  obtain ⟨Ω, σ, u₀, -, h0, -, -, -, -, hdiag, -⟩ :=
    exists_heatCoeff_zero (minkowski_isCoordMetric (n := n) 0) (mem_univ 0)
  exact ⟨σ, u₀, hdiag 0 h0⟩

end Lightlike.HeatCoeffZeroTests
