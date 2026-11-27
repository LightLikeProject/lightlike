import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrix
import Lightlike.Spacetime.LaplaceBeltrami.Tests

/-!
# Tests: the parametrix in a chart

Non-vacuity of `Lightlike.exists_chart_parametrix` for the flat (Riemannian) metric of the line, at every order `N`:
a cut-off parametrix exists whose diagonal at the centre is `(4πt)^{-1/2} Σ tᵏ u_k(0, 0)` with `u₀(0, 0) = 1`, and
whose heat error is `O(t^{N − 1/2})` uniformly near `0`.
-/

open Set
noncomputable section
namespace Lightlike.ChartParametrixTests

open Lightlike.LaplaceBeltramiTests

/-- The flat metric of the line is Riemannian (in the form of the geodesic-expansion layer). -/
theorem isRiemMetric_gLine : Upstream.GeodesicExpansion.IsRiemMetric gLine univ :=
  ⟨⟨isOpen_univ, isCoordMetric_gLine.symm, isCoordMetric_gLine.isUnit_det, isCoordMetric_gLine.smooth⟩,
    fun _ _ => Matrix.PosDef.one⟩

/-- Non-vacuity: on the line, at the centre, `u₀ = 1` and the heat error bound holds, for every order. -/
example (N : ℕ) : ∃ (r : ℝ) (u : ℕ → (Fin 1 → ℝ) × (Fin 1 → ℝ) → ℝ) (H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ),
    0 < r ∧ u 0 (0, 0) = 1 ∧ ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, ∃ D, HasDerivAt (fun s => H s 0 y) D t ∧
      |D + coordLaplacian gLine (H t 0) y| ≤ C * t ^ ((N : ℝ) - (1 : ℕ) / 2) := by
  obtain ⟨r, u, H, hr, hu0, -, -, C, hC⟩ := exists_chart_parametrix isRiemMetric_gLine (mem_univ 0) N
  exact ⟨r, u, H, hr, hu0 0 (by simpa using hr), C, fun t ht y => hC t ht 0 (by simpa using hr) y⟩

end Lightlike.ChartParametrixTests
