import Mathlib
import Lightlike.Geometry.HeatKernel.IsChartParametrix
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: the bundled chart parametrix

Non-vacuity of `Lightlike.exists_isChartParametrix` for the flat metric of the line: the bundle exists at every order,
its cutoff is `1` at the origin and its first coefficient is `1` on the diagonal at the centre.
-/

open Set
noncomputable section
namespace Lightlike.IsChartParametrixTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (N : ℕ) : ∃ r u H Ω θ σ V, IsChartParametrix gLine univ 0 N r u H Ω θ σ V ∧ θ 0 = 1 ∧ u 0 (0, 0) = 1 := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  exact ⟨r, u, H, Ω, θ, σ, V, h, h.θ_one 0 (by simpa using h.r_pos), h.u_zero_diag 0 (by simpa using h.r_pos)⟩

end Lightlike.IsChartParametrixTests
