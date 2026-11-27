import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrix

/-!
# The properties of the parametrix in a chart, bundled

`Lightlike.IsChartParametrix g U x N r u H Ω θ σ V` (defined in `Lightlike.Geometry.HeatKernel.ChartParametrix`) collects everything `Lightlike.exists_chart_parametrix` proves about
the cut-off parametrix `H(t, p, y) = θ(y − p) (4πt)^{-n/2} e^{-σ(p, y)/4t} Σ_{k ≤ N} tᵏ u_k(p, y)` of a Riemannian
coordinate metric `g` on `U` near `x`: the diagonal, the Gaussian and integral bounds, the heat error bound, the
structure (domain `Ω`, cutoff `θ`, world function `σ = g_p(V, V)`, coefficients `u_k`) and the expanded heat error.
`Lightlike.exists_isChartParametrix` restates the existence theorem in this form, so that later properties (the delta
property, derivative bounds of the heat error) can be proved from the bundle.
-/

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The parametrix in a chart exists**, with all its properties bundled. -/
theorem exists_isChartParametrix {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (N : ℕ) :
    ∃ r u H Ω θ σ V, IsChartParametrix g U x N r u H Ω θ σ V := by
  obtain ⟨r, u, Ω, θ, σ, V, h⟩ := exists_chart_parametrix_uniform hg hx
  obtain ⟨H, hH⟩ := h N
  exact ⟨r, u, H, Ω, θ, σ, V, hH⟩

end Lightlike
