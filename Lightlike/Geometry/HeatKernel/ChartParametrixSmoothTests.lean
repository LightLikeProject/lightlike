import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrixSmooth
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: joint smoothness of the chart parametrix

Non-vacuity of `Lightlike.IsChartParametrix.contDiffOn_joint` for the flat metric of the line, at every order: the
parametrix is smooth at `(1, 0, 0)`.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.ChartParametrixSmoothTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (N : ℕ) : ∃ H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ,
    ContDiffAt ℝ ∞ (fun z : ℝ × ((Fin 1 → ℝ) × (Fin 1 → ℝ)) => H z.1 z.2.1 z.2.2) (1, 0, 0) := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  refine ⟨H, (h.contDiffOn_joint isCoordMetric_gLine).contDiffAt ?_⟩
  refine (isOpen_Ioi.prod (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const)).mem_nhds ?_
  exact ⟨show (0 : ℝ) < 1 from one_pos, by simpa using h.r_pos⟩

end Lightlike.ChartParametrixSmoothTests
