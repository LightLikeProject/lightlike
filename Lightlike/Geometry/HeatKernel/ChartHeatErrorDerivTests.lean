import Mathlib
import Lightlike.Geometry.HeatKernel.ChartHeatErrorDeriv
import Lightlike.Geometry.HeatKernel.ChartParametrixTests

/-!
# Tests: derivative bounds of the heat error of the chart parametrix

Non-vacuity of `Lightlike.IsChartParametrix.heatError_deriv_le` for the flat metric of the line, at every order `N`
and every derivative order `ℓ`: the bound `C t^{N − 1/2 − ℓ}` holds at the centre. Trust check of
`exists_bound_iteratedFDerivWithin_poly` for the constant coefficients `β_k = 1`.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.ChartHeatErrorDerivTests

open Lightlike.LaplaceBeltramiTests Lightlike.ChartParametrixTests

example (N ℓ : ℕ) : ∃ H : ℝ → (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ, ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
    ‖iteratedFDeriv ℝ ℓ (fun q : (Fin 1 → ℝ) × (Fin 1 → ℝ) =>
      deriv (fun s => H s q.1 q.2) t + coordLaplacian gLine (H t q.1) q.2) ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ))‖ ≤
      C * t ^ ((N : ℝ) - (1 : ℕ) / 2 - ℓ) := by
  obtain ⟨r, u, H, Ω, θ, σ, V, h⟩ := exists_isChartParametrix isRiemMetric_gLine (mem_univ 0) N
  obtain ⟨C, -, hC⟩ := h.heatError_deriv_le isCoordMetric_gLine (half_lt_self h.r_pos) ℓ
  exact ⟨H, C, fun t ht => hC t ht _ (by simp; exact (half_pos h.r_pos).le)⟩

example (N ℓ : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ≤ ℓ, ∀ q ∈ Icc (0 : ℝ) 1,
    ‖iteratedFDerivWithin ℝ i (fun q : ℝ => ∑ k ∈ Finset.range (N + 1), t ^ k * (fun _ _ => (1 : ℝ)) k q) univ q‖ ≤
      M :=
  exists_bound_iteratedFDerivWithin_poly uniqueDiffOn_univ (fun _ => contDiffOn_const) isCompact_Icc
    (subset_univ _) N ℓ

end Lightlike.ChartHeatErrorDerivTests
