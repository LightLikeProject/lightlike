import Lightlike.Spacetime.CoordKilling
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# `∂_t` is a Killing field of the exterior Schwarzschild metric

`schwarzschild_killing`: on the manifold layer, for the Levi-Civita connection of `schwarzschildMetric M hM`, the coordinate field `∂_t`
of every chart is a Killing field at every point of the chart domain. The metric components `schMetric M` do not depend on `t`
(`pd_schD`), and in every chart the components are `schMetric M` (`schwarzschild_coordMetric`), so `coordField_killing` applies.

**Limits.** The exterior region `r > 2M`, `0 < θ < π` (the manifold `schOpen`); statement for any Levi-Civita connection.

Compared with Carroll, *Lecture Notes on General Relativity* (gr-qc/9712019), ch. 7, pp. 173-174: "four Killing vectors: three for the
spherical symmetry, and one for time translations", "the timelike Killing vector K = ∂_t", eq. (7.41): match for `∂_t`; the three
rotation Killing fields are not covered.
-/

open Bundle Manifold Set VectorField TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable (M : ℝ) (hM : 0 < M)

/-- **`∂_t` is a Killing field of exterior Schwarzschild.** -/
theorem schwarzschild_killing (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (schOpen M hM))
    (h : cov.IsLeviCivita (schwarzschildMetric M hM).toNondegMetric) (x₀ : schOpen M hM) {p : schOpen M hM}
    (hp : p ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).source) :
    IsKillingAt cov (schwarzschildMetric M hM).toNondegMetric (coordField x₀ 0) p := by
  refine coordField_killing (schwarzschildMetric M hM).toNondegMetric x₀ cov h 0 ?_ hp
  intro y hy a b
  have hyU := target_subset_schU M hM x₀ hy
  have hreg := schU_subset M hM hyU
  have hev : (fun z => (schwarzschildMetric M hM).toNondegMetric.coordMetric x₀ z a b) =ᶠ[nhds y] fun z => schMetric M z a b := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) x₀).mem_nhds hy] with z hz
    rw [schwarzschild_coordMetric M hM x₀ hz]
  rw [pd_congr hev]
  have hr : 0 < y 1 := by linarith [hyU.1, hM]
  have h1 : y 1 ≠ 0 := hr.ne'
  have h2 : 1 - 2 * M / y 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h'
    have : 2 * M / y 1 < 1 := by rw [div_lt_one hr]; linarith [hyU.1]
    linarith
  by_cases hab : a = b
  · subst hab
    have := pd_schD M h1 h2 0 a
    simp only [schMetric, Matrix.diagonal_apply_eq]
    rw [this]
    fin_cases a <;> simp [schDD]
  · have : (fun z => schMetric M z a b) = fun _ => 0 := by
      funext z; simp [schMetric, Matrix.diagonal_apply_ne _ hab]
    rw [this]; simp [pd]

end Lightlike
