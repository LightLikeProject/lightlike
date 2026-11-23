import Lightlike.Upstream.GeodesicExpansion.DistMid
import Lightlike.Upstream.GeodesicExpansion.Riemannian
import Mathlib

/-!
# Expansion of the squared Riemannian distance to fifth order (Mathlib form)

For an open `U ⊆ ℝⁿ` and a Riemannian coordinate metric `g` on `U` (`IsRiemMetric g U`), the
tangent bundle of the manifold `U` becomes a Riemannian bundle (`IsRiemMetric.riemannianBundle`),
and Mathlib's `riemannianEDist` is the distance of `g`. This file restates the two expansions of
the squared distance in terms of Mathlib's `riemannianEDist`:

* `IsRiemMetric.riemannianEDist_sq_expansion`: `d(x, y)² = F_x(y - x) + O(‖y - x‖⁵)`, uniformly
  for `x` in a compact `K ⊆ U`, with `F_x` the quartic jet `distJet`.
* `IsRiemMetric.riemannianEDist_sq_expansion_midpoint`: the same about the midpoint
  `m = (x + y)/2`, `d(x, y)² = midJet g m (y - x) + O(‖y - x‖⁵)`; no cubic term appears.
-/

open Matrix Set Filter Topology Metric MeasureTheory Manifold Bundle
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Upstream.GeodesicExpansion

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  {U : TopologicalSpace.Opens (Fin n → ℝ)}

/-- **Expansion of the squared Riemannian distance to fifth order.** Let `g` be a Riemannian
coordinate metric on an open `U ⊆ ℝⁿ`, viewed as a Riemannian manifold via
`IsRiemMetric.riemannianBundle`, and `K ⊆ U` compact. Then there are `C` and `r > 0` such that for
`x ∈ K` and `y ∈ U` with `‖y - x‖ ≤ r`,
`|d(x, y)² - F_x(y - x)| ≤ C ‖y - x‖⁵`, where `d` is `riemannianEDist` and
`F_x(w) = g(w, w) + ½ ∂_w g(w, w) + ⅙ ∂_w ∂_w g(w, w) - (1/12) g(Γ(w, w), Γ(w, w))` at `x`
(`distJet`). -/
theorem IsRiemMetric.riemannianEDist_sq_expansion (hg : IsRiemMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    letI := hg.riemannianBundle
    ∃ C r : ℝ, 0 < r ∧ ∀ x y : U, (x : Fin n → ℝ) ∈ K → ‖(y : Fin n → ℝ) - x‖ ≤ r →
      |(riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 - distJet g x ((y : Fin n → ℝ) - x)| ≤
        C * ‖(y : Fin n → ℝ) - x‖ ^ 5 := by
  let := hg.riemannianBundle
  obtain ⟨C, r, hr, h⟩ := hg.dist_sq_expansion hK hKU
  refine ⟨C, r, hr, fun x y hx hxy => ?_⟩
  rw [← hg.chartDist_eq_toReal_riemannianEDist x y]
  have := h x hx ((y : Fin n → ℝ) - x) hxy
  rwa [add_sub_cancel] at this

/-- **Expansion of the squared Riemannian distance about the midpoint.** With the hypotheses of
`riemannianEDist_sq_expansion`, there are `C` and `r > 0` such that for `x, y ∈ U` with
`‖y - x‖ ≤ r` and midpoint `m = (1/2)(x + y) ∈ K`,
`|d(x, y)² - midJet g m (y - x)| ≤ C ‖y - x‖⁵`. -/
theorem IsRiemMetric.riemannianEDist_sq_expansion_midpoint (hg : IsRiemMetric g U)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    letI := hg.riemannianBundle
    ∃ C r : ℝ, 0 < r ∧ ∀ x y : U, (1 / 2 : ℝ) • ((x : Fin n → ℝ) + y) ∈ K →
      ‖(y : Fin n → ℝ) - x‖ ≤ r →
      |(riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y).toReal ^ 2 -
          midJet g ((1 / 2 : ℝ) • ((x : Fin n → ℝ) + y)) ((y : Fin n → ℝ) - x)| ≤
        C * ‖(y : Fin n → ℝ) - x‖ ^ 5 := by
  let := hg.riemannianBundle
  obtain ⟨C, r, hr, h⟩ := hg.dist_sq_expansion_midpoint hK hKU
  refine ⟨C, r, hr, fun x y hm hxy => ?_⟩
  rw [← hg.chartDist_eq_toReal_riemannianEDist x y]
  have := h _ hm ((y : Fin n → ℝ) - x) hxy
  have e1 : (1 / 2 : ℝ) • ((x : Fin n → ℝ) + y) - (1 / 2 : ℝ) • ((y : Fin n → ℝ) - x) = x := by
    module
  have e2 : (1 / 2 : ℝ) • ((x : Fin n → ℝ) + y) + (1 / 2 : ℝ) • ((y : Fin n → ℝ) - x) = y := by
    module
  rwa [e1, e2] at this

end Lightlike.Upstream.GeodesicExpansion
