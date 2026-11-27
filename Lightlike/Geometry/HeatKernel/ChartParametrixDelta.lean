import Mathlib
import Lightlike.Geometry.HeatKernel.ChartParametrix
import Lightlike.Geometry.HeatKernel.ChartDelta
import Lightlike.Geometry.HeatKernel.WorldFunctionTaylor

/-!
# The delta property of the parametrix in a chart

For a Riemannian coordinate metric `g` on an open `U ⊆ ℝⁿ` and `x ∈ U`, the cut-off parametrix `H` of
`Lightlike.exists_chart_parametrix` is an approximate identity near `x`: for every bounded uniformly continuous `F`,

`∫ H(t, p, y) F(y) dy → F(p) / √det g(p)`   as `t → 0⁺`, uniformly for `p` near `x`.

With `F = f · √det g` (the chart density of the volume measure) the limit is `f(p)`: this is the delta property of the
parametrix in the chart.

The proof compares `H` with the frozen Gaussian `(4πt)^{-n/2} e^{-g_p(y−p, y−p)/4t}` pointwise
(`Lightlike.cutoffGauss_sub_frozen_le₂`, an error `O(√t)` times a wider Gaussian, from the third-order Taylor bound of
the world function `Lightlike.exists_abs_pairing_sub_le` and the Lipschitz bound of `u₀` with `u₀(p, p) = 1`),
integrates the error (`Lightlike.delta_of_pointwise`), and uses that the frozen Gaussian is an approximate identity
with total mass `1/√det g(p)` (`Lightlike.frozenGaussian_approx`).

## Main results

* `Lightlike.quad_lower_of_ball`: a quadratic lower bound on a ball holds for all vectors (homogeneity).
* `Lightlike.exists_chart_parametrix_delta`: the chart parametrix with the delta property.

## References

Liu Bo, *Note on Global Analysis on Manifolds* (ECNU course notes, 2019), Thm 3.2.13(1), printed pp. 124–125,
eqs. (3.2.99)–(3.2.102) (read). The source works on the manifold in exponential coordinates around the base point
`x`, substitutes `y = √t v` and passes to the limit under the integral, getting `K_t^N s → s` in every `C^ℓ` norm.
Here the statement is the `C⁰` delta property in a chart, uniform in the base point, for bounded uniformly continuous
test functions, and the proof is by comparison with the frozen Gaussian of `g(p)` rather than by exponential
coordinates; the `C^ℓ` convergence of the source is not proved here.
-/

open Set Filter Metric MeasureTheory Real Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **A quadratic lower bound on a ball extends to all vectors** by homogeneity. -/
theorem quad_lower_of_ball {G : Matrix (Fin n) (Fin n) ℝ} {l ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ w : Fin n → ℝ, ‖w‖ ≤ ρ → l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (G *ᵥ w)) (w : Fin n → ℝ) :
    l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (G *ᵥ w) := by
  by_cases hw : w = 0
  · simp [hw]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set s := ρ / ‖w‖ with hs
  have hs0 : 0 < s := by positivity
  have h1 := h (s • w) (by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hs, div_mul_cancel₀ _ hwn.ne'])
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul] at h1
  have hss : 0 < s * s := by positivity
  nlinarith

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The delta property of the chart parametrix**: the parametrix `H` of `exists_chart_parametrix` (with all its
properties restated) satisfies, for `p` in a smaller ball around `x`, `∫ H(t, p, y) F(y) dy → F(p)/√det g(p)` as
`t → 0⁺`, uniformly in `p`, for every bounded uniformly continuous `F`. -/
theorem exists_chart_parametrix_delta (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) (N : ℕ) :
    ∃ (r : ℝ) (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ), 0 < r ∧
      (∀ p, ‖p - x‖ < r → u 0 (p, p) = 1) ∧
      (∀ t > 0, ∀ p, ‖p - x‖ < r →
        H t p p = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k (p, p)) ∧
      (∃ C a : ℝ, 0 < a ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y,
        |H t p y| ≤ C * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t)) ∧
      (∀ t p, ‖p - x‖ < r → Continuous (H t p)) ∧
      (∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y, ∃ D, HasDerivAt (fun s => H s p y) D t ∧
        |D + coordLaplacian g (H t p) y| ≤ C * t ^ ((N : ℝ) - n / 2)) ∧
      ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∀ (F : (Fin n → ℝ) → ℝ) (B : ℝ), (∀ y, |F y| ≤ B) → UniformContinuous F →
        ∀ ε > 0, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ p, ‖p - x‖ < r' →
          |(∫ y, H t p y * F y) - F p / √(g p).det| ≤ ε := by
  obtain ⟨r, u, H, hr, hu0, hHd, hGa, -, ⟨Ω, θ, σ, V, hΩo, hxΩ, hmem, hΩU, hVs, hus, hVd, hσV, hθ1, hθ0, hθr,
    -, -, hHc, -, ⟨c, hc, hσlow⟩, ⟨A, hA⟩, hH⟩, herr⟩ := exists_chart_parametrix hg hx N
  refine ⟨r, u, H, hr, hu0, hHd, hGa, hHc, herr, ?_⟩
  -- the Taylor bound of the world function
  obtain ⟨rT, C₁, hrT, hC₁, hT⟩ := exists_abs_pairing_sub_le hg.coord.toLightlike hΩo hVs hx hxΩ
    (fun p hp => (hVd p hp).1) (fun p hp => (hVd p hp).2)
  -- `u₀` is Lipschitz near `(x, x)`
  obtain ⟨KL, tL, htL, hlip⟩ :=
    (((hus 0).contDiffAt (hΩo.mem_nhds hxΩ)).of_le (by exact_mod_cast le_top) :
      ContDiffAt ℝ 1 (u 0) (x, x)).exists_lipschitzOnWith
  obtain ⟨ρL, hρL, hρLt⟩ := Metric.mem_nhds_iff.1 htL
  -- the higher coefficients are bounded near `(x, x)`
  obtain ⟨ρΩ, hρΩ, hρΩs⟩ := Metric.isOpen_iff.1 hΩo _ hxΩ
  have hKΩ : closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) (ρΩ / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hρΩs
  have hcs : ContinuousOn (fun q => ∑ k ∈ Finset.range N, |u (k + 1) q|) Ω :=
    continuousOn_finsetSum _ fun k _ => (hus (k + 1)).continuousOn.abs
  obtain ⟨M, hM⟩ := (isCompact_closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) (ρΩ / 2)).exists_bound_of_continuousOn
    (hcs.mono hKΩ)
  -- the uniform lower bound of the metric
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hg.coord.isOpen x hx
  have hKU : closedBall x (ε₀ / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hε₀U
  obtain ⟨l, rw, hl, hrw, hlow⟩ := Upstream.GeodesicExpansion.IsRiemMetric.normSq_lower
    (U := ⟨U, hg.coord.isOpen⟩) hg (isCompact_closedBall x (ε₀ / 2)) hKU
  -- the radii
  set R := min (min rT ρL) (min (ρΩ / 2) (ε₀ / 2)) with hR
  have hR0 : 0 < R := lt_min (lt_min hrT hρL) (lt_min (by linarith) (by linarith))
  have hRT : R ≤ rT := (min_le_left _ _).trans (min_le_left _ _)
  have hRL : R ≤ ρL := (min_le_left _ _).trans (min_le_right _ _)
  have hRΩ : R ≤ ρΩ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : R ≤ ε₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set rb := min (R / 2) r with hrb
  have hrb0 : 0 < rb := lt_min (by linarith) hr
  have hrbr : rb ≤ r := min_le_right _ _
  have hrbR : rb ≤ R / 2 := min_le_left _ _
  set c' := min c l with hc'
  have hc'0 : 0 < c' := lt_min hc hl
  set C₂ := (KL : ℝ) + |M| with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set K := ((1 + C₂ * (rb + 1)) * C₁ * 2 * √(4 / c') ^ 3 + C₂ * (√(4 / c') + 1) + 64 / (rb ^ 2 * c')) +
    (|A| + 1) * (32 / (rb ^ 2 * c')) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the metric lower bound for all vectors
  have hlowall : ∀ p, ‖p - x‖ < rb → ∀ w, l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (g p *ᵥ w) := fun p hp =>
    quad_lower_of_ball hrw (hlow p (by rw [mem_closedBall, dist_eq_norm]; linarith))
  have hpU : ∀ p, ‖p - x‖ < rb → p ∈ U := fun p hp =>
    hΩU (p, p) (hmem p p (lt_of_lt_of_le hp hrbr) (by simpa using hr))
  -- the pointwise comparison
  have hcmp : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p ∈ {p : Fin n → ℝ | ‖p - x‖ < rb}, ∀ y, |H t p y -
      (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t))| ≤
      (4 * π * t) ^ (-(n : ℝ) / 2) * (K * √t * Real.exp (-(c' * ‖y - p‖ ^ 2 / (4 * t)) / 2)) := by
    intro t ht p hp y
    have hp : ‖p - x‖ < rb := hp
    have hpr : ‖p - x‖ < r := lt_of_lt_of_le hp hrbr
    have ht0 : 0 < t := ht.1
    have hyx : ‖y - p‖ < rb → ‖y - x‖ < R := fun hz => by
      have := norm_sub_le_norm_sub_add_norm_sub y p x
      linarith
    have hσ : ‖y - p‖ < r → c' * ‖y - p‖ ^ 2 ≤ σ (p, y) := fun hz =>
      le_trans (by gcongr; exact min_le_left _ _) (hσlow p y hpr hz)
    have hq : c' * ‖y - p‖ ^ 2 ≤ (y - p) ⬝ᵥ (g p *ᵥ (y - p)) :=
      le_trans (by gcongr; exact min_le_right _ _) (hlowall p hp (y - p))
    have hσq : ‖y - p‖ < rb → |σ (p, y) - (y - p) ⬝ᵥ (g p *ᵥ (y - p))| ≤ C₁ * ‖y - p‖ ^ 3 := fun hz => by
      rw [hσV (p, y) (hmem p y hpr (lt_of_lt_of_le hz hrbr)), ← Geodesic.pairing_eq_dotProduct]
      exact hT p y (by linarith) (by linarith [hyx hz])
    have hU : ‖y - p‖ < rb → |truncAnsatz (fun k y => u k (p, y)) N t y - 1| ≤ C₂ * (‖y - p‖ + t) := by
      intro hz
      have hyR := hyx hz
      have hpyB : (p, y) ∈ ball ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) R := by
        rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact max_lt (by linarith) hyR
      have hppB : (p, p) ∈ ball ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) R := by
        rw [mem_ball, Prod.dist_eq, dist_eq_norm, max_self]; linarith
      have h1 : |u 0 (p, y) - 1| ≤ KL * ‖y - p‖ := by
        rw [← hu0 p hpr, ← Real.dist_eq]
        have := hlip.dist_le_mul (p, y) (hρLt (ball_subset_ball hRL hpyB)) (p, p)
          (hρLt (ball_subset_ball hRL hppB))
        refine this.trans (le_of_eq ?_)
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact congrArg _ (dist_eq_norm y p)
      have h2 : |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)| ≤ t * |M| := by
        have hb := hM (p, y) (ball_subset_closedBall (ball_subset_ball hRΩ hpyB))
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at hb
        calc |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)|
            ≤ ∑ k ∈ Finset.range N, |t ^ (k + 1) * u (k + 1) (p, y)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range N, t * |u (k + 1) (p, y)| := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [abs_mul, abs_of_nonneg (pow_nonneg ht0.le _)]
              exact mul_le_mul_of_nonneg_right (pow_le_of_le_one ht0.le ht.2 (Nat.succ_ne_zero k))
                (abs_nonneg _)
          _ = t * ∑ k ∈ Finset.range N, |u (k + 1) (p, y)| := by rw [Finset.mul_sum]
          _ ≤ t * |M| := mul_le_mul_of_nonneg_left (hb.trans (le_abs_self _)) ht0.le
      have hsplit : truncAnsatz (fun k y => u k (p, y)) N t y - 1 =
          (∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)) + (u 0 (p, y) - 1) := by
        rw [truncAnsatz, Finset.sum_range_succ', pow_zero, one_mul]; ring
      rw [hsplit]
      calc _ ≤ |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)| + |u 0 (p, y) - 1| := abs_add_le _ _
        _ ≤ t * |M| + KL * ‖y - p‖ := add_le_add h2 h1
        _ ≤ C₂ * (‖y - p‖ + t) := by
            rw [hC₂]
            nlinarith [norm_nonneg (y - p), abs_nonneg M, KL.2, ht0.le]
    have hUA : ‖y - p‖ < r → |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ |A| := fun hz =>
      (hA t ht p y hpr hz).trans (le_abs_self _)
    have hpt := cutoffGauss_sub_frozen_le₂ ht0 ht.2 hc'0 hrb0 hrbr hC₁ hC₂0 (abs_nonneg A) (hθr (y - p))
      (hθ1 (y - p)) (hθ0 (y - p)) hσ hq hσq hU hUA
    have hG0 : 0 < (4 * π * t) ^ (-(n : ℝ) / 2) := by positivity
    have heq : H t p y - (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t)) =
        (4 * π * t) ^ (-(n : ℝ) / 2) * (θ (y - p) * Real.exp (-σ (p, y) / (4 * t)) *
          truncAnsatz (fun k y => u k (p, y)) N t y - Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t))) := by
      rw [hH, heatGaussian, gaussFactor]; ring
    rw [heq, abs_mul, abs_of_pos hG0]
    exact mul_le_mul_of_nonneg_left hpt hG0.le
  refine ⟨rb, hrb0, hrbr, fun F B hB hF => ?_⟩
  have := delta_of_pointwise (S := {p : Fin n → ℝ | ‖p - x‖ < rb}) (G := g)
    (fun p hp => hg.posDef p (hpU p hp)) hl (fun p hp => hlowall p hp) hK0 hc'0 hcmp
    (fun t _ p hp => hHc t p (lt_of_lt_of_le hp hrbr)) hB hF
  exact fun ε hε => by
    obtain ⟨t₀, ht₀, h⟩ := this ε hε
    exact ⟨t₀, ht₀, fun t ht p hp => h t ht p hp⟩

end Lightlike
