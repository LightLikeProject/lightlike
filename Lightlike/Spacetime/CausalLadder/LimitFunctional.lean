import Mathlib

/-!
# A one-sided functional bound passes to the derivative of a uniform limit

Let `g k : ℝ → E` converge uniformly on `[σ₀, σ₀ + h₀]` to a `C`-Lipschitz map `u` that is
differentiable at `σ₀`, and let `Φ` be a continuous linear functional. If, for every `k`, the bound
`Φ (g k σ₂ - g k σ₁) ≤ ε (σ₂ - σ₁)` holds whenever `σ₀ ≤ σ₁ ≤ σ₂ ≤ σ₀ + h₀` and `g k` stays within
distance `r` of `u σ₀` on `[σ₁, σ₂]`, then `Φ (u' σ₀) ≤ ε`.

This is the analytic step that turns the frozen functional estimate for causal curves
(`exists_functional_estimate`) into a statement about the derivative of the limit curve.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Set Filter Topology

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One-sided bound for the derivative of a uniform limit.** See the module docstring. -/
theorem functional_le_of_tendstoUniformlyOn {Φ : E →L[ℝ] ℝ} {ε r C h₀ σ₀ : ℝ} {u : ℝ → E} {D : E}
    (hr : 0 < r) (hC : 0 < C) (hh₀ : 0 < h₀) (g : ℕ → ℝ → E)
    (hlip : ∀ x y, ‖u x - u y‖ ≤ C * |x - y|)
    (hu : HasDerivAt u D σ₀)
    (hconv : TendstoUniformlyOn g u atTop (Icc σ₀ (σ₀ + h₀)))
    (hbound : ∀ᶠ k in atTop, ∀ σ₁ σ₂, σ₀ ≤ σ₁ → σ₁ ≤ σ₂ → σ₂ ≤ σ₀ + h₀ →
      (∀ σ ∈ Icc σ₁ σ₂, ‖g k σ - u σ₀‖ < r) → Φ (g k σ₂ - g k σ₁) ≤ ε * (σ₂ - σ₁)) :
    Φ D ≤ ε := by
  -- the displacement bound for the limit
  have hlim : ∀ h, 0 < h → h ≤ h₀ → C * h < r / 2 → Φ (u (σ₀ + h) - u σ₀) ≤ ε * h := by
    intro h hh hhh hCh
    have hev : ∀ᶠ k in atTop, ∀ σ ∈ Icc σ₀ (σ₀ + h₀), dist (u σ) (g k σ) < r / 2 :=
      Metric.tendstoUniformlyOn_iff.1 hconv (r / 2) (by positivity)
    have hk : ∀ᶠ k in atTop, Φ (g k (σ₀ + h) - g k σ₀) ≤ ε * h := by
      filter_upwards [hev, hbound] with k hk hbk
      have := hbk σ₀ (σ₀ + h) le_rfl (by linarith) (by linarith) (fun σ hσ => by
        have h1 := hk σ ⟨hσ.1, hσ.2.trans (by linarith)⟩
        have h2 := hlip σ σ₀
        rw [abs_of_nonneg (by linarith [hσ.1])] at h2
        have h3 : ‖g k σ - u σ₀‖ ≤ ‖g k σ - u σ‖ + ‖u σ - u σ₀‖ := by
          simpa using norm_add_le (g k σ - u σ) (u σ - u σ₀)
        rw [dist_eq_norm, norm_sub_rev] at h1
        have : σ - σ₀ ≤ h := by linarith [hσ.2]
        nlinarith [mul_le_mul_of_nonneg_left this hC.le])
      simpa using this
    -- pass to the limit `k → ∞`
    have ht : Tendsto (fun k => Φ (g k (σ₀ + h) - g k σ₀)) atTop (𝓝 (Φ (u (σ₀ + h) - u σ₀))) := by
      have h1 : Tendsto (fun k => g k (σ₀ + h)) atTop (𝓝 (u (σ₀ + h))) :=
        (hconv.tendsto_at ⟨by linarith, by linarith⟩)
      have h2 : Tendsto (fun k => g k σ₀) atTop (𝓝 (u σ₀)) :=
        (hconv.tendsto_at ⟨le_rfl, by linarith⟩)
      exact Φ.continuous.continuousAt.tendsto.comp (h1.sub h2)
    exact le_of_tendsto ht hk
  -- the slope converges to `D`
  have hslope : Tendsto (fun h : ℝ => h⁻¹ • (u (σ₀ + h) - u σ₀)) (𝓝[>] 0) (𝓝 D) := by
    have := hu.tendsto_slope_zero_right
    simpa using this
  have hΦ : Tendsto (fun h : ℝ => Φ (h⁻¹ • (u (σ₀ + h) - u σ₀))) (𝓝[>] 0) (𝓝 (Φ D)) :=
    Φ.continuous.continuousAt.tendsto.comp hslope
  refine le_of_tendsto hΦ ?_
  have hmin : (0 : ℝ) < min h₀ (r / (2 * C)) := lt_min hh₀ (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hmin] with h hh
  have hpos' : 0 < h := hh.1
  have h1 : h ≤ h₀ := (hh.2.trans_le (min_le_left _ _)).le
  have h2 : C * h < r / 2 := by
    have := hh.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    nlinarith
  have := hlim h hpos' h1 h2
  rw [map_smul, smul_eq_mul]
  calc h⁻¹ * Φ (u (σ₀ + h) - u σ₀) ≤ h⁻¹ * (ε * h) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.2 hpos'.le)
    _ = ε := by field_simp

end Lightlike.Causal
