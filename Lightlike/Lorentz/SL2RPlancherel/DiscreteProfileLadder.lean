module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileCalc

/-!
# Ladder relations for the profile polynomials of the discrete series

`P_{jl}(t) = j`-th Taylor coefficient of `(t + w)^l (1 + t w)^{-(n+l)}` is differentiable on `(-1, 1)`
(`hasDerivAt_profPoly`) and satisfies
`t (1 - t²) P_{jl}' + (l (1 + t²) - j (1 - t²)) P_{jl} = 2 l t P_{j,l-1}` (`profPoly_lower`, with `P_{j,-1}` absent for
`l = 0`: `profPoly_lower_zero`) and
`t (1 - t²) P_{jl}' + (j (1 - t²) - l (1 + t²) - 2 n t²) P_{jl} = -2 (n + l) t P_{j,l+1}` (`profPoly_raise`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma norm_inv_pow_le {v : ℂ} (hv : (1 / 2 : ℝ) ≤ ‖v‖) (N : ℕ) : ‖(v ^ N)⁻¹‖ ≤ 2 ^ N := by
  rw [norm_inv, norm_pow]
  have h1 : (1 / 2 : ℝ) ^ N ≤ ‖v‖ ^ N := pow_le_pow_left₀ (by norm_num) hv N
  have h2 : (0 : ℝ) < (1 / 2) ^ N := by positivity
  calc (‖v‖ ^ N)⁻¹ ≤ ((1 / 2 : ℝ) ^ N)⁻¹ := inv_anti₀ h2 h1
    _ = 2 ^ N := by rw [one_div, inv_pow, inv_inv]

lemma norm_one_add_mul_ge {t : ℝ} (ht : |t| ≤ 1) {w : ℂ} (hw : ‖w‖ = 1 / 2) :
    (1 / 2 : ℝ) ≤ ‖1 + (t : ℂ) * w‖ := by
  have h1 : ‖(t : ℂ) * w‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hw]; nlinarith [abs_nonneg t]
  have := norm_sub_norm_le (1 : ℂ) (-((t : ℂ) * w))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-- The uniform bound of `∂_t G` on the circle `|w| = 1/2`, for `|t| ≤ 1`. -/
def genBound (n l : ℕ) : ℝ :=
  (l : ℝ) * (3 / 2) ^ (l - 1) * 2 ^ (n + l) + ((n + l : ℕ) : ℝ) * (1 / 2) * (3 / 2) ^ l * 2 ^ (n + l + 1)

lemma norm_genFunT_le (n l : ℕ) {t : ℝ} (ht : |t| ≤ 1) {w : ℂ} (hw : ‖w‖ = 1 / 2) :
    ‖genFunT n l t w‖ ≤ genBound n l := by
  have hv := norm_one_add_mul_ge ht hw
  have hA : ‖(t : ℂ) + w‖ ≤ 3 / 2 := by
    calc ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ ≤ 1 + 1 / 2 := by rw [Complex.norm_real, Real.norm_eq_abs, hw]; linarith
      _ = 3 / 2 := by norm_num
  unfold genFunT genBound
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
    have h1 := norm_inv_pow_le hv (n + l)
    have h2 : ‖(t : ℂ) + w‖ ^ (l - 1) ≤ (3 / 2) ^ (l - 1) := pow_le_pow_left₀ (norm_nonneg _) hA _
    gcongr
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow, hw]
    have h1 := norm_inv_pow_le hv (n + l + 1)
    have h2 : ‖(t : ℂ) + w‖ ^ l ≤ (3 / 2) ^ l := pow_le_pow_left₀ (norm_nonneg _) hA _
    gcongr

lemma norm_exp_mode (j : ℕ) (θ : ℝ) : ‖Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I))‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma circleMap_mem_ball (θ : ℝ) : circleMap (0 : ℂ) (1 / 2) θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_circleMap_zero]; norm_num

lemma norm_circleMap_half (θ : ℝ) : ‖circleMap (0 : ℂ) (1 / 2) θ‖ = 1 / 2 := by
  rw [norm_circleMap_zero]; norm_num

/-- **The profile polynomial is differentiable**, with derivative the Taylor coefficient of `∂_t G`. -/
theorem hasDerivAt_profPoly (n l j : ℕ) (hn : 1 ≤ n) {t₀ : ℝ} (ht₀ : |t₀| < 1) :
    HasDerivAt (profPoly n l j) (discCoeff (genFunT n l t₀) j) t₀ := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set E : ℝ → ℂ := fun θ => Complex.exp (-((j : ℂ) * (θ : ℂ) * Complex.I)) with hE
  set F : ℝ → ℝ → ℂ := fun t θ => genFun n l t (circleMap 0 (1 / 2) θ) * E θ with hF
  set F' : ℝ → ℝ → ℂ := fun t θ => genFunT n l t (circleMap 0 (1 / 2) θ) * E θ with hF'
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hne : (2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ j) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by norm_num)))
  set K : ℂ := ((2 * π : ℂ) * (((1 / 2 : ℝ) : ℂ) ^ j))⁻¹ with hK
  set ε : ℝ := 1 - |t₀| with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : ∀ t ∈ ball t₀ ε, |t| < 1 := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have : |t| ≤ |t₀| + |t - t₀| := by
      calc |t| = |t₀ + (t - t₀)| := by ring_nf
        _ ≤ |t₀| + |t - t₀| := abs_add_le _ _
    linarith
  have hint : ∀ t, |t| < 1 → profPoly n l j t = K * ∫ θ in (0 : ℝ)..2 * π, F t θ := by
    intro t ht
    have h := integral_circleMap_mode (differentiableOn_genFun n l ht) j hs
    have h' : ∫ θ in (0 : ℝ)..2 * π, F t θ = 2 * π * (((1 / 2 : ℝ) : ℂ) ^ j * profPoly n l j t) := h
    rw [h', hK]
    field_simp
  have hint' : ∀ t, |t| < 1 → K * ∫ θ in (0 : ℝ)..2 * π, F' t θ = discCoeff (genFunT n l t) j := by
    intro t ht
    have h := integral_circleMap_mode (differentiableOn_genFunT n l ht) j hs
    have h' : ∫ θ in (0 : ℝ)..2 * π, F' t θ =
        2 * π * (((1 / 2 : ℝ) : ℂ) ^ j * discCoeff (genFunT n l t) j) := h
    rw [h', hK]
    field_simp
  have hcontF : ∀ t, |t| < 1 → Continuous (F t) := by
    intro t ht
    refine Continuous.mul ?_ (by simp only [hE]; fun_prop)
    exact (differentiableOn_genFun n l ht).continuousOn.comp_continuous (continuous_circleMap 0 (1 / 2))
      circleMap_mem_ball
  have hcontF' : Continuous (F' t₀) := by
    refine Continuous.mul ?_ (by simp only [hE]; fun_prop)
    exact (differentiableOn_genFunT n l ht₀).continuousOn.comp_continuous (continuous_circleMap 0 (1 / 2))
      circleMap_mem_ball
  have hderiv := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2 * π) (F := F) (F' := F') (x₀ := t₀) (s := ball t₀ ε)
    (bound := fun _ => genBound n l) (ball_mem_nhds t₀ hεpos)
    (by filter_upwards [ball_mem_nhds t₀ hεpos] with x hx using (hcontF x (hball x hx)).aestronglyMeasurable)
    ((hcontF t₀ ht₀).intervalIntegrable _ _)
    hcontF'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ x hx => by
      simp only [hF']
      rw [norm_mul, norm_exp_mode, mul_one]
      exact norm_genFunT_le n l (hball x hx).le (norm_circleMap_half θ))
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ x hx => by
      have hxm := hball x hx
      have hV := one_add_mul_ne_zero hxm (circleMap_mem_ball θ)
      exact (hasDerivAt_genFun_t n l hn x _ hV).mul_const (E θ))
  have heq : profPoly n l j =ᶠ[𝓝 t₀] fun t => K * ∫ θ in (0 : ℝ)..2 * π, F t θ := by
    filter_upwards [ball_mem_nhds t₀ hεpos] with t ht using hint t (hball t ht)
  have := (hderiv.2.const_mul K).congr_of_eventuallyEq heq
  rwa [hint' t₀ ht₀] at this

end Lightlike.Lorentz.SL2RPlancherel
