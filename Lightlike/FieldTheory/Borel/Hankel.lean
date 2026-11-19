import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Hankel's formula on a vertical line

For `k ≥ 1`, `x > 0` and `c > 0`, the integral of `e^{xw} w^{-k-1}` along the vertical line `Re w = c`, divided by
`2πi`, is `x^k/k!` (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776, eq. (B.2), p. 25, Hankel's representation of
`1/Γ(k + 1)`, for integer `k ≥ 1`). The line is parametrized as `w = c + 2πiξ`, `ξ ∈ ℝ`, so that `dw/(2πi) = dξ`
(`hankel_vertical`).

The proof is the Fourier inversion of `φ(t) = t^k e^{-ct}` (`t > 0`, `0` for `t ≤ 0`), whose Fourier transform is the
Laplace transform `∫_0^∞ t^k e^{-(c + 2πiξ)t} dt = k!/(c + 2πiξ)^{k+1}` (`integral_pow_mul_cexp_neg`).

## Main results

* `integral_pow_mul_cexp_neg`: `∫_0^∞ t^k e^{-st} dt = k!/s^{k+1}` for `Re s > 0`.
* `hankel_vertical`: `∫_ℝ e^{x(c + 2πiξ)} (c + 2πiξ)^{-(k+1)} dξ = x^k/k!` for `k ≥ 1`, `x, c > 0`.

## References

* D. Benedetti, R. Gurau, H. Keppler, D. Lettera, arXiv:2210.14776v2, Appendix B, eq. (B.2), p. 25.
-/

open MeasureTheory Set Filter Complex
open scoped Nat Topology FourierTransform Real

namespace Lightlike.FieldTheory.Borel

lemma tendsto_pow_mul_exp_neg_mul (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-(b * t))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (tendsto_id.const_mul_atTop hb)
  have hb' : b ^ n ≠ 0 := pow_ne_zero _ hb.ne'
  have e : (fun t : ℝ => t ^ n * Real.exp (-(b * t))) =
      fun t => (b ^ n)⁻¹ * ((b * t) ^ n * Real.exp (-(b * t))) := by
    funext t; rw [mul_pow]; field_simp
  rw [e]
  simpa using h.const_mul (b ^ n)⁻¹

lemma integrableOn_pow_mul_exp_neg (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := k) (p := 1) (b := b)
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) one_pos hb
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one, neg_mul]

lemma norm_pow_mul_cexp (k : ℕ) (s : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖(t : ℂ) ^ k * cexp (-(s * t))‖ = t ^ k * Real.exp (-(s.re * t)) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
  simp [Complex.mul_re]

lemma integrableOn_pow_mul_cexp_neg (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ k * cexp (-(s * t))) (Ioi 0) := by
  refine (integrableOn_pow_mul_exp_neg k hs).mono' (by fun_prop : Continuous fun t : ℝ =>
    (t : ℂ) ^ k * cexp (-(s * t))).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_pow_mul_cexp k s (le_of_lt ht)]

lemma hasDerivAt_cexp_neg_mul (s : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => cexp (-(s * t))) (cexp (-(s * t)) * (-s)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(s * (t : ℂ))) (-s) t :=
    (((hasDerivAt_id t).ofReal_comp.const_mul s).neg).congr_deriv (by simp)
  exact h1.cexp

/-- **The Laplace transform of `t^k`**: `∫_0^∞ t^k e^{-st} dt = k!/s^{k+1}` for `Re s > 0`. -/
theorem integral_pow_mul_cexp_neg (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ k * cexp (-(s * t)) = (k ! : ℂ) / s ^ (k + 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => -cexp (-(s * t)) / s) (cexp (-(s * t))) t := fun t => by
    have := ((hasDerivAt_cexp_neg_mul s t).neg).div_const s
    convert this using 1
    field_simp
  have hv0 : Tendsto (fun t : ℝ => -cexp (-(s * t)) / s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_pow_mul_exp_neg_mul 0 hs).div_const ‖s‖
    simp only [pow_zero, one_mul, zero_div] at h
    refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
    show _ = ‖-cexp (-(s * t)) / s‖
    rw [norm_div, norm_neg, Complex.norm_exp]
    simp [Complex.mul_re]
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hv 0).continuousAt.continuousWithinAt (fun t _ => hv t)
      (by simpa using integrableOn_pow_mul_cexp_neg 0 hs) hv0]
    simp only [mul_zero, Complex.ofReal_zero, neg_zero, Complex.exp_zero, zero_sub]
    rw [neg_div, neg_neg, one_div]
  | succ k ih =>
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (k + 1)) ((k + 1 : ℂ) * (t : ℂ) ^ k) t :=
      fun t _ => ((hasDerivAt_id t).ofReal_comp.pow (k + 1)).congr_deriv (by simp)
    have huv : Tendsto ((fun t : ℝ => (t : ℂ) ^ (k + 1)) * fun t : ℝ => -cexp (-(s * t)) / s) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h := (tendsto_pow_mul_exp_neg_mul (k + 1) hs).div_const ‖s‖
      rw [zero_div] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp only [Pi.mul_apply]
      rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht, Complex.norm_exp]
      simp [Complex.mul_re]
      ring
    have huv0 : Tendsto ((fun t : ℝ => (t : ℂ) ^ (k + 1)) * fun t : ℝ => -cexp (-(s * t)) / s) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous ((fun t : ℝ => (t : ℂ) ^ (k + 1)) * fun t : ℝ => -cexp (-(s * t)) / s) := by
        fun_prop
      have := hc.tendsto 0
      simp only [Pi.mul_apply, Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero k), zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hI : IntegrableOn (fun t : ℝ => (k + 1 : ℂ) * (t : ℂ) ^ k * (-cexp (-(s * t)) / s)) (Ioi 0) := by
      have : IntegrableOn (fun t : ℝ => -(k + 1 : ℂ) / s * ((t : ℂ) ^ k * cexp (-(s * t)))) (Ioi 0) :=
        (integrableOn_pow_mul_cexp_neg k hs).const_mul (-(k + 1 : ℂ) / s)
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      field_simp
    have h := integral_Ioi_mul_deriv_eq_deriv_mul hu (fun t _ => hv t)
      (by simpa [Pi.mul_def] using integrableOn_pow_mul_cexp_neg (k + 1) hs) (by simpa [Pi.mul_def] using hI)
      huv0 huv
    rw [h, sub_zero, zero_sub]
    have e : ∫ t in Ioi (0 : ℝ), (k + 1 : ℂ) * (t : ℂ) ^ k * (-cexp (-(s * t)) / s) =
        -((k + 1 : ℂ) / s) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ k * cexp (-(s * t)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      field_simp
    rw [e, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The point `c + 2πiξ` of the vertical line `Re w = c`. -/
noncomputable def vline (c ξ : ℝ) : ℂ := (c : ℂ) + 2 * π * ξ * I

@[simp] lemma vline_re (c ξ : ℝ) : (vline c ξ).re = c := by simp [vline]

lemma sq_norm_vline (c ξ : ℝ) : ‖vline c ξ‖ ^ 2 = c ^ 2 + (2 * π * ξ) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [vline]
  ring

lemma le_norm_vline {c : ℝ} (hc : 0 ≤ c) (ξ : ℝ) : c ≤ ‖vline c ξ‖ := by
  have := Complex.abs_re_le_norm (vline c ξ)
  rwa [vline_re, abs_of_nonneg hc] at this

lemma vline_ne_zero {c : ℝ} (hc : 0 < c) (ξ : ℝ) : vline c ξ ≠ 0 := fun h => by
  have := vline_re c ξ; rw [h, Complex.zero_re] at this; linarith

lemma continuous_vline (c : ℝ) : Continuous (vline c) := by unfold vline; fun_prop

/-- `ξ ↦ 1/(c² + (2πξ)²)` is integrable. -/
lemma integrable_inv_sq_vline {c : ℝ} (hc : 0 < c) :
    Integrable fun ξ : ℝ => (c ^ 2 + (2 * π * ξ) ^ 2)⁻¹ := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (R := 2 * π / c) (by positivity)).const_mul (c ^ 2)⁻¹
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  field_simp

/-- For `n ≥ 2`, `‖c + 2πiξ‖^{-n}` is integrable in `ξ`. -/
lemma integrable_inv_norm_vline_pow {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 2 ≤ n) :
    Integrable fun ξ : ℝ => (‖vline c ξ‖ ^ n)⁻¹ := by
  refine ((integrable_inv_sq_vline hc).const_mul (c ^ (n - 2))⁻¹).mono'
    (Continuous.inv₀ ((continuous_vline c).norm.pow n)
      (fun ξ => pow_ne_zero _ (norm_ne_zero_iff.2 (vline_ne_zero hc ξ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hpos : 0 < ‖vline c ξ‖ := norm_pos_iff.2 (vline_ne_zero hc ξ)
  rw [Real.norm_of_nonneg (by positivity), ← sq_norm_vline]
  have hle : c ^ (n - 2) * ‖vline c ξ‖ ^ 2 ≤ ‖vline c ξ‖ ^ n := by
    calc c ^ (n - 2) * ‖vline c ξ‖ ^ 2 ≤ ‖vline c ξ‖ ^ (n - 2) * ‖vline c ξ‖ ^ 2 := by
          gcongr; exact le_norm_vline hc.le ξ
      _ = ‖vline c ξ‖ ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [← mul_inv]
  exact inv_anti₀ (by positivity) hle

/-- `φ(t) = t^k e^{-ct}` for `t ≥ 0` and `φ(t) = φ(0)` for `t < 0` (through `max t 0`); `φ = 0` on `t ≤ 0` for `k ≥ 1`. -/
noncomputable def laplaceKernel (k : ℕ) (c t : ℝ) : ℂ := ((max t 0 : ℝ) : ℂ) ^ k * cexp (-(c * ((max t 0 : ℝ) : ℂ)))

lemma laplaceKernel_of_nonpos {k : ℕ} (hk : 1 ≤ k) (c : ℝ) {t : ℝ} (ht : t ≤ 0) : laplaceKernel k c t = 0 := by
  simp [laplaceKernel, max_eq_right ht, zero_pow (Nat.one_le_iff_ne_zero.1 hk)]

lemma laplaceKernel_of_pos (k : ℕ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    laplaceKernel k c t = (t : ℂ) ^ k * cexp (-((c : ℂ) * t)) := by
  simp [laplaceKernel, max_eq_left ht.le]

lemma continuous_laplaceKernel (k : ℕ) (c : ℝ) : Continuous (laplaceKernel k c) := by
  unfold laplaceKernel; fun_prop

lemma integrable_laplaceKernel {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) : Integrable (laplaceKernel k c) := by
  have h : IntegrableOn (laplaceKernel k c) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_pow_mul_cexp_neg k (s := c) (by simpa using hc))
      (fun t ht => (laplaceKernel_of_pos k c ht).symm) measurableSet_Ioi
  exact h.integrable_of_forall_notMem_eq_zero fun t ht => laplaceKernel_of_nonpos hk c (not_lt.1 ht)

/-- The Fourier transform of `φ` is its Laplace transform at `c + 2πiξ`. -/
lemma fourier_laplaceKernel {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    𝓕 (laplaceKernel k c) ξ = (k ! : ℂ) / vline c ξ ^ (k + 1) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)
    (fun t ht => by rw [laplaceKernel_of_nonpos hk c (not_lt.1 ht), smul_zero]),
    ← integral_pow_mul_cexp_neg k (s := vline c ξ) (by simpa using hc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [laplaceKernel_of_pos k c ht, smul_eq_mul, mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [vline]
  push_cast
  ring

/-- **Hankel's formula on a vertical line** (Benedetti–Gurau–Keppler–Lettera, eq. (B.2), for integer `k ≥ 1`):
`∫_ℝ e^{x(c + 2πiξ)} (c + 2πiξ)^{-(k+1)} dξ = x^k/k!` for `x, c > 0`, i.e.
`(1/2πi) ∫_{Re w = c} e^{xw} w^{-k-1} dw = x^k/k!`. -/
theorem hankel_vertical {k : ℕ} (hk : 1 ≤ k) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∫ ξ : ℝ, cexp (x * vline c ξ) / vline c ξ ^ (k + 1) = ((x ^ k / k ! : ℝ) : ℂ) := by
  have hF : Integrable (𝓕 (laplaceKernel k c)) := by
    rw [show 𝓕 (laplaceKernel k c) = fun ξ => (k ! : ℂ) / vline c ξ ^ (k + 1) from
      funext (fourier_laplaceKernel hk hc)]
    have h := (integrable_inv_norm_vline_pow hc (n := k + 1) (by omega)).const_mul (k ! : ℝ)
    refine h.mono' (continuous_const.div ((continuous_vline c).pow _)
      fun ξ => pow_ne_zero _ (vline_ne_zero hc ξ)).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_div, norm_pow, Complex.norm_natCast, div_eq_mul_inv]
  have hinv := (continuous_laplaceKernel k c).fourierInv_fourier_eq (integrable_laplaceKernel hk hc) hF
  have hx' := congrFun hinv x
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, laplaceKernel_of_pos k c hx] at hx'
  simp_rw [fourier_laplaceKernel hk hc, smul_eq_mul] at hx'
  have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have e : ∀ ξ : ℝ, cexp (x * vline c ξ) / vline c ξ ^ (k + 1) =
      cexp (c * x) / k ! * (cexp (↑(-2 * π * ξ * -x) * I) * ((k ! : ℂ) / vline c ξ ^ (k + 1))) := fun ξ => by
    have h1 : cexp (↑x * vline c ξ) = cexp (↑c * ↑x) * cexp (↑(-2 * π * ξ * -x) * I) := by
      rw [← Complex.exp_add]; congr 1; simp only [vline]; push_cast; ring
    have hv : vline c ξ ^ (k + 1) ≠ 0 := pow_ne_zero _ (vline_ne_zero hc ξ)
    rw [h1]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, hx',
    show cexp (↑c * ↑x) / (k ! : ℂ) * ((x : ℂ) ^ k * cexp (-(↑c * ↑x))) =
      (x : ℂ) ^ k / k ! * (cexp (↑c * ↑x) * cexp (-(↑c * ↑x))) by ring,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
  push_cast
  ring

end Lightlike.FieldTheory.Borel
