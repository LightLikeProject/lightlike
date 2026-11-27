import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz

/-!
# The Fourier transform of a compactly supported function at complex frequency

For `g : ℝ → ℂ` continuous with compact support, `ftC g z = ∫ e^{izt} g(t) dt` is an entire function of `z`
(`differentiable_ftC`). If `g` is `C²`, integrating by parts twice gives `ftC g'' z = -z² ftC g z`
(`ftC_deriv_deriv`) and so a decay uniform on horizontal strips:
`‖ftC g (x + iy)‖ ≤ C/(1 + x²)` for `|y| ≤ Y` (`norm_ftC_le`). This is the analytic input for the contour shifts of
the odd Plancherel identity (`docs/notes/sl2r-odd-plancherel-route.md`): for `g = 𝒜G`, the transform at a real
frequency is the spherical transform `sphTransformH G` (`ftC_ofReal`).
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2RPlancherel

/-- **The Fourier transform at complex frequency** `z ↦ ∫ e^{izt} g(t) dt`. -/
def ftC (g : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t : ℝ, Complex.exp (z * t * I) * g t

/-- At a real frequency it is the spherical transform of `G` when `g = 𝒜G`. -/
lemma ftC_ofReal (G : ℝ → ℂ) (ρ : ℝ) : ftC (abelTransform G) (ρ : ℂ) = sphTransformH G ρ := by
  rw [sphTransformH_eq_integral_abel]; rfl

/-- A compactly supported function vanishes outside some `[-T, T]`. -/
lemma exists_zero_of_abs_gt {g : ℝ → ℂ} (hg : HasCompactSupport g) : ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T < |t| → g t = 0 := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 0, le_max_right _ _, fun t ht => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have := lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left R 0) ht)
  exact lt_irrefl _ this

lemma norm_exp_mul_I (z : ℂ) (t : ℝ) : ‖Complex.exp (z * t * I)‖ = Real.exp (-(t * z.im)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]; ring

lemma norm_exp_mul_I_le (z : ℂ) (t : ℝ) {Y : ℝ} (hz : |z.im| ≤ Y) {T : ℝ} (ht : |t| ≤ T) :
    ‖Complex.exp (z * t * I)‖ ≤ Real.exp (Y * T) := by
  rw [norm_exp_mul_I]
  refine Real.exp_le_exp.mpr ?_
  have h1 : -(t * z.im) ≤ |t * z.im| := neg_le_abs _
  rw [abs_mul] at h1
  have h2 : |t| * |z.im| ≤ T * Y := mul_le_mul ht hz (abs_nonneg _) ((abs_nonneg t).trans ht)
  nlinarith

/-- **`ftC g` is entire** for `g` continuous with compact support. -/
theorem differentiable_ftC {g : ℝ → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Differentiable ℂ (ftC g) := by
  intro z₀
  obtain ⟨T, hT0, hT⟩ := exists_zero_of_abs_gt hc
  set Y : ℝ := |z₀.im| + 1 with hY
  set B : ℝ := T * Real.exp (Y * T) with hB
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hc
  have hcontF : ∀ z : ℂ, Continuous fun t : ℝ => Complex.exp (z * t * I) * g t := fun z =>
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (z * t * I)).mul hg
  have hcontF' : ∀ z : ℂ, Continuous fun t : ℝ => (I * (t : ℂ)) * (Complex.exp (z * t * I) * g t) := fun z =>
    (by fun_prop : Continuous fun t : ℝ => I * (t : ℂ)).mul (hcontF z)
  have hcsF : ∀ z : ℂ, HasCompactSupport fun t : ℝ => Complex.exp (z * t * I) * g t := fun z => hc.mul_left
  have hcsF' : ∀ z : ℂ, HasCompactSupport fun t : ℝ => (I * (t : ℂ)) * (Complex.exp (z * t * I) * g t) :=
    fun z => (hcsF z).mul_left
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
    (F := fun z t => Complex.exp (z * t * I) * g t)
    (F' := fun z t => (I * (t : ℂ)) * (Complex.exp (z * t * I) * g t)) (x₀ := z₀)
    (bound := fun t => B * ‖g t‖) (s := Metric.ball z₀ 1) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (hcontF z).aestronglyMeasurable)
    ((hcontF z₀).integrable_of_hasCompactSupport (hcsF z₀))
    (hcontF' z₀).aestronglyMeasurable
    (Eventually.of_forall fun t z hz => by
      by_cases ht : T < |t|
      · rw [hT t ht]; simp [hB]
      · have ht' : |t| ≤ T := not_lt.mp ht
        have hzY : |z.im| ≤ Y := by
          have : |z.im - z₀.im| ≤ ‖z - z₀‖ := by simpa using Complex.abs_im_le_norm (z - z₀)
          have hz' : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
          rw [hY]
          have := abs_sub_abs_le_abs_sub z.im z₀.im
          linarith
        have hexp := norm_exp_mul_I_le z t hzY ht'
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |t| * (‖Complex.exp (z * t * I)‖ * ‖g t‖) ≤ T * (Real.exp (Y * T) * ‖g t‖) := by gcongr
          _ = B * ‖g t‖ := by rw [hB]; ring)
    (hgi.norm.const_mul B)
    (Eventually.of_forall fun t z _ => by
      have h1 : HasDerivAt (fun z : ℂ => z * t * I) ((t : ℂ) * I) z := by
        simpa [mul_assoc] using ((hasDerivAt_id z).mul_const (t : ℂ)).mul_const I
      have h2 := (h1.cexp).mul_const (g t)
      convert h2 using 1
      ring)
  exact key.2.differentiableAt

/-- **Integration by parts**: `ftC g' z = -(i z) ftC g z` for `g` of class `C¹` with compact support. -/
lemma ftC_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (z : ℂ) :
    ftC (deriv g) z = -(I * z) * ftC g z := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd1 : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (z * t * I))
      (z * I * Complex.exp (z * t * I)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ) * I) (z * I) t := by
      have := (((hasDerivAt_id t).ofReal_comp).const_mul z).mul_const I
      simpa using this
    have := h1.cexp
    simpa [mul_comm] using this
  have hcexp : Continuous fun t : ℝ => Complex.exp (z * t * I) := by fun_prop
  have hi1 : Integrable fun t : ℝ => Complex.exp (z * t * I) * deriv g t :=
    (hcexp.mul hd1).integrable_of_hasCompactSupport hc.deriv.mul_left
  have hi2 : Integrable fun t : ℝ => (z * I * Complex.exp (z * t * I)) * g t :=
    ((by fun_prop : Continuous fun t : ℝ => z * I * Complex.exp (z * t * I)).mul hg.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi3 : Integrable fun t : ℝ => Complex.exp (z * t * I) * g t :=
    (hcexp.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  have := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => Complex.exp (z * t * I)) (v := g)
    (u' := fun t => z * I * Complex.exp (z * t * I)) (v' := deriv g)
    (fun t _ => hu t) (fun t _ => (hgd t).hasDerivAt)
    (by simpa [Pi.mul_def] using hi1) (by simpa [Pi.mul_def] using hi2)
    (by simpa [Pi.mul_def] using hi3)
  have e2 : ∫ t : ℝ, (z * I * Complex.exp (z * t * I)) * g t =
      (z * I) * ∫ t : ℝ, Complex.exp (z * t * I) * g t := by
    rw [← integral_const_mul]; congr 1; funext t; ring
  unfold ftC
  calc ∫ t : ℝ, Complex.exp (z * t * I) * deriv g t
      = -∫ t : ℝ, (z * I * Complex.exp (z * t * I)) * g t := this
    _ = -(I * z) * ∫ t : ℝ, Complex.exp (z * t * I) * g t := by rw [e2]; ring

/-- The derivative of a `C²` function is `C¹`. -/
lemma contDiff_one_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) := by
  have h := hg.fderiv_right (m := 1) (by norm_num)
  have e : deriv g = fun x => fderiv ℝ g x 1 := funext fun x => fderiv_apply_one_eq_deriv.symm
  rw [e]
  exact h.clm_apply contDiff_const

/-- `ftC g'' z = -z² ftC g z` for `g` of class `C²` with compact support. -/
lemma ftC_deriv_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (z : ℂ) :
    ftC (deriv (deriv g)) z = -(z ^ 2) * ftC g z := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  rw [ftC_deriv (contDiff_one_deriv hg) hc.deriv, ftC_deriv hg1 hc]
  have : I * I = -1 := Complex.I_mul_I
  linear_combination (z ^ 2 * ftC g z) * this

/-- The norm of the transform at a frequency of imaginary part at most `Y`, for `g` vanishing outside `[-T, T]`:
`‖ftC g z‖ ≤ e^{YT} ∫ ‖g‖`. -/
lemma norm_ftC_le_exp {g : ℝ → ℂ} {T : ℝ} (hT : ∀ t, T < |t| → g t = 0)
    (hgi : Integrable g) {Y : ℝ} {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖ftC g z‖ ≤ Real.exp (Y * T) * ∫ t, ‖g t‖ := by
  unfold ftC
  calc ‖∫ t : ℝ, Complex.exp (z * t * I) * g t‖ ≤ ∫ t : ℝ, ‖Complex.exp (z * t * I) * g t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Real.exp (Y * T) * ‖g t‖ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
          (hgi.norm.const_mul _) (Eventually.of_forall fun t => ?_)
        beta_reduce
        by_cases ht : T < |t|
        · rw [hT t ht]; simp
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_exp_mul_I_le z t hz (not_lt.mp ht)) (norm_nonneg _)
    _ = Real.exp (Y * T) * ∫ t, ‖g t‖ := integral_const_mul _ _

/-- **Uniform decay on a strip**: for `g` of class `C²` with compact support and `Y ≥ 0` there is `C` with
`‖ftC g (x + iy)‖ ≤ C/(1 + x²)` whenever `|y| ≤ Y`. -/
theorem norm_ftC_le {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) (Y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |y| ≤ Y → ‖ftC g ((x : ℂ) + (y : ℂ) * I)‖ ≤ C / (1 + x ^ 2) := by
  have hd2 : Continuous (deriv (deriv g)) := (contDiff_one_deriv hg).continuous_deriv (by norm_num)
  obtain ⟨T, hT0, hT⟩ := exists_zero_of_abs_gt hc
  have hT2 : ∀ t, T < |t| → deriv (deriv g) t = 0 := by
    intro t ht
    have h0 : g =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      have : IsOpen {s : ℝ | T < |s|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [this.mem_nhds ht] with s hs using hT s hs
    have h1 : deriv g =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
      simpa using h0.deriv
    simpa using h1.deriv_eq
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have hg2i : Integrable (deriv (deriv g)) := hd2.integrable_of_hasCompactSupport hc.deriv.deriv
  set K0 : ℝ := Real.exp (Y * T) * ∫ t, ‖g t‖ with hK0
  set K2 : ℝ := Real.exp (Y * T) * ∫ t, ‖deriv (deriv g) t‖ with hK2
  have hK0n : 0 ≤ K0 := by positivity
  have hK2n : 0 ≤ K2 := by positivity
  refine ⟨2 * max K0 K2, by positivity, fun x y hy => ?_⟩
  set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
  have hzim : |z.im| ≤ Y := by simpa [hz] using hy
  have hpos : 0 < 1 + x ^ 2 := by positivity
  by_cases hx : 1 ≤ |x|
  · have h2 := norm_ftC_le_exp hT2 hg2i hzim
    rw [ftC_deriv_deriv hg hc z, norm_mul, norm_neg, norm_pow] at h2
    have hxz : x ^ 2 ≤ ‖z‖ ^ 2 := by
      have : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have hre : z.re = x := by simp [hz]
      rw [hre] at this
      nlinarith [sq_abs x, abs_nonneg x]
    have hx1 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x]
    have hxpos : 0 < x ^ 2 := by linarith
    have : ‖ftC g z‖ ≤ K2 / x ^ 2 := by
      rw [le_div_iff₀ hxpos]
      calc ‖ftC g z‖ * x ^ 2 ≤ ‖ftC g z‖ * ‖z‖ ^ 2 := by gcongr
        _ = ‖z‖ ^ 2 * ‖ftC g z‖ := by ring
        _ ≤ K2 := h2
    calc ‖ftC g z‖ ≤ K2 / x ^ 2 := this
      _ ≤ (2 * K2) / (1 + x ^ 2) := by
          rw [div_le_div_iff₀ hxpos hpos]; nlinarith
      _ ≤ (2 * max K0 K2) / (1 + x ^ 2) := by gcongr; exact le_max_right _ _
  · have hx2 : x ^ 2 < 1 := by
      have := not_le.mp hx
      nlinarith [sq_abs x, abs_nonneg x]
    have h0 := norm_ftC_le_exp hT hgi hzim
    calc ‖ftC g z‖ ≤ K0 := h0
      _ ≤ (2 * K0) / (1 + x ^ 2) := by
          rw [le_div_iff₀ hpos]; nlinarith
      _ ≤ (2 * max K0 K2) / (1 + x ^ 2) := by gcongr; exact le_max_left _ _

end Lightlike.Lorentz.SL2ROddPlancherel
