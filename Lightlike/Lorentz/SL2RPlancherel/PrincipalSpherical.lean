import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalCoeff
import Lightlike.Lorentz.SL2RPlancherel.AbelTransform

/-!
# The spherical matrix coefficient of the even principal series

For the `K`-fixed vector `e_0(x) = (1 + x²)^w`, `w = (iν - 1)/2`, the matrix coefficient
`Φ^ν_{0,0}(ξ) = ⟪e_0, π(a(ξ)) e_0⟫` is an average of `u^w` with
`u_ξ(x) = (e^{-ξ} + e^ξ x²)/(1 + x²)` against `dx/(1 + x²)` (`mcoefP_zero_zero`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (the spherical base of the identification of
the block transforms with matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `u_ξ(x) = (e^{-ξ} + e^ξ x²)/(1 + x²)`, which runs over `[e^{-ξ}, e^ξ)`. -/
def sphU (ξ x : ℝ) : ℝ := (Real.exp (-ξ) + Real.exp ξ * x ^ 2) / (1 + x ^ 2)

lemma sphU_pos (ξ x : ℝ) : 0 < sphU ξ x := by
  unfold sphU; positivity

/-- `conj w = -w - 1`. -/
lemma conj_wP (ν : ℝ) : (starRingEnd ℂ) (wP ν) = -wP ν - 1 := by
  simp only [wP, map_div₀, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_one,
    map_ofNat]
  ring

/-- `r^z = exp(z log r)` for `r > 0`. -/
lemma ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (r : ℂ) ^ z = Complex.exp (z * Real.log r) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le, mul_comm]

/-- **The spherical matrix coefficient**:
`Φ^ν_{0,0}(ξ) = ∫ u_ξ(x)^w dx/(1 + x²)`. -/
theorem mcoefP_zero_zero (ν ξ : ℝ) :
    mcoefP ν 0 0 ξ =
      ∫ x, Complex.exp (wP ν * Real.log (sphU ξ x)) / ((1 + x ^ 2 : ℝ) : ℂ) := by
  rw [mcoefP_eq_integral]
  congr 1
  funext x
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + (Real.exp ξ * x) ^ 2 := by positivity
  have h3 : (0 : ℝ) < Real.exp (-ξ) + Real.exp ξ * x ^ 2 := by positivity
  simp only [kVecP, zpow_zero, mul_one]
  rw [show ((I * ν - 1) / 2 : ℂ) = wP ν from rfl, ofReal_cpow_eq_exp h1, ofReal_cpow_eq_exp h2,
    ← Complex.exp_conj, map_mul, conj_wP, Complex.conj_ofReal]
  have hr2 : 1 + (Real.exp ξ * x) ^ 2 = Real.exp ξ * (Real.exp (-ξ) + Real.exp ξ * x ^ 2) := by
    rw [mul_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero]; ring
  have hlog2 : Real.log (1 + (Real.exp ξ * x) ^ 2) =
      ξ + Real.log (Real.exp (-ξ) + Real.exp ξ * x ^ 2) := by
    rw [hr2, Real.log_mul (Real.exp_pos _).ne' h3.ne', Real.log_exp]
  have hlogu : Real.log (sphU ξ x) =
      Real.log (Real.exp (-ξ) + Real.exp ξ * x ^ 2) - Real.log (1 + x ^ 2) := by
    rw [sphU, Real.log_div h3.ne' h1.ne']
  have he : ((1 + x ^ 2 : ℝ) : ℂ) = Complex.exp (Real.log (1 + x ^ 2)) := by
    rw [← Complex.ofReal_exp, Real.exp_log h1]
  rw [he, ← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_add, hlog2, hlogu]
  congr 1
  push_cast
  ring

lemma sphU_eq (ξ x : ℝ) : sphU ξ x = Real.exp ξ - 2 * Real.sinh ξ / (1 + x ^ 2) := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [sphU, Real.sinh_eq, Real.exp_neg]
  field_simp
  ring

lemma sphU_neg (ξ x : ℝ) : sphU ξ (-x) = sphU ξ x := by
  simp only [sphU, neg_sq]

lemma continuous_sphU (ξ : ℝ) : Continuous (sphU ξ) :=
  (continuous_const.add (continuous_const.mul (continuous_pow 2))).div
    (continuous_const.add (continuous_pow 2)) fun x => by positivity

/-- The derivative of `t = log u_ξ(x)`: `4 sinh ξ x/((e^{-ξ} + e^ξ x²)(1 + x²))`. -/
def mehlerDeriv (ξ x : ℝ) : ℝ :=
  4 * Real.sinh ξ * x / ((Real.exp (-ξ) + Real.exp ξ * x ^ 2) * (1 + x ^ 2))

lemma hasDerivAt_log_sphU (ξ x : ℝ) :
    HasDerivAt (fun x => Real.log (sphU ξ x)) (mehlerDeriv ξ x) x := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h3 : (0 : ℝ) < Real.exp (-ξ) + Real.exp ξ * x ^ 2 := by positivity
  have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have hA := (hp.const_mul (Real.exp ξ)).const_add (Real.exp (-ξ))
  have hB := hp.const_add 1
  have e : (fun x => Real.log (sphU ξ x)) =
      fun y => Real.log ((Real.exp (-ξ) + Real.exp ξ * y ^ 2) / (1 + y ^ 2)) := rfl
  rw [e]
  have h := (hA.div hB h1.ne').log (div_pos h3 h1).ne'
  convert h using 1
  simp only [Pi.div_apply]
  have h3' : (0 : ℝ) < (Real.exp ξ)⁻¹ + Real.exp ξ * x ^ 2 := by positivity
  rw [mehlerDeriv, Real.sinh_eq, Real.exp_neg]
  field_simp
  ring

lemma sphU_lt_sphU {ξ : ℝ} (hξ : 0 < ξ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    sphU ξ x < sphU ξ y := by
  have hs := Real.sinh_pos_iff.2 hξ
  rw [sphU_eq, sphU_eq]
  have : 2 * Real.sinh ξ / (1 + y ^ 2) < 2 * Real.sinh ξ / (1 + x ^ 2) :=
    div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)
  linarith

lemma strictMonoOn_log_sphU {ξ : ℝ} (hξ : 0 < ξ) :
    StrictMonoOn (fun x => Real.log (sphU ξ x)) (Ioi 0) := fun x hx _ _ hxy =>
  Real.log_lt_log (sphU_pos ξ x) (sphU_lt_sphU hξ (le_of_lt hx) hxy)

/-- `t = log u_ξ(x)` maps `(0, ∞)` onto `(-ξ, ξ)`. -/
lemma image_log_sphU {ξ : ℝ} (hξ : 0 < ξ) :
    (fun x => Real.log (sphU ξ x)) '' Ioi 0 = Ioo (-ξ) ξ := by
  have hs := Real.sinh_pos_iff.2 hξ
  have hE : Real.exp (-ξ) < Real.exp ξ := Real.exp_lt_exp.2 (by linarith)
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (0 : ℝ) < x := hx
    have h1 : (1 : ℝ) < 1 + x ^ 2 := by nlinarith
    have hq : 2 * Real.sinh ξ / (1 + x ^ 2) < 2 * Real.sinh ξ :=
      div_lt_self (by linarith) h1
    have hq0 : 0 < 2 * Real.sinh ξ / (1 + x ^ 2) := by positivity
    have hEs : Real.exp (-ξ) = Real.exp ξ - 2 * Real.sinh ξ := by rw [Real.sinh_eq]; ring
    constructor
    · rw [Real.lt_log_iff_exp_lt (sphU_pos ξ x), sphU_eq, hEs]; linarith
    · rw [Real.log_lt_iff_lt_exp (sphU_pos ξ x), sphU_eq]; linarith
  · rintro ⟨h1, h2⟩
    have ha : Real.exp (-ξ) < Real.exp t := Real.exp_lt_exp.2 h1
    have hb : Real.exp t < Real.exp ξ := Real.exp_lt_exp.2 h2
    have hr : 0 < (Real.exp t - Real.exp (-ξ)) / (Real.exp ξ - Real.exp t) :=
      div_pos (by linarith) (by linarith)
    refine ⟨Real.sqrt ((Real.exp t - Real.exp (-ξ)) / (Real.exp ξ - Real.exp t)),
      Real.sqrt_pos.2 hr, ?_⟩
    have hsq := Real.sq_sqrt hr.le
    have hu : sphU ξ (Real.sqrt ((Real.exp t - Real.exp (-ξ)) / (Real.exp ξ - Real.exp t))) =
        Real.exp t := by
      rw [sphU, hsq]
      have hne : Real.exp ξ - Real.exp t ≠ 0 := by linarith
      have hne2 : Real.exp ξ - Real.exp (-ξ) ≠ 0 := by linarith
      have hden : 1 + (Real.exp t - Real.exp (-ξ)) / (Real.exp ξ - Real.exp t) =
          (Real.exp ξ - Real.exp (-ξ)) / (Real.exp ξ - Real.exp t) := by
        field_simp; ring
      rw [hden, div_eq_iff (div_ne_zero hne2 hne)]
      field_simp
      ring
    simp only [hu, Real.log_exp]

/-- The Mehler kernel `e^{iνt/2}/√(2(cosh ξ - cosh t))`. -/
def mehlerKernel (ν ξ t : ℝ) : ℂ :=
  Complex.exp (I * ν * t / 2) / ((Real.sqrt (2 * (Real.cosh ξ - Real.cosh t)) : ℝ) : ℂ)

/-- The integrand of `mcoefP_zero_zero`. -/
def sphIntegrand (ν ξ x : ℝ) : ℂ :=
  Complex.exp (wP ν * Real.log (sphU ξ x)) / ((1 + x ^ 2 : ℝ) : ℂ)

/-- **The Jacobian identity** of the substitution `t = log u_ξ(x)`, `x > 0`:
`|t'(x)| e^{iνt/2}/√(2(cosh ξ - cosh t)) = 2 u^w/(1 + x²)`. -/
lemma abs_mehlerDeriv_smul {ν ξ x : ℝ} (hξ : 0 < ξ) (hx : 0 < x) :
    |mehlerDeriv ξ x| • mehlerKernel ν ξ (Real.log (sphU ξ x)) = 2 * sphIntegrand ν ξ x := by
  have hs := Real.sinh_pos_iff.2 hξ
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h3 : (0 : ℝ) < Real.exp (-ξ) + Real.exp ξ * x ^ 2 := by positivity
  have hu := sphU_pos ξ x
  have het : Real.exp (Real.log (sphU ξ x)) = sphU ξ x := Real.exp_log hu
  have hq : 0 < 2 * Real.sinh ξ * x / (1 + x ^ 2) := by positivity
  have hct : Real.cosh (Real.log (sphU ξ x)) = (sphU ξ x + (sphU ξ x)⁻¹) / 2 := by
    rw [Real.cosh_eq, Real.exp_neg, het]
  have hcosh : 2 * (Real.cosh ξ - Real.cosh (Real.log (sphU ξ x))) =
      (2 * Real.sinh ξ * x / (1 + x ^ 2)) ^ 2 / sphU ξ x := by
    have h3' : (0 : ℝ) < (Real.exp ξ)⁻¹ + Real.exp ξ * x ^ 2 := by positivity
    rw [hct, Real.cosh_eq, Real.sinh_eq, sphU, Real.exp_neg]
    field_simp
    ring
  have hsqrt : Real.sqrt (2 * (Real.cosh ξ - Real.cosh (Real.log (sphU ξ x)))) =
      (2 * Real.sinh ξ * x / (1 + x ^ 2)) / Real.sqrt (sphU ξ x) := by
    rw [hcosh, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hq.le]
  have hsu : Real.sqrt (sphU ξ x) = Real.exp (Real.log (sphU ξ x) / 2) := by
    have : sphU ξ x = Real.exp (Real.log (sphU ξ x) / 2) * Real.exp (Real.log (sphU ξ x) / 2) := by
      rw [← Real.exp_add, add_halves, het]
    conv_lhs => rw [this]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hder : mehlerDeriv ξ x = 2 * (2 * Real.sinh ξ * x / (1 + x ^ 2)) / (sphU ξ x * (1 + x ^ 2)) := by
    rw [mehlerDeriv, sphU]
    field_simp
    ring
  have hpos : 0 < mehlerDeriv ξ x := by rw [mehlerDeriv]; positivity
  rw [abs_of_pos hpos, Complex.real_smul, mehlerKernel, sphIntegrand, hsqrt, hsu, hder]
  set t := Real.log (sphU ξ x) with ht
  set q := 2 * Real.sinh ξ * x / (1 + x ^ 2) with hq'
  rw [← het]
  have hw : Complex.exp (wP ν * t) =
      Complex.exp (I * ν * t / 2) * Complex.exp ((t / 2 : ℝ) : ℂ) / Complex.exp (t : ℂ) := by
    rw [← Complex.exp_add, ← Complex.exp_sub]
    congr 1
    simp only [wP]
    push_cast
    ring
  rw [hw]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hBC : ((1 + x ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
  have hE1 : Complex.exp ((t / 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
  have hE2 : Complex.exp (t : ℂ) ≠ 0 := Complex.exp_ne_zero _
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_ofNat]
  field_simp

lemma sphIntegrand_neg (ν ξ x : ℝ) : sphIntegrand ν ξ (-x) = sphIntegrand ν ξ x := by
  simp only [sphIntegrand, sphU_neg, neg_sq]

lemma continuous_sphIntegrand (ν ξ : ℝ) : Continuous (sphIntegrand ν ξ) := by
  have hlog : Continuous fun x => Real.log (sphU ξ x) :=
    (continuous_sphU ξ).log fun x => (sphU_pos ξ x).ne'
  exact (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp hlog))).div
    (Complex.continuous_ofReal.comp (continuous_const.add (continuous_pow 2)))
    fun x => by exact_mod_cast (show (0 : ℝ) < 1 + x ^ 2 by positivity).ne'

lemma re_wP_mul (ν L : ℝ) : (wP ν * (L : ℂ)).re = -L / 2 := by
  simp only [wP, Complex.mul_re, Complex.div_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.div_im,
    Complex.sub_im, Complex.mul_im, Complex.one_im]
  norm_num
  ring

lemma norm_sphIntegrand_le (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) (x : ℝ) :
    ‖sphIntegrand ν ξ x‖ ≤ Real.exp (ξ / 2) * (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hs := Real.sinh_pos_iff.2 hξ
  have hlow : Real.exp (-ξ) ≤ sphU ξ x := by
    rw [sphU_eq]
    have hEs : Real.exp (-ξ) = Real.exp ξ - 2 * Real.sinh ξ := by rw [Real.sinh_eq]; ring
    have : 2 * Real.sinh ξ / (1 + x ^ 2) ≤ 2 * Real.sinh ξ :=
      div_le_self (by linarith) (by nlinarith [sq_nonneg x])
    linarith
  have hL : -ξ ≤ Real.log (sphU ξ x) := (Real.le_log_iff_exp_le (sphU_pos ξ x)).2 hlow
  rw [sphIntegrand, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h1, div_eq_mul_inv, re_wP_mul]
  gcongr
  linarith

lemma integrable_sphIntegrand (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) : Integrable (sphIntegrand ν ξ) :=
  (integrable_inv_one_add_sq.const_mul (Real.exp (ξ / 2))).mono'
    (continuous_sphIntegrand ν ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_sphIntegrand_le ν hξ))

/-- **Mehler's formula** for the spherical matrix coefficient:
`Φ^ν_{0,0}(ξ) = ∫_{-ξ}^{ξ} e^{iνt/2}/√(2(cosh ξ - cosh t)) dt` for `ξ > 0`. -/
theorem mcoefP_zero_zero_mehler (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    mcoefP ν 0 0 ξ = ∫ t in Ioo (-ξ) ξ, mehlerKernel ν ξ t := by
  have hint := integrable_sphIntegrand ν hξ
  have h0 : mcoefP ν 0 0 ξ = ∫ x, sphIntegrand ν ξ x := mcoefP_zero_zero ν ξ
  rw [h0, ← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
  have hneg : ∫ x in Iic (0 : ℝ), sphIntegrand ν ξ x = ∫ x in Ioi (0 : ℝ), sphIntegrand ν ξ x := by
    have := integral_comp_neg_Iic (0 : ℝ) (sphIntegrand ν ξ)
    simp only [sphIntegrand_neg, neg_zero] at this
    exact this
  rw [hneg, ← two_mul, ← image_log_sphU hξ,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_log_sphU ξ x).hasDerivWithinAt) (strictMonoOn_log_sphU hξ).injOn,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  exact (abs_mehlerDeriv_smul hξ hx).symm

lemma cosh_lt_cosh_of_abs_lt {t ξ : ℝ} (h : |t| < ξ) : Real.cosh t < Real.cosh ξ := by
  rw [Real.cosh_lt_cosh, abs_of_pos ((abs_nonneg t).trans_lt h)]; exact h

/-- **The inner Abel substitution** `w = √(2(cosh ξ - cosh t))` on `ξ > |t|`:
`∫_{ξ > |t|} sinh ξ F(cosh ξ)/√(2(cosh ξ - cosh t)) dξ = ∫_{w > 0} F(cosh t + w²/2) dw`. -/
theorem integral_Ioi_abs_sinh_div_sqrt (F : ℝ → ℂ) (t : ℝ) :
    ∫ ξ in Ioi |t|, ((Real.sinh ξ / Real.sqrt (2 * (Real.cosh ξ - Real.cosh t)) : ℝ) : ℂ) *
      F (Real.cosh ξ) = ∫ w in Ioi (0 : ℝ), F (Real.cosh t + w ^ 2 / 2) := by
  set f : ℝ → ℝ := fun ξ => Real.sqrt (2 * (Real.cosh ξ - Real.cosh t)) with hf
  have hpos : ∀ ξ ∈ Ioi |t|, 0 < 2 * (Real.cosh ξ - Real.cosh t) := fun ξ hξ => by
    have := cosh_lt_cosh_of_abs_lt (t := t) hξ; linarith
  have hder : ∀ ξ ∈ Ioi |t|, HasDerivWithinAt f (Real.sinh ξ / f ξ) (Ioi |t|) ξ := by
    intro ξ hξ
    have hin : HasDerivAt (fun ξ => 2 * (Real.cosh ξ - Real.cosh t)) (2 * Real.sinh ξ) ξ := by
      have := ((Real.hasDerivAt_cosh ξ).sub_const (Real.cosh t)).const_mul 2
      simpa using this
    have h := (hin.sqrt (hpos ξ hξ).ne').hasDerivWithinAt (s := Ioi |t|)
    convert h using 1
    have hs : Real.sqrt (2 * (Real.cosh ξ - Real.cosh t)) ≠ 0 := (Real.sqrt_pos.2 (hpos ξ hξ)).ne'
    simp only [hf]
    field_simp
  have hmono : StrictMonoOn f (Ioi |t|) := by
    intro a ha b hb hab
    have ha0 : 0 ≤ a := (abs_nonneg t).trans (le_of_lt ha)
    have hc : Real.cosh a < Real.cosh b := by
      rw [Real.cosh_lt_cosh, abs_of_nonneg ha0, abs_of_nonneg (ha0.trans hab.le)]; exact hab
    exact Real.sqrt_lt_sqrt (hpos a ha).le (by linarith)
  have himg : f '' Ioi |t| = Ioi 0 := by
    ext w
    constructor
    · rintro ⟨ξ, hξ, rfl⟩; exact Real.sqrt_pos.2 (hpos ξ hξ)
    · intro hw
      have hw' : (0 : ℝ) < w := hw
      have h1 : 1 ≤ Real.cosh t + w ^ 2 / 2 := by
        have := Real.one_le_cosh t; nlinarith [sq_nonneg w]
      refine ⟨Real.arcosh (Real.cosh t + w ^ 2 / 2), ?_, ?_⟩
      · have hc : Real.cosh t < Real.cosh (Real.arcosh (Real.cosh t + w ^ 2 / 2)) := by
          rw [Real.cosh_arcosh h1]; nlinarith
        rw [Real.cosh_lt_cosh, abs_of_nonneg (Real.arcosh_nonneg h1)] at hc
        exact hc
      · simp only [hf, Real.cosh_arcosh h1]
        rw [show 2 * (Real.cosh t + w ^ 2 / 2 - Real.cosh t) = w ^ 2 by ring]
        exact Real.sqrt_sq hw'.le
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hmono.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  have hξ0 : 0 < ξ := (abs_nonneg t).trans_lt hξ
  have hsq : f ξ ^ 2 = 2 * (Real.cosh ξ - Real.cosh t) := Real.sq_sqrt (hpos ξ hξ).le
  have hd : 0 < Real.sinh ξ / f ξ := div_pos (Real.sinh_pos_iff.2 hξ0) (Real.sqrt_pos.2 (hpos ξ hξ))
  rw [abs_of_pos hd, Complex.real_smul, hsq, show Real.cosh t + 2 * (Real.cosh ξ - Real.cosh t) / 2 =
    Real.cosh ξ by ring]

/-- `F ∘ g` has compact support when `F` does and `g x → ∞` as `|x| → ∞`. -/
lemma hasCompactSupport_comp_of_forall {F : ℝ → ℂ} (hc : HasCompactSupport F) {g : ℝ → ℝ}
    (hg : ∀ M, ∃ r, ∀ x, r < |x| → M < g x) : HasCompactSupport fun x => F (g x) := by
  obtain ⟨R, hR⟩ := hc.isCompact.bddAbove
  obtain ⟨r, hr⟩ := hg R
  refine HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun x hx => ?_
  have hx' : r < |x| := by
    by_contra h
    push Not at h
    exact hx (abs_le.1 h)
  by_contra hne
  have := hR (subset_tsupport F hne)
  linarith [hr x hx']

lemma cosh_ge_half_abs (ξ : ℝ) : (1 + |ξ|) / 2 ≤ Real.cosh ξ := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.add_one_le_exp |ξ|
  have := Real.exp_pos (-|ξ|)
  linarith

lemma hasCompactSupport_comp_cosh {F : ℝ → ℂ} (hc : HasCompactSupport F) :
    HasCompactSupport fun ξ => F (Real.cosh ξ) :=
  hasCompactSupport_comp_of_forall hc fun M => ⟨2 * |M| + 1, fun ξ hξ => by
    have := cosh_ge_half_abs ξ
    have := le_abs_self M
    linarith⟩

lemma hasCompactSupport_comp_abel {F : ℝ → ℂ} (hc : HasCompactSupport F) (t : ℝ) :
    HasCompactSupport fun w => F (Real.cosh t + w ^ 2 / 2) :=
  hasCompactSupport_comp_of_forall hc fun M => ⟨2 * |M| + 1, fun w hw => by
    have h1 := Real.one_le_cosh t
    have h2 := le_abs_self M
    have h3 : (2 * |M| + 1) ^ 2 < w ^ 2 := by
      rw [← sq_abs w]; exact pow_lt_pow_left₀ hw (by positivity) (by norm_num)
    nlinarith [abs_nonneg M]⟩

lemma integrableOn_mehlerKernel (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    IntegrableOn (mehlerKernel ν ξ) (Ioo (-ξ) ξ) := by
  rw [← image_log_sphU hξ, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (hasDerivAt_log_sphU ξ x).hasDerivWithinAt) (strictMonoOn_log_sphU hξ).injOn]
  refine (((integrable_sphIntegrand ν hξ).const_mul 2).integrableOn).congr_fun
    (fun x hx => (abs_mehlerDeriv_smul hξ hx).symm) measurableSet_Ioi

lemma integral_norm_mehlerKernel_le (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∫ t in Ioo (-ξ) ξ, ‖mehlerKernel ν ξ t‖ ≤ 2 * Real.exp (ξ / 2) * Real.pi := by
  have hint := integrable_sphIntegrand ν hξ
  rw [← image_log_sphU hξ, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ => (hasDerivAt_log_sphU ξ x).hasDerivWithinAt) (strictMonoOn_log_sphU hξ).injOn]
  have hc : ∫ x in Ioi (0 : ℝ), |mehlerDeriv ξ x| • ‖mehlerKernel ν ξ (Real.log (sphU ξ x))‖ =
      ∫ x in Ioi (0 : ℝ), ‖2 * sphIntegrand ν ξ x‖ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [← abs_mehlerDeriv_smul hξ hx, norm_smul, Real.norm_eq_abs, abs_abs, smul_eq_mul]
  rw [hc]
  calc ∫ x in Ioi (0 : ℝ), ‖2 * sphIntegrand ν ξ x‖
      ≤ ∫ x, ‖2 * sphIntegrand ν ξ x‖ :=
        setIntegral_le_integral (hint.const_mul 2).norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫ x, 2 * Real.exp (ξ / 2) * (1 + x ^ 2)⁻¹ := by
        refine integral_mono (hint.const_mul 2).norm
          (integrable_inv_one_add_sq.const_mul _) fun x => ?_
        rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_sphIntegrand_le ν hξ x) (by norm_num)
    _ = 2 * Real.exp (ξ / 2) * Real.pi := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

end Lightlike.Lorentz.SL2RPlancherel
