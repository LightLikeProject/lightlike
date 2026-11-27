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

end Lightlike.Lorentz.SL2RPlancherel
