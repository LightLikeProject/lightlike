import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalKType

/-!
# The radial matrix coefficients of the even principal series

`Φ^ν_{m,n}(ξ) = ⟪e_m, π(a(ξ)) e_n⟫ = ∫ conj(e_m(x)) e^{-wξ} e_n(e^ξ x) dx` with `w = (iν - 1)/2`
(`mcoefP_eq_integral`).  The generator of the diagonal subgroup acts on the `K`-types by
`y e_n'(y) - w e_n(y) = ((w - n)/2) e_{n+1}(y) + ((w + n)/2) e_{n-1}(y)` (`deriv_kVecP_rel`), hence
`Φ'_{m,n} = ((w - n)/2) Φ_{m,n+1} + ((w + n)/2) Φ_{m,n-1}` (`hasDerivAt_mcoefP`, differentiation under
the integral, dominated by `C/(1 + x²)`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (identification of the block transforms with
matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Real Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The exponent `w = (iν - 1)/2` of the `K`-type vectors. -/
def wP (ν : ℝ) : ℂ := (I * ν - 1) / 2

/-- **The matrix coefficients as an integral**:
`Φ^ν_{m,n}(ξ) = ∫ conj(e_m(x)) e^{-wξ} e_n(e^ξ x) dx`. -/
theorem mcoefP_eq_integral (ν : ℝ) (m n : ℤ) (ξ : ℝ) :
    mcoefP ν m n ξ = ∫ x, (starRingEnd ℂ) (kVecP ν m x) *
      (Complex.exp (-(wP ν * ξ)) * kVecP ν n (Real.exp ξ * x)) := by
  rw [mcoefP, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 : (kVecL2 ν m : ℝ → ℂ) =ᵐ[volume] kVecP ν m := MemLp.coeFn_toLp (memLp_kVecP ν m)
  have h2 := coeFn_principalSeries 0 ν (aR ξ) (kVecL2 ν n)
  have h3 := ae_eq_comp_mob (aR ξ) (MemLp.coeFn_toLp (memLp_kVecP ν n))
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [Function.comp_apply] at e3
  rw [e1, e2, RCLike.inner_apply']
  congr 1
  have := act_aR ν ξ (kVecP ν n) x
  rw [act] at this
  rw [show (kVecL2 ν n : ℝ → ℂ) (mob (aR ξ) x) = kVecP ν n (mob (aR ξ) x) from e3, this, wP]
  congr 1
  · congr 1; ring

/-- The phase `u(x) = (x - i)/(x + i)` and its derivative `u' = 2i/(x + i)²`. -/
lemma hasDerivAt_phaseP (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) - I) / ((y : ℂ) + I)) (2 * I / ((x : ℂ) + I) ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) - I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.sub_const I
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) + I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const I
  have h := h1.div h2 (ofReal_add_I_ne_zero x)
  convert h using 1
  have hne := ofReal_add_I_ne_zero x
  field_simp
  ring

/-- The derivative of the `K`-type vector `e_n`. -/
lemma hasDerivAt_kVecP (ν : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (kVecP ν n)
      (wP ν * (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) * ((2 * x : ℝ) : ℂ) *
          (((x : ℂ) - I) / ((x : ℂ) + I)) ^ n +
        (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) *
          ((n : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ (n - 1) * (2 * I / ((x : ℂ) + I) ^ 2))) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hslit : (((1 + x ^ 2 : ℝ)) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := wP ν) hslit).hasDerivAt
  have hi : HasDerivAt (fun y : ℝ => (((1 + y ^ 2 : ℝ)) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have := ((hasDerivAt_id x).pow 2).const_add 1
    simpa using this.ofReal_comp
  have h1 := hc.comp x hi
  have hu := hasDerivAt_phaseP x
  have hune : ((x : ℂ) - I) / ((x : ℂ) + I) ≠ 0 :=
    div_ne_zero (ofReal_sub_I_ne_zero x) (ofReal_add_I_ne_zero x)
  have h2 := (hasDerivAt_zpow n _ (Or.inl hune)).comp x hu
  have h := h1.mul h2
  have hfun : kVecP ν n = ((fun z : ℂ => z ^ wP ν) ∘ fun y : ℝ => (((1 + y ^ 2 : ℝ)) : ℂ)) *
      ((fun z : ℂ => z ^ n) ∘ fun y : ℝ => ((y : ℂ) - I) / ((y : ℂ) + I)) := by
    funext y; simp [kVecP, wP]
  rw [hfun]
  convert h using 1
  simp only [Function.comp_apply]

/-- **The generator of the diagonal subgroup on the `K`-types**:
`x e_n'(x) - w e_n(x) = ((w - n)/2) e_{n+1}(x) + ((w + n)/2) e_{n-1}(x)`. -/
theorem deriv_kVecP_rel (ν : ℝ) (n : ℤ) (x : ℝ) :
    (x : ℂ) * (wP ν * (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) * ((2 * x : ℝ) : ℂ) *
          (((x : ℂ) - I) / ((x : ℂ) + I)) ^ n +
        (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) *
          ((n : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ (n - 1) * (2 * I / ((x : ℂ) + I) ^ 2))) -
      wP ν * kVecP ν n x =
      (wP ν - n) / 2 * kVecP ν (n + 1) x + (wP ν + n) / 2 * kVecP ν (n - 1) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hP0 : (((1 + x ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  have hune : ((x : ℂ) - I) / ((x : ℂ) + I) ≠ 0 := div_ne_zero hm hp
  set P := (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) with hP
  set u := ((x : ℂ) - I) / ((x : ℂ) + I) with hu
  have hPm : (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) = P / (((1 + x ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.cpow_sub _ _ hP0, Complex.cpow_one]
  have h1 : u ^ (n + 1) = u ^ n * u := zpow_add_one₀ hune n
  have h2 : u ^ (n - 1) = u ^ n / u := zpow_sub_one₀ hune n
  have hx2 : (((1 + x ^ 2 : ℝ)) : ℂ) = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  simp only [kVecP, show ((I * (ν : ℂ) - 1) / 2) = wP ν from rfl]
  rw [← hP, ← hu, hPm, h1, h2]
  rw [hx2] at hP0 ⊢
  rw [hu]
  field_simp
  push_cast
  ring

/-- **The `ξ`-derivative of `π(a(ξ)) e_n`, pointwise**:
`d/dξ [e^{-wξ} e_n(e^ξ x)] = e^{-wξ} [((w - n)/2) e_{n+1}(e^ξ x) + ((w + n)/2) e_{n-1}(e^ξ x)]`. -/
theorem hasDerivAt_act_aR_kVecP (ν : ℝ) (n : ℤ) (x ξ : ℝ) :
    HasDerivAt (fun ξ : ℝ => Complex.exp (-(wP ν * ξ)) * kVecP ν n (Real.exp ξ * x))
      (Complex.exp (-(wP ν * ξ)) * ((wP ν - n) / 2 * kVecP ν (n + 1) (Real.exp ξ * x) +
        (wP ν + n) / 2 * kVecP ν (n - 1) (Real.exp ξ * x))) ξ := by
  have he : HasDerivAt (fun ξ : ℝ => Complex.exp (-(wP ν * ξ)))
      (Complex.exp (-(wP ν * ξ)) * (-(wP ν))) ξ := by
    have h : HasDerivAt (fun ξ : ℝ => -(wP ν * (ξ : ℂ))) (-(wP ν)) ξ := by
      have := ((hasDerivAt_id ξ).ofReal_comp.const_mul (wP ν)).fun_neg
      simpa using this
    exact h.cexp
  have hy' : HasDerivAt (fun ξ : ℝ => Real.exp ξ * x) (Real.exp ξ * x) ξ :=
    (Real.hasDerivAt_exp ξ).mul_const x
  have hk := (hasDerivAt_kVecP ν n (Real.exp ξ * x)).scomp ξ hy'
  have h := he.mul hk
  have hrel := deriv_kVecP_rel ν n (Real.exp ξ * x)
  convert h using 1
  · funext t; rfl
  · rw [← hrel, Complex.real_smul]
    simp only [Function.comp_apply]
    push_cast
    ring

lemma norm_exp_neg_wP (ν ξ : ℝ) : ‖Complex.exp (-(wP ν * ξ))‖ = Real.exp (ξ / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [wP]
  ring

/-- `(1 + (e^ξ x)²)^{-1/2} ≤ c^{-1/2} (1 + x²)^{-1/2}` for `e^{2ξ} ≥ c`, `0 < c ≤ 1`. -/
lemma rpow_one_add_sq_exp_le {c ξ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hξ : c ≤ Real.exp ξ ^ 2) (x : ℝ) :
    (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2) ≤ c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have h1 : c * (1 + x ^ 2) ≤ 1 + (Real.exp ξ * x) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg x]
  rw [← Real.mul_rpow hc.le (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)

/-- The integrand `conj(e_m(x)) e^{-wξ} e_k(e^ξ x)` of the matrix coefficients. -/
def mcoefIntegrand (ν : ℝ) (m k : ℤ) (ξ x : ℝ) : ℂ :=
  (starRingEnd ℂ) (kVecP ν m x) * (Complex.exp (-(wP ν * ξ)) * kVecP ν k (Real.exp ξ * x))

lemma continuous_mcoefIntegrand (ν : ℝ) (m k : ℤ) (ξ : ℝ) : Continuous (mcoefIntegrand ν m k ξ) :=
  (Complex.continuous_conj.comp (continuous_kVecP ν m)).mul
    (continuous_const.mul ((continuous_kVecP ν k).comp (continuous_const.mul continuous_id)))

/-- The bound `‖conj(e_m(x)) e^{-wξ} e_k(e^ξ x)‖ ≤ e^{ξ/2} c^{-1/2} / (1 + x²)` for `e^{2ξ} ≥ c`. -/
lemma norm_mcoefIntegrand_le (ν : ℝ) (m k : ℤ) {c ξ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hξ : c ≤ Real.exp ξ ^ 2) (x : ℝ) :
    ‖mcoefIntegrand ν m k ξ x‖ ≤ Real.exp (ξ / 2) * c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2)⁻¹ := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [mcoefIntegrand, norm_mul, norm_mul, Complex.norm_conj, norm_kVecP, norm_kVecP, norm_exp_neg_wP]
  have h1 := rpow_one_add_sq_exp_le hc hc1 hξ x
  have h2 : (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) = (1 + x ^ 2)⁻¹ := by
    rw [← Real.rpow_add hpos]; norm_num; exact Real.rpow_neg_one _
  calc (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * (Real.exp (ξ / 2) * (1 + (Real.exp ξ * x) ^ 2) ^ (-(1 : ℝ) / 2))
      ≤ (1 + x ^ 2) ^ (-(1 : ℝ) / 2) * (Real.exp (ξ / 2) *
          (c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2))) := by
        gcongr
    _ = Real.exp (ξ / 2) * c ^ (-(1 : ℝ) / 2) * ((1 + x ^ 2) ^ (-(1 : ℝ) / 2) *
          (1 + x ^ 2) ^ (-(1 : ℝ) / 2)) := by ring
    _ = _ := by rw [h2]

lemma integrable_mcoefIntegrand (ν : ℝ) (m k : ℤ) (ξ : ℝ) : Integrable (mcoefIntegrand ν m k ξ) := by
  set c : ℝ := min 1 (Real.exp ξ ^ 2) with hcdef
  have hc : 0 < c := lt_min one_pos (by positivity)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (Real.exp (ξ / 2) * c ^ (-(1 : ℝ) / 2)))
    (continuous_mcoefIntegrand ν m k ξ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  exact norm_mcoefIntegrand_le ν m k hc (min_le_left _ _) (min_le_right _ _) x

/-- **The derivative of the matrix coefficients**:
`Φ'_{m,n}(ξ) = ((w - n)/2) Φ_{m,n+1}(ξ) + ((w + n)/2) Φ_{m,n-1}(ξ)`. -/
theorem hasDerivAt_mcoefP (ν : ℝ) (m n : ℤ) (ξ₀ : ℝ) :
    HasDerivAt (mcoefP ν m n) ((wP ν - n) / 2 * mcoefP ν m (n + 1) ξ₀ +
      (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ₀) ξ₀ := by
  set a : ℂ := (wP ν - n) / 2 with ha
  set b : ℂ := (wP ν + n) / 2 with hb
  set F' : ℝ → ℝ → ℂ := fun ξ x =>
    a * mcoefIntegrand ν m (n + 1) ξ x + b * mcoefIntegrand ν m (n - 1) ξ x with hF'
  have hfun : mcoefP ν m n = fun ξ => ∫ x, mcoefIntegrand ν m n ξ x :=
    funext fun ξ => mcoefP_eq_integral ν m n ξ
  set c : ℝ := min 1 (Real.exp (ξ₀ - 1) ^ 2) with hcdef
  have hc : 0 < c := lt_min one_pos (by positivity)
  set C : ℝ := (‖a‖ + ‖b‖) * (Real.exp ((ξ₀ + 1) / 2) * c ^ (-(1 : ℝ) / 2)) with hC
  have hbound : ∀ x, ∀ ξ ∈ Metric.ball ξ₀ 1, ‖F' ξ x‖ ≤ C * (1 + x ^ 2)⁻¹ := by
    intro x ξ hξ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hξ
    have hcξ : c ≤ Real.exp ξ ^ 2 := (min_le_right _ _).trans
      (pow_le_pow_left₀ (by positivity) (Real.exp_le_exp.2 (by linarith)) 2)
    have he : Real.exp (ξ / 2) ≤ Real.exp ((ξ₀ + 1) / 2) := Real.exp_le_exp.2 (by linarith)
    have k1 := norm_mcoefIntegrand_le ν m (n + 1) hc (min_le_left _ _) hcξ x
    have k2 := norm_mcoefIntegrand_le ν m (n - 1) hc (min_le_left _ _) hcξ x
    have hD : 0 ≤ c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2)⁻¹ := by positivity
    calc ‖F' ξ x‖ ≤ ‖a‖ * ‖mcoefIntegrand ν m (n + 1) ξ x‖ + ‖b‖ * ‖mcoefIntegrand ν m (n - 1) ξ x‖ := by
          simp only [hF']; exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ ‖a‖ * (Real.exp ((ξ₀ + 1) / 2) * c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2)⁻¹) +
          ‖b‖ * (Real.exp ((ξ₀ + 1) / 2) * c ^ (-(1 : ℝ) / 2) * (1 + x ^ 2)⁻¹) := by
          gcongr
          · exact k1.trans (by nlinarith [mul_le_mul_of_nonneg_right he hD])
          · exact k2.trans (by nlinarith [mul_le_mul_of_nonneg_right he hD])
      _ = C * (1 + x ^ 2)⁻¹ := by simp only [hC]; ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := mcoefIntegrand ν m n)
    (F' := F') (x₀ := ξ₀) (bound := fun x => C * (1 + x ^ 2)⁻¹) (Metric.ball_mem_nhds ξ₀ one_pos)
    (Filter.Eventually.of_forall fun ξ => (continuous_mcoefIntegrand ν m n ξ).aestronglyMeasurable)
    (integrable_mcoefIntegrand ν m n ξ₀)
    (((continuous_mcoefIntegrand ν m (n + 1) ξ₀).const_smul a).add
      ((continuous_mcoefIntegrand ν m (n - 1) ξ₀).const_smul b)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ξ hξ => hbound x ξ hξ)
    (integrable_inv_one_add_sq.const_mul C)
    (Filter.Eventually.of_forall fun x ξ _ => by
      have := (hasDerivAt_act_aR_kVecP ν n x ξ).const_mul ((starRingEnd ℂ) (kVecP ν m x))
      show HasDerivAt (fun ξ => mcoefIntegrand ν m n ξ x) (F' ξ x) ξ
      have e : F' ξ x = (starRingEnd ℂ) (kVecP ν m x) * (Complex.exp (-(wP ν * ξ)) *
          ((wP ν - n) / 2 * kVecP ν (n + 1) (Real.exp ξ * x) +
            (wP ν + n) / 2 * kVecP ν (n - 1) (Real.exp ξ * x))) := by
        simp only [hF', mcoefIntegrand, ha, hb]; ring
      rw [e]
      exact this)
  rw [hfun]
  convert h.2 using 1
  simp only [hF']
  rw [integral_add ((integrable_mcoefIntegrand ν m (n + 1) ξ₀).const_mul a)
      ((integrable_mcoefIntegrand ν m (n - 1) ξ₀).const_mul b), integral_const_mul, integral_const_mul,
    mcoefP_eq_integral, mcoefP_eq_integral]
  rfl

end Lightlike.Lorentz.SL2RPlancherel
