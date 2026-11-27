import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalKType
import Lightlike.Lorentz.SL2RPlancherel.Ladder

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

/-- `num² + den² > 0`: the column `(num, den) = gᵀ (x, 1)` does not vanish. -/
lemma num_sq_add_den_sq_pos (g : SL2R) (x : ℝ) : 0 < num g x ^ 2 + den g x ^ 2 := by
  by_contra h
  push Not at h
  have h1 : num g x = 0 := by nlinarith [sq_nonneg (num g x), sq_nonneg (den g x)]
  have h2 : den g x = 0 := by nlinarith [sq_nonneg (num g x), sq_nonneg (den g x)]
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; linarith
  simp only [num, den] at h1 h2
  -- `x = (g11 num - g10 den)`, `1 = (g00 den - g01 num)` up to the determinant
  have : (1 : ℝ) = g 0 0 * (g 0 1 * x + g 1 1) - g 0 1 * (g 0 0 * x + g 1 0) := by
    linear_combination -hdet
  rw [h1, h2] at this
  simp at this

/-- **The `K`-type vectors under any group element, in smooth form**: off the pole,
`(π(g) e_n)(x) = (num² + den²)^w ((num - i den)/(num + i den))^n` with `num = num g x`,
`den = den g x`; the singularities of the multiplier and of `e_n ∘ mob` cancel. -/
theorem act_kVecP_eq (ν : ℝ) (n : ℤ) (g : SL2R) (x : ℝ) (hx : den g x ≠ 0) :
    act 0 ν g (kVecP ν n) x =
      (((num g x ^ 2 + den g x ^ 2 : ℝ)) : ℂ) ^ (wP ν) *
        ((((num g x : ℝ) : ℂ) - I * (den g x : ℂ)) / (((num g x : ℝ) : ℂ) + I * (den g x : ℂ))) ^ n := by
  set d := den g x with hd
  set N := num g x with hN
  have had : 0 < |d| := abs_pos.mpr hx
  have hA : 0 ≤ N ^ 2 + d ^ 2 := by positivity
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  -- the modulus
  have e : (1 + mob g x ^ 2 : ℝ) = (N ^ 2 + d ^ 2) * (|d| * |d|)⁻¹ := by
    rw [abs_mul_abs_self, mob, ← hN, ← hd]; field_simp; ring
  have harg : ((((|d| * |d| : ℝ)) : ℂ)).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have hmod : (((1 + mob g x ^ 2 : ℝ)) : ℂ) ^ (wP ν) =
      (((N ^ 2 + d ^ 2 : ℝ)) : ℂ) ^ (wP ν) * ((((|d| : ℝ) : ℂ)) ^ (wP ν) * (((|d| : ℝ) : ℂ)) ^ (wP ν))⁻¹ := by
    rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hA
      (inv_nonneg.2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _)]
  have hmult : mult 0 ν d = (((|d| : ℝ) : ℂ)) ^ (wP ν) * (((|d| : ℝ) : ℂ)) ^ (wP ν) := by
    rw [mult, zpow_zero, mul_one, show I * (ν : ℂ) - 1 = (2 : ℕ) * wP ν by rw [wP]; push_cast; ring,
      Complex.cpow_nat_mul, sq]
  have hne : (((|d| : ℝ) : ℂ)) ^ (wP ν) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not
    intro h; exact absurd (by exact_mod_cast h) had.ne'
  -- the phase
  have hph : ((mob g x : ℂ) - I) / ((mob g x : ℂ) + I) =
      (((N : ℝ) : ℂ) - I * (d : ℂ)) / (((N : ℝ) : ℂ) + I * (d : ℂ)) := by
    have hmob : (mob g x : ℂ) = ((N : ℝ) : ℂ) / ((d : ℝ) : ℂ) := by simp [mob, hN, hd]
    have hden : ((N : ℝ) : ℂ) + I * (d : ℂ) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hx this
    rw [hmob]
    field_simp
  rw [act, kVecP, show ((I * (ν : ℂ) - 1) / 2) = wP ν from rfl, hmult, hmod, hph]
  field_simp

/-- The smooth form `Q(N, D) = (N² + D²)^w ((N - iD)/(N + iD))^n` of `π(g) e_n`. -/
def qForm (ν : ℝ) (n : ℤ) (N D : ℝ) : ℂ :=
  (((N ^ 2 + D ^ 2 : ℝ)) : ℂ) ^ (wP ν) * ((((N : ℝ) : ℂ) - I * (D : ℂ)) / (((N : ℝ) : ℂ) + I * (D : ℂ))) ^ n

/-- **Matrix coefficients against an arbitrary vector**:
`⟪f, π(g) e_n⟫ = ∫ conj(f(x)) Q(num g x, den g x) dx`. -/
theorem inner_principalSeries_kVecL2 (ν : ℝ) (n : ℤ) (f : L2R) (g : SL2R) :
    inner ℂ f (principalSeries 0 ν g (kVecL2 ν n)) =
      ∫ x, (starRingEnd ℂ) (f x) * qForm ν n (num g x) (den g x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h2 := coeFn_principalSeries 0 ν g (kVecL2 ν n)
  have h3 := ae_eq_comp_mob g (MemLp.coeFn_toLp (memLp_kVecP ν n))
  filter_upwards [h2, h3, ae_den_ne_zero g] with x e2 e3 hx
  simp only [Function.comp_apply] at e3
  rw [e2, RCLike.inner_apply']
  congr 1
  have := act_kVecP_eq ν n g x hx
  rw [act] at this
  rw [show (kVecL2 ν n : ℝ → ℂ) (mob g x) = kVecP ν n (mob g x) from e3, this, qForm]

/-- **A uniform lower bound**: `1 + x² ≤ (Σ g_ij²)(num² + den²)` for `g ∈ SL(2,ℝ)` (`det g = 1`). -/
lemma one_add_sq_le_num_den (g : SL2R) (x : ℝ) :
    1 + x ^ 2 ≤ (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) * (num g x ^ 2 + den g x ^ 2) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; linarith
  have hx : x = g 1 1 * num g x - g 1 0 * den g x := by
    simp only [num, den]; linear_combination (-x) * hdet
  have h1 : (1 : ℝ) = g 0 0 * den g x - g 0 1 * num g x := by
    simp only [num, den]; linear_combination -hdet
  have c1 : (g 1 1 * num g x - g 1 0 * den g x) ^ 2 ≤
      (g 1 1 ^ 2 + g 1 0 ^ 2) * (num g x ^ 2 + den g x ^ 2) := by
    nlinarith [sq_nonneg (g 1 1 * den g x + g 1 0 * num g x)]
  have c2 : (g 0 0 * den g x - g 0 1 * num g x) ^ 2 ≤
      (g 0 0 ^ 2 + g 0 1 ^ 2) * (num g x ^ 2 + den g x ^ 2) := by
    nlinarith [sq_nonneg (g 0 0 * num g x + g 0 1 * den g x)]
  have hn : 0 ≤ num g x ^ 2 + den g x ^ 2 := by positivity
  calc 1 + x ^ 2 = (g 0 0 * den g x - g 0 1 * num g x) ^ 2 +
        (g 1 1 * num g x - g 1 0 * den g x) ^ 2 := by rw [← h1, ← hx]; ring
    _ ≤ (g 0 0 ^ 2 + g 0 1 ^ 2) * (num g x ^ 2 + den g x ^ 2) +
        (g 1 1 ^ 2 + g 1 0 ^ 2) * (num g x ^ 2 + den g x ^ 2) := add_le_add c2 c1
    _ = _ := by ring

lemma norm_qForm (ν : ℝ) (n : ℤ) {N D : ℝ} (h : 0 < N ^ 2 + D ^ 2) :
    ‖qForm ν n N D‖ = (N ^ 2 + D ^ 2) ^ (-(1 : ℝ) / 2) := by
  have hden : ((N : ℝ) : ℂ) + I * (D : ℂ) ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    rw [hr, hi] at h; simp at h
  have hph : ‖(((N : ℝ) : ℂ) - I * (D : ℂ)) / (((N : ℝ) : ℂ) + I * (D : ℂ))‖ = 1 := by
    rw [norm_div]
    have h1 : ‖((N : ℝ) : ℂ) - I * (D : ℂ)‖ = ‖((N : ℝ) : ℂ) + I * (D : ℂ)‖ := by
      rw [← Complex.norm_conj (((N : ℝ) : ℂ) + I * (D : ℂ))]
      simp [map_add, sub_eq_add_neg]
    rw [h1, div_self (norm_ne_zero_iff.mpr hden)]
  rw [qForm, norm_mul, norm_zpow, hph, one_zpow, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos h]
  congr 1
  simp [wP]

/-- The curve `c(t) = a(ξ)⁻¹ k_t a(ξ)`. -/
def cT (ξ t : ℝ) : SL2R := aR (-ξ) * rot t * aR ξ

lemma num_cT (ξ t x : ℝ) : num (cT ξ t) x = Real.cos t * x - Real.exp ξ * Real.sin t := by
  have h : Real.exp ξ = Real.exp (ξ / 2) * Real.exp (ξ / 2) := by rw [← Real.exp_add]; ring_nf
  simp [num, cT, aR, diagSL, rot, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h, show -ξ / 2 = -(ξ / 2) by ring, Real.exp_neg]
  field_simp
  ring

lemma den_cT (ξ t x : ℝ) : den (cT ξ t) x = Real.exp (-ξ) * Real.sin t * x + Real.cos t := by
  have h : Real.exp (-ξ) = Real.exp (-(ξ / 2)) * Real.exp (-(ξ / 2)) := by
    rw [← Real.exp_add]; ring_nf
  simp [den, cT, aR, diagSL, rot, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h, show -ξ / 2 = -(ξ / 2) by ring, Real.exp_neg]
  field_simp

/-- **The derivative of the smooth form along a curve**: for differentiable `N, D` with
`N² + D² > 0`, `d/dt Q(N, D) = Q · (w · 2(N N' + D D')/(N² + D²) + n · 2i(N' D - N D')/(N² + D²))`. -/
theorem hasDerivAt_qForm_comp (ν : ℝ) (n : ℤ) {N D : ℝ → ℝ} {N' D' t : ℝ}
    (hN : HasDerivAt N N' t) (hD : HasDerivAt D D' t) (hpos : 0 < N t ^ 2 + D t ^ 2) :
    HasDerivAt (fun t => qForm ν n (N t) (D t))
      (qForm ν n (N t) (D t) * (wP ν * ((2 * (N t * N' + D t * D') : ℝ) / (N t ^ 2 + D t ^ 2 : ℝ)) +
        (n : ℂ) * (2 * I * ((N' * D t - N t * D' : ℝ) : ℂ)) / ((N t ^ 2 + D t ^ 2 : ℝ) : ℂ))) t := by
  set A : ℝ := N t ^ 2 + D t ^ 2 with hA
  have hslit : ((A : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hAd : HasDerivAt (fun s => (((N s ^ 2 + D s ^ 2 : ℝ)) : ℂ)) (((2 * (N t * N' + D t * D') : ℝ)) : ℂ) t := by
    have := ((hN.pow 2).add (hD.pow 2)).ofReal_comp
    convert this using 1; push_cast; ring
  have h1 := (Complex.hasStrictDerivAt_cpow_const (c := wP ν) hslit).hasDerivAt.comp t hAd
  have hden : ((N t : ℝ) : ℂ) + I * (D t : ℂ) ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    rw [hA, hr, hi] at hpos; simp at hpos
  have hnum : ((N t : ℝ) : ℂ) - I * (D t : ℂ) ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp at hr hi
    rw [hA, hr, hi] at hpos; simp at hpos
  have hNc : HasDerivAt (fun s => ((N s : ℝ) : ℂ)) ((N' : ℝ) : ℂ) t := hN.ofReal_comp
  have hDc : HasDerivAt (fun s => ((D s : ℝ) : ℂ)) ((D' : ℝ) : ℂ) t := hD.ofReal_comp
  have hP := (hNc.sub (hDc.const_mul I)).div (hNc.add (hDc.const_mul I)) hden
  have hPne : (((N t : ℝ) : ℂ) - I * (D t : ℂ)) / (((N t : ℝ) : ℂ) + I * (D t : ℂ)) ≠ 0 :=
    div_ne_zero hnum hden
  have h2 := (hasDerivAt_zpow n _ (Or.inl hPne)).comp t hP
  have h := h1.mul h2
  have hfun : (fun t => qForm ν n (N t) (D t)) = ((fun z : ℂ => z ^ wP ν) ∘
      fun s => (((N s ^ 2 + D s ^ 2 : ℝ)) : ℂ)) * ((fun z : ℂ => z ^ n) ∘
      fun s => (((N s : ℝ) : ℂ) - I * (D s : ℂ)) / (((N s : ℝ) : ℂ) + I * (D s : ℂ))) := by
    funext s; simp [qForm]
  rw [hfun]
  convert h using 1
  simp only [Function.comp_apply, qForm, Pi.sub_apply, Pi.add_apply, Pi.div_apply]
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcpow : (((A : ℝ)) : ℂ) ^ (wP ν - 1) = (((A : ℝ)) : ℂ) ^ (wP ν) / ((A : ℝ) : ℂ) := by
    rw [Complex.cpow_sub _ _ hA0, Complex.cpow_one]
  rw [show (((N t ^ 2 + D t ^ 2 : ℝ)) : ℂ) = ((A : ℝ) : ℂ) from rfl, hcpow,
    zpow_sub_one₀ hPne]
  have hAeq : ((A : ℝ) : ℂ) = (((N t : ℝ) : ℂ) - I * (D t : ℂ)) * (((N t : ℝ) : ℂ) + I * (D t : ℂ)) := by
    rw [hA]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [hAeq] at hA0 ⊢
  field_simp
  push_cast
  ring_nf

lemma qForm_one (ν : ℝ) (n : ℤ) (x : ℝ) : qForm ν n x 1 = kVecP ν n x := by
  simp only [qForm, kVecP, mul_one, Complex.ofReal_one, show ((I * (ν : ℂ) - 1) / 2) = wP ν from rfl]
  congr 2
  ring

/-- `t ↦ (num, den)(c(t), x)` has derivative `(-sin t x - e^ξ cos t, e^{-ξ} cos t x - sin t)`. -/
lemma hasDerivAt_num_cT (ξ x t : ℝ) :
    HasDerivAt (fun t => num (cT ξ t) x) (-(Real.sin t) * x - Real.exp ξ * Real.cos t) t := by
  have h : (fun t => num (cT ξ t) x) = fun t => Real.cos t * x - Real.exp ξ * Real.sin t :=
    funext fun t => num_cT ξ t x
  rw [h]
  have := ((Real.hasDerivAt_cos t).mul_const x).sub ((Real.hasDerivAt_sin t).const_mul (Real.exp ξ))
  convert this using 1

lemma hasDerivAt_den_cT (ξ x t : ℝ) :
    HasDerivAt (fun t => den (cT ξ t) x) (Real.exp (-ξ) * Real.cos t * x - Real.sin t) t := by
  have h : (fun t => den (cT ξ t) x) = fun t => Real.exp (-ξ) * Real.sin t * x + Real.cos t :=
    funext fun t => den_cT ξ t x
  rw [h]
  have := (((Real.hasDerivAt_sin t).const_mul (Real.exp (-ξ))).mul_const x).add (Real.hasDerivAt_cos t)
  convert this using 1

/-- **The derivative along `c(t)` at `t = 0`, in `K`-types**:
`d/dt|₀ (π(c(t)) e_n)(x) = -2in cosh ξ e_n(x) - i sinh ξ (w - n) e_{n+1}(x) + i sinh ξ (w + n) e_{n-1}(x)`. -/
theorem hasDerivAt_qForm_cT_zero (ν : ℝ) (n : ℤ) (ξ x : ℝ) :
    HasDerivAt (fun t => qForm ν n (num (cT ξ t) x) (den (cT ξ t) x))
      (-(2 * I * n * Real.cosh ξ) * kVecP ν n x -
        I * Real.sinh ξ * (wP ν - n) * kVecP ν (n + 1) x +
        I * Real.sinh ξ * (wP ν + n) * kVecP ν (n - 1) x) 0 := by
  have hpos := num_sq_add_den_sq_pos (cT ξ 0) x
  have h := hasDerivAt_qForm_comp ν n (hasDerivAt_num_cT ξ x 0) (hasDerivAt_den_cT ξ x 0) hpos
  convert h using 1
  have hN : num (cT ξ 0) x = x := by rw [num_cT]; simp
  have hD : den (cT ξ 0) x = 1 := by rw [den_cT]; simp
  rw [hN, hD, qForm_one]
  simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, mul_one, zero_sub, sub_zero]
  -- `e_{n±1} = e_n u^{±1}` and the hyperbolic functions in exponentials
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  have hune : ((x : ℂ) - I) / ((x : ℂ) + I) ≠ 0 := div_ne_zero hm hp
  have h1 : kVecP ν (n + 1) x = kVecP ν n x * (((x : ℂ) - I) / ((x : ℂ) + I)) := by
    simp only [kVecP]; rw [zpow_add_one₀ hune]; ring
  have h2 : kVecP ν (n - 1) x = kVecP ν n x / (((x : ℂ) - I) / ((x : ℂ) + I)) := by
    simp only [kVecP]; rw [zpow_sub_one₀ hune]; ring
  have hx2 : (((x ^ 2 + 1 : ℝ)) : ℂ) = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hE : Real.exp ξ * Real.exp (-ξ) = 1 := by rw [← Real.exp_add]; simp
  rw [h1, h2, Real.cosh_eq, Real.sinh_eq]
  rw [show (x ^ 2 + 1 ^ 2 : ℝ) = x ^ 2 + 1 by ring, hx2]
  have hEC : ((Real.exp ξ : ℝ) : ℂ) * ((Real.exp (-ξ) : ℝ) : ℂ) = 1 := by exact_mod_cast hE
  field_simp
  push_cast
  linear_combination (2 * kVecP ν n x * x * wP ν * (Complex.exp ξ - Complex.exp (-ξ)) +
    2 * I * kVecP ν n x * n * Complex.exp ξ) * Complex.I_sq

lemma aR_mul_aR_neg (ξ : ℝ) : aR ξ * aR (-ξ) = 1 := by
  ext i j
  have h : Real.exp (ξ / 2) * Real.exp (-(ξ / 2)) = 1 := by
    rw [← Real.exp_add, show ξ / 2 + -(ξ / 2) = 0 by ring, Real.exp_zero]
  have h' : (Real.exp (ξ / 2))⁻¹ * (Real.exp (-(ξ / 2)))⁻¹ = 1 := by rw [← mul_inv, h, inv_one]
  fin_cases i <;> fin_cases j <;>
    simp [aR, diagSL, Matrix.mul_apply, Fin.sum_univ_two, neg_div, h, h']

lemma aR_neg_mul_aR (ξ : ℝ) : aR (-ξ) * aR ξ = 1 := by
  simpa using aR_mul_aR_neg (-ξ)

lemma aR_mul_cT (ξ t : ℝ) : aR ξ * cT ξ t = rot t * aR ξ := by
  rw [cT, ← mul_assoc, ← mul_assoc, aR_mul_aR_neg, one_mul]

/-- **The exact rotation identity**: `⟪π(a(-ξ)) e_m, π(c(t)) e_n⟫ = e^{-2imt} Φ^ν_{m,n}(ξ)`. -/
theorem inner_cT_eq (ν ξ t : ℝ) (m n : ℤ) :
    inner ℂ (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m)) (principalSeries 0 ν (cT ξ t) (kVecL2 ν n)) =
      Complex.exp (-(2 * m * t * I)) * mcoefP ν m n ξ := by
  have hu := principalSeries_inner 0 ν (aR ξ) (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m))
    (principalSeries 0 ν (cT ξ t) (kVecL2 ν n))
  rw [← hu, ← mul_apply_eq_comp, ← principalSeries_mul, aR_mul_aR_neg,
    principalSeries_one, one_apply_eq_self, ← mul_apply_eq_comp,
    ← principalSeries_mul, aR_mul_cT]
  have h := inner_kVecL2_kak ν t ξ 0 m n
  rw [rot_zero, mul_one] at h
  rw [h]
  congr 1
  push_cast
  ring_nf

/-- `⟪π(a(-ξ)) e_m, e_k⟫ = Φ^ν_{m,k}(ξ)`. -/
lemma inner_aR_neg_kVecL2 (ν ξ : ℝ) (m k : ℤ) :
    inner ℂ (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m)) (kVecL2 ν k) = mcoefP ν m k ξ := by
  have hu := principalSeries_inner 0 ν (aR ξ) (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m))
    (kVecL2 ν k)
  rw [← hu, ← mul_apply_eq_comp, ← principalSeries_mul, aR_mul_aR_neg,
    principalSeries_one, one_apply_eq_self, mcoefP]

/-- From `A ≥ (1 + x²)/S`: `A^{-1/2} ≤ S^{1/2} (1 + x²)^{-1/2}`. -/
lemma rpow_neg_half_le_of_le {A S x : ℝ} (hS : 0 < S) (hA : (1 + x ^ 2) ≤ S * A) :
    A ^ (-(1 : ℝ) / 2) ≤ S ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have hx : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hA0 : 0 < A := by
    by_contra h; push Not at h; nlinarith
  have h1 : (1 + x ^ 2) * S⁻¹ ≤ A := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hS]; linarith
  calc A ^ (-(1 : ℝ) / 2) ≤ ((1 + x ^ 2) * S⁻¹) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    _ = S ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
        rw [Real.mul_rpow hx.le (by positivity), Real.inv_rpow hS.le, ← Real.rpow_neg hS.le]
        ring_nf

/-- **The size of `π(g) e_n`**: `‖Q(num g x, den g x)‖ ≤ (Σ g_ij²)^{1/2} (1 + x²)^{-1/2}`. -/
lemma norm_qForm_le (ν : ℝ) (n : ℤ) (g : SL2R) (x : ℝ) :
    ‖qForm ν n (num g x) (den g x)‖ ≤
      (g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2) ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
  have hpos := num_sq_add_den_sq_pos g x
  have hS : 0 < g 0 0 ^ 2 + g 0 1 ^ 2 + g 1 0 ^ 2 + g 1 1 ^ 2 := by
    by_contra h; push Not at h
    have := one_add_sq_le_num_den g x
    nlinarith [sq_nonneg x]
  rw [norm_qForm ν n hpos]
  exact rpow_neg_half_le_of_le hS (one_add_sq_le_num_den g x)

lemma cT_entries (ξ t : ℝ) :
    (cT ξ t) 0 0 = Real.cos t ∧ (cT ξ t) 0 1 = Real.exp (-ξ) * Real.sin t ∧
      (cT ξ t) 1 0 = -(Real.exp ξ * Real.sin t) ∧ (cT ξ t) 1 1 = Real.cos t := by
  have h00 := num_cT ξ t 0
  have h01 := den_cT ξ t 1
  have h10 := num_cT ξ t 1
  have h11 := den_cT ξ t 0
  simp only [num, den, mul_zero, zero_add, mul_one] at h00 h01 h10 h11
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The squared entries of `c(t)` are bounded uniformly in `t`. -/
lemma cT_sq_le (ξ t : ℝ) :
    (cT ξ t) 0 0 ^ 2 + (cT ξ t) 0 1 ^ 2 + (cT ξ t) 1 0 ^ 2 + (cT ξ t) 1 1 ^ 2 ≤
      2 + Real.exp ξ ^ 2 + Real.exp (-ξ) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := cT_entries ξ t
  rw [h1, h2, h3, h4]
  have hs := Real.sin_sq_le_one t
  have hc := Real.cos_sq_le_one t
  nlinarith [sq_nonneg (Real.exp ξ), sq_nonneg (Real.exp (-ξ)), sq_nonneg (Real.sin t),
    mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.exp ξ)),
    mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.exp (-ξ)))]

/-- The function `(1 + x²)^{-1/2}` as a vector of `L²(ℝ)`. -/
lemma memLp_rpow_neg_half : MemLp (fun x : ℝ => (((1 + x ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)) 2 volume := by
  have hc : Continuous fun x : ℝ => (((1 + x ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (continuous_id.pow 2)).rpow_const
      fun x => Or.inl (by have : (0 : ℝ) < 1 + x ^ 2 := by positivity
                          exact this.ne'))
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  refine integrable_inv_one_add_sq.congr (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_mul_natCast hpos.le]
  norm_num
  rw [Real.rpow_neg_one]

/-- `conj(f x) g x` is integrable for `f, g ∈ L²(ℝ)`. -/
lemma integrable_conj_mul (f g : L2R) :
    Integrable (fun x => (starRingEnd ℂ) (f x) * g x) := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f g
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.inner_apply', mul_comm]

/-- The logarithmic derivative of `π(c(t)) e_n` in `t`. -/
def rotLogDeriv (ν : ℝ) (n : ℤ) (ξ t x : ℝ) : ℂ :=
  wP ν * ((2 * (num (cT ξ t) x * (-(Real.sin t) * x - Real.exp ξ * Real.cos t) +
      den (cT ξ t) x * (Real.exp (-ξ) * Real.cos t * x - Real.sin t)) : ℝ) /
      (num (cT ξ t) x ^ 2 + den (cT ξ t) x ^ 2 : ℝ)) +
    (n : ℂ) * (2 * I * (((-(Real.sin t) * x - Real.exp ξ * Real.cos t) * den (cT ξ t) x -
      num (cT ξ t) x * (Real.exp (-ξ) * Real.cos t * x - Real.sin t) : ℝ) : ℂ)) /
      ((num (cT ξ t) x ^ 2 + den (cT ξ t) x ^ 2 : ℝ) : ℂ)

lemma abs_lin_le {E a b c d x : ℝ} (hE1 : 1 ≤ E) (hc : |c| ≤ E) (hd : |d| ≤ E) (ha : |a| ≤ 1)
    (hb : |b| ≤ 1) : |c * a * x + d * b| ≤ E * (1 + |x|) := by
  have h1 : |c * a * x| ≤ E * |x| := by
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg c, abs_nonneg a, abs_nonneg x, mul_le_mul_of_nonneg_left ha (abs_nonneg c)]
  have h2 : |d * b| ≤ E := by rw [abs_mul]; nlinarith [abs_nonneg d, abs_nonneg b]
  calc |c * a * x + d * b| ≤ |c * a * x| + |d * b| := abs_add_le _ _
    _ ≤ E * |x| + E := add_le_add h1 h2
    _ = E * (1 + |x|) := by ring

set_option maxHeartbeats 400000 in
/-- **The logarithmic derivative is bounded** uniformly in `t` and `x`. -/
lemma norm_rotLogDeriv_le (ν : ℝ) (n : ℤ) (ξ t x : ℝ) :
    ‖rotLogDeriv ν n ξ t x‖ ≤ 16 * (‖wP ν‖ + |(n : ℝ)|) * (1 + Real.exp ξ + Real.exp (-ξ)) ^ 2 *
      (2 + Real.exp ξ ^ 2 + Real.exp (-ξ) ^ 2) := by
  set E := 1 + Real.exp ξ + Real.exp (-ξ) with hE
  set S := 2 + Real.exp ξ ^ 2 + Real.exp (-ξ) ^ 2 with hS
  set N := num (cT ξ t) x with hN
  set D := den (cT ξ t) x with hD
  set N' := -(Real.sin t) * x - Real.exp ξ * Real.cos t with hN'
  set D' := Real.exp (-ξ) * Real.cos t * x - Real.sin t with hD'
  set A := N ^ 2 + D ^ 2 with hA
  have hApos : 0 < A := num_sq_add_den_sq_pos _ _
  have hE1 : 1 ≤ E := by have := Real.exp_pos ξ; have := Real.exp_pos (-ξ); linarith
  have he1 : |Real.exp ξ| ≤ E := by rw [abs_of_pos (Real.exp_pos ξ)]; linarith [Real.exp_pos (-ξ)]
  have he2 : |Real.exp (-ξ)| ≤ E := by rw [abs_of_pos (Real.exp_pos _)]; linarith [Real.exp_pos ξ]
  have h1E : |(1 : ℝ)| ≤ E := by rw [abs_one]; exact hE1
  have hs := Real.abs_sin_le_one t
  have hc := Real.abs_cos_le_one t
  have hsn : |-(Real.sin t)| ≤ 1 := by rw [abs_neg]; exact hs
  have hcn : |-(Real.cos t)| ≤ 1 := by rw [abs_neg]; exact hc
  have bN : |N| ≤ E * (1 + |x|) := by
    have := abs_lin_le hE1 h1E he1 hc hsn (x := x)
    rw [hN, num_cT]; convert this using 2; ring
  have bD : |D| ≤ E * (1 + |x|) := by
    have := abs_lin_le hE1 he2 h1E hs hc (x := x)
    rw [hD, den_cT]; convert this using 2; ring
  have bN' : |N'| ≤ E * (1 + |x|) := by
    have := abs_lin_le hE1 h1E he1 hsn hcn (x := x)
    rw [hN']; convert this using 2; ring
  have bD' : |D'| ≤ E * (1 + |x|) := by
    have := abs_lin_le hE1 he2 h1E hc hsn (x := x)
    rw [hD']; convert this using 2; ring
  -- `1 + x² ≤ S A`
  have hSA : 1 + x ^ 2 ≤ S * A := by
    have h := one_add_sq_le_num_den (cT ξ t) x
    have h2 := cT_sq_le ξ t
    calc 1 + x ^ 2 ≤ _ := h
      _ ≤ S * A := mul_le_mul_of_nonneg_right h2 hApos.le
  have hx1 : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith [sq_abs x, abs_nonneg x, sq_nonneg (1 - |x|)]
  have hP : (|N| + |D|) * (|N'| + |D'|) ≤ 8 * E ^ 2 * (S * A) := by
    have hp1 : |N| + |D| ≤ 2 * E * (1 + |x|) := by linarith
    have hp2 : |N'| + |D'| ≤ 2 * E * (1 + |x|) := by linarith
    have h0 : 0 ≤ 2 * E * (1 + |x|) := by positivity
    calc (|N| + |D|) * (|N'| + |D'|) ≤ (2 * E * (1 + |x|)) * (2 * E * (1 + |x|)) :=
          mul_le_mul hp1 hp2 (by positivity) h0
      _ = 4 * E ^ 2 * (1 + |x|) ^ 2 := by ring
      _ ≤ 4 * E ^ 2 * (2 * (1 + x ^ 2)) := by gcongr
      _ ≤ 8 * E ^ 2 * (S * A) := by nlinarith [sq_nonneg E]
  have hq1 : |N * N' + D * D'| ≤ (|N| + |D|) * (|N'| + |D'|) := by
    calc |N * N' + D * D'| ≤ |N| * |N'| + |D| * |D'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ _ := by nlinarith [abs_nonneg N, abs_nonneg D, abs_nonneg N', abs_nonneg D']
  have hq2 : |N' * D - N * D'| ≤ (|N| + |D|) * (|N'| + |D'|) := by
    calc |N' * D - N * D'| ≤ |N'| * |D| + |N| * |D'| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ _ := by nlinarith [abs_nonneg N, abs_nonneg D, abs_nonneg N', abs_nonneg D']
  have hAC : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have t1 : ‖wP ν * (((2 * (N * N' + D * D') : ℝ) : ℂ) / ((A : ℝ) : ℂ))‖ ≤ ‖wP ν‖ * (16 * E ^ 2 * S) := by
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hApos]
    gcongr
    rw [div_le_iff₀ hApos, abs_mul, abs_two]
    have := hq1.trans hP
    linarith
  have t2 : ‖(n : ℂ) * (2 * I * ((N' * D - N * D' : ℝ) : ℂ)) / ((A : ℝ) : ℂ)‖ ≤
      |(n : ℝ)| * (16 * E ^ 2 * S) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hApos, Complex.norm_intCast,
      show ‖(2 : ℂ)‖ = 2 by simp]
    rw [div_le_iff₀ hApos]
    have : |(n : ℝ)| * 2 * 1 * |N' * D - N * D'| ≤ |(n : ℝ)| * (16 * E ^ 2 * S) * A := by
      have h := mul_le_mul_of_nonneg_left (hq2.trans hP) (abs_nonneg (n : ℝ))
      have e : |(n : ℝ)| * (16 * E ^ 2 * S) * A = 2 * (|(n : ℝ)| * (8 * E ^ 2 * (S * A))) := by ring
      rw [e]
      linarith
    linarith
  calc ‖rotLogDeriv ν n ξ t x‖ = ‖wP ν * (((2 * (N * N' + D * D') : ℝ) : ℂ) / ((A : ℝ) : ℂ)) +
        (n : ℂ) * (2 * I * ((N' * D - N * D' : ℝ) : ℂ)) / ((A : ℝ) : ℂ)‖ := rfl
    _ ≤ ‖wP ν * (((2 * (N * N' + D * D') : ℝ) : ℂ) / ((A : ℝ) : ℂ))‖ +
        ‖(n : ℂ) * (2 * I * ((N' * D - N * D' : ℝ) : ℂ)) / ((A : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖wP ν‖ * (16 * E ^ 2 * S) + |(n : ℝ)| * (16 * E ^ 2 * S) := add_le_add t1 t2
    _ = _ := by ring

/-- `π(g) e_n` agrees almost everywhere with its smooth form. -/
lemma coeFn_principalSeries_kVecL2 (ν : ℝ) (n : ℤ) (g : SL2R) :
    (principalSeries 0 ν g (kVecL2 ν n) : ℝ → ℂ) =ᵐ[volume]
      fun x => qForm ν n (num g x) (den g x) := by
  have h2 := coeFn_principalSeries 0 ν g (kVecL2 ν n)
  have h3 := ae_eq_comp_mob g (MemLp.coeFn_toLp (memLp_kVecP ν n))
  filter_upwards [h2, h3, ae_den_ne_zero g] with x e2 e3 hx
  simp only [Function.comp_apply] at e3
  rw [e2]
  have := act_kVecP_eq ν n g x hx
  rw [act] at this
  rw [show (kVecL2 ν n : ℝ → ℂ) (mob g x) = kVecP ν n (mob g x) from e3, this, qForm]

/-- `∫ conj(f x) e_k(x) dx = ⟪f, e_k⟫`. -/
lemma integral_conj_mul_kVecP (ν : ℝ) (k : ℤ) (f : L2R) :
    ∫ x, (starRingEnd ℂ) (f x) * kVecP ν k x = inner ℂ f (kVecL2 ν k) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_kVecP ν k)] with x hx
  rw [RCLike.inner_apply', kVecL2, hx]

/-- **The rotation relation of the matrix coefficients**:
`2 (n cosh ξ - m) Φ_{m,n}(ξ) = -sinh ξ ((w - n) Φ_{m,n+1}(ξ) - (w + n) Φ_{m,n-1}(ξ))`. -/
theorem mcoefP_rot_rel (ν ξ : ℝ) (m n : ℤ) :
    2 * ((n : ℂ) * Real.cosh ξ - m) * mcoefP ν m n ξ =
      -(Real.sinh ξ : ℂ) * ((wP ν - n) * mcoefP ν m (n + 1) ξ - (wP ν + n) * mcoefP ν m (n - 1) ξ) := by
  set f : L2R := principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m) with hf
  set Q : ℝ → ℝ → ℂ := fun t x => qForm ν n (num (cT ξ t) x) (den (cT ξ t) x) with hQ
  set F : ℝ → ℝ → ℂ := fun t x => (starRingEnd ℂ) (f x) * Q t x with hF
  set F' : ℝ → ℝ → ℂ := fun t x => (starRingEnd ℂ) (f x) * (Q t x * rotLogDeriv ν n ξ t x) with hF'
  set K : ℝ → ℂ := fun x => -(2 * I * n * Real.cosh ξ) * kVecP ν n x -
      I * Real.sinh ξ * (wP ν - n) * kVecP ν (n + 1) x + I * Real.sinh ξ * (wP ν + n) * kVecP ν (n - 1) x
    with hK
  set S : ℝ := 2 + Real.exp ξ ^ 2 + Real.exp (-ξ) ^ 2 with hS
  set M : ℝ := 16 * (‖wP ν‖ + |(n : ℝ)|) * (1 + Real.exp ξ + Real.exp (-ξ)) ^ 2 * S with hM
  have hQd : ∀ t x, HasDerivAt (fun t => Q t x) (Q t x * rotLogDeriv ν n ξ t x) t := fun t x =>
    hasDerivAt_qForm_comp ν n (hasDerivAt_num_cT ξ x t) (hasDerivAt_den_cT ξ x t)
      (num_sq_add_den_sq_pos _ _)
  -- at `t = 0` the derivative is the `K`-type expression
  have hK0 : ∀ x, Q 0 x * rotLogDeriv ν n ξ 0 x = K x := fun x =>
    (hQd 0 x).unique (hasDerivAt_qForm_cT_zero ν n ξ x)
  have hQae : ∀ t, (principalSeries 0 ν (cT ξ t) (kVecL2 ν n) : ℝ → ℂ) =ᵐ[volume] Q t := fun t =>
    coeFn_principalSeries_kVecL2 ν n (cT ξ t)
  -- the bound
  set r : L2R := memLp_rpow_neg_half.toLp _ with hr
  have hrae : (r : ℝ → ℂ) =ᵐ[volume] fun x => (((1 + x ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) :=
    MemLp.coeFn_toLp _
  set bound : ℝ → ℝ := fun x => S ^ ((1 : ℝ) / 2) * M * ‖(starRingEnd ℂ) (f x) * r x‖ with hbound
  have hbi : Integrable bound := (integrable_conj_mul f r).norm.const_mul _
  have hb : ∀ᵐ x ∂(volume : Measure ℝ), ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖F' t x‖ ≤ bound x := by
    filter_upwards [hrae] with x hx t _
    have hq := norm_qForm_le ν n (cT ξ t) x
    have hsq : ((cT ξ t) 0 0 ^ 2 + (cT ξ t) 0 1 ^ 2 + (cT ξ t) 1 0 ^ 2 + (cT ξ t) 1 1 ^ 2) ^ ((1 : ℝ) / 2) ≤
        S ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (cT_sq_le ξ t) (by norm_num)
    have hR := norm_rotLogDeriv_le ν n ξ t x
    have hrx : ‖r x‖ = (1 + x ^ 2) ^ (-(1 : ℝ) / 2) := by
      rw [hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [hF', hbound, norm_mul, Complex.norm_conj, hrx]
    have h1 : ‖Q t x‖ ≤ S ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2) :=
      hq.trans (mul_le_mul_of_nonneg_right hsq (by positivity))
    calc ‖f x‖ * (‖Q t x‖ * ‖rotLogDeriv ν n ξ t x‖)
        ≤ ‖f x‖ * ((S ^ ((1 : ℝ) / 2) * (1 + x ^ 2) ^ (-(1 : ℝ) / 2)) * M) := by
          gcongr
      _ = S ^ ((1 : ℝ) / 2) * M * (‖f x‖ * (1 + x ^ 2) ^ (-(1 : ℝ) / 2)) := by ring
  have hFm : ∀ t, AEStronglyMeasurable (F t) volume := fun t =>
    ((Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
      (Lp.aestronglyMeasurable (principalSeries 0 ν (cT ξ t) (kVecL2 ν n)))).congr
      (by filter_upwards [hQae t] with x hx; simp only [hF, Pi.mul_apply, hx])
  have hFi : Integrable (F 0) :=
    (integrable_conj_mul f (principalSeries 0 ν (cT ξ 0) (kVecL2 ν n))).congr
      (by filter_upwards [hQae 0] with x hx; simp only [hF, hx])
  have hF'0 : F' 0 = fun x => (starRingEnd ℂ) (f x) * K x := by
    funext x; simp only [hF', hK0]
  have hKc : Continuous K := by
    simp only [hK]
    exact (((continuous_const.mul (continuous_kVecP ν n)).sub
      (continuous_const.mul (continuous_kVecP ν (n + 1)))).add
      (continuous_const.mul (continuous_kVecP ν (n - 1))))
  have hF'm : AEStronglyMeasurable (F' 0) volume := by
    rw [hF'0]
    exact (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).mul
      hKc.aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := 0)
    (bound := bound) (Metric.ball_mem_nhds 0 one_pos) (Filter.Eventually.of_forall hFm) hFi hF'm
    hb hbi (Filter.Eventually.of_forall fun x t _ => (hQd t x).const_mul _)
  -- the same function is `t ↦ e^{-2imt} Φ`
  have hfun : (fun t : ℝ => ∫ x, F t x) = fun t : ℝ => Complex.exp (-(2 * m * t * I)) * mcoefP ν m n ξ := by
    funext t
    rw [← inner_cT_eq ν ξ t m n, inner_principalSeries_kVecL2]
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * m * t * I)) * mcoefP ν m n ξ)
      (-(2 * m * I) * mcoefP ν m n ξ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => -(2 * (m : ℂ) * t * I)) (-(2 * m * I)) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul (-(2 * (m : ℂ) * I)))
      convert this using 1
      · funext t; simp; ring
      · simp
    have := h1.cexp.mul_const (mcoefP ν m n ξ)
    convert this using 1
    simp
  rw [hfun] at h
  have huniq := h.2.unique hexp
  rw [hF'0] at huniq
  -- evaluate the integral of `conj f · K`
  have hint : ∀ k : ℤ, Integrable (fun x => (starRingEnd ℂ) (f x) * kVecP ν k x) := fun k =>
    (integrable_conj_mul f (kVecL2 ν k)).congr
      (by filter_upwards [MemLp.coeFn_toLp (memLp_kVecP ν k)] with x hx
          simp only [kVecL2] at hx ⊢; rw [hx])
  have hev : ∀ k : ℤ, ∫ x, (starRingEnd ℂ) (f x) * kVecP ν k x = mcoefP ν m k ξ := fun k => by
    rw [integral_conj_mul_kVecP, hf, inner_aR_neg_kVecL2]
  have hsplit : ∫ x, (starRingEnd ℂ) (f x) * K x =
      -(2 * I * n * Real.cosh ξ) * mcoefP ν m n ξ - I * Real.sinh ξ * (wP ν - n) * mcoefP ν m (n + 1) ξ +
        I * Real.sinh ξ * (wP ν + n) * mcoefP ν m (n - 1) ξ := by
    have e : (fun x => (starRingEnd ℂ) (f x) * K x) = fun x =>
        (-(2 * I * n * Real.cosh ξ) * ((starRingEnd ℂ) (f x) * kVecP ν n x) -
          I * Real.sinh ξ * (wP ν - n) * ((starRingEnd ℂ) (f x) * kVecP ν (n + 1) x)) +
        I * Real.sinh ξ * (wP ν + n) * ((starRingEnd ℂ) (f x) * kVecP ν (n - 1) x) := by
      funext x; simp only [hK]; ring
    rw [e, integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul,
      hev, hev, hev]
    all_goals first
      | exact ((hint n).const_mul _).sub ((hint (n + 1)).const_mul _)
      | exact (hint _).const_mul _
  rw [hsplit] at huniq
  linear_combination I * huniq - (-2 * (n : ℂ) * Real.cosh ξ * mcoefP ν m n ξ -
    Real.sinh ξ * (wP ν - n) * mcoefP ν m (n + 1) ξ + Real.sinh ξ * (wP ν + n) * mcoefP ν m (n - 1) ξ +
    2 * m * mcoefP ν m n ξ) * Complex.I_sq

lemma sinh_mul_ladCoeff (l r : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    (Real.sinh ξ : ℂ) * (ladCoeff l r ξ : ℂ) = l * Real.cosh ξ + r := by
  have hs : Real.sinh ξ ≠ 0 := fun h => hξ (Real.sinh_eq_zero.1 h)
  have h : Real.sinh ξ * ladCoeff l r ξ = l * Real.cosh ξ + r := by
    rw [ladCoeff]; field_simp
  rw [← Complex.ofReal_mul, h, Complex.ofReal_add, Complex.ofReal_mul]

/-- **The raising operator on the matrix coefficients**:
`ladUp_{n, -m} Φ^ν_{m,n} = (w - n) Φ^ν_{m,n+1}` for `ξ ≠ 0`. -/
theorem ladUp_mcoefP (ν : ℝ) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ladUp n (-m) (mcoefP ν m n) ξ = (wP ν - n) * mcoefP ν m (n + 1) ξ := by
  have hs : (Real.sinh ξ : ℂ) ≠ 0 := by exact_mod_cast fun h => hξ (Real.sinh_eq_zero.1 h)
  have e := sinh_mul_ladCoeff n (-m) hξ
  have R := mcoefP_rot_rel ν ξ m n
  apply mul_left_cancel₀ hs
  rw [ladUp, (hasDerivAt_mcoefP ν m n ξ).deriv]
  simp only [Complex.ofReal_intCast, Complex.ofReal_neg] at e
  linear_combination (-1 / 2 : ℂ) * R - mcoefP ν m n ξ * e

/-- **The lowering operator on the matrix coefficients**:
`ladDown_{n, -m} Φ^ν_{m,n} = -(w + n) Φ^ν_{m,n-1}` for `ξ ≠ 0`. -/
theorem ladDown_mcoefP (ν : ℝ) (m n : ℤ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ladDown n (-m) (mcoefP ν m n) ξ = -(wP ν + n) * mcoefP ν m (n - 1) ξ := by
  have hs : (Real.sinh ξ : ℂ) ≠ 0 := by exact_mod_cast fun h => hξ (Real.sinh_eq_zero.1 h)
  have e := sinh_mul_ladCoeff n (-m) hξ
  have R := mcoefP_rot_rel ν ξ m n
  apply mul_left_cancel₀ hs
  rw [ladDown, (hasDerivAt_mcoefP ν m n ξ).deriv]
  simp only [Complex.ofReal_intCast, Complex.ofReal_neg] at e
  linear_combination (-1 / 2 : ℂ) * R - mcoefP ν m n ξ * e

end Lightlike.Lorentz.SL2RPlancherel
