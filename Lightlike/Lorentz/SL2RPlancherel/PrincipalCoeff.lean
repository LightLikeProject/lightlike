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

end Lightlike.Lorentz.SL2RPlancherel
