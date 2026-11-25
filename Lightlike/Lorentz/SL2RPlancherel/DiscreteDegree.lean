module

public import Lightlike.Lorentz.SL2RBergman
public import Lightlike.Lorentz.SL2RPlancherel.BergmanReproducing
public import Lightlike.Lorentz.SL2RPlancherel.RadialHaar

/-!
# The formal degree of the holomorphic discrete series

For the lowest weight vector `e₀ = (z + i)⁻ⁿ` of `D_n⁺` (`n ≥ 2`) the matrix coefficient `⟨e₀, D_n(g) e₀⟩` is
`(4π/(n-1)) (-2i)⁻ⁿ ((c-b) + i(a+d))⁻ⁿ` (the reproducing property of `e₀`), so `|⟨e₀, D_n(g) e₀⟩|²` is a function of
`cosh d(g)` and its integral over `SL(2,ℝ)` is computed by the radial formula for the Haar measure.
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real UpperHalfPlane Lightlike.Lorentz.SL2R
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz

/-- An integral against `μ_n` on `ℍ` as an integral over the upper half-plane in `ℂ` with density `yⁿ⁻²`. -/
lemma integral_μn_eq_halfplane {n : ℕ} (hn : 2 ≤ n) (F : ℍ → ℂ) :
    ∫ z, F z ∂μn n = ∫ z in {z : ℂ | 0 < z.im},
      (((z.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex z) := by
  have hmp : MeasurableEmbedding UpperHalfPlane.coe := UpperHalfPlane.measurableEmbedding_coe
  have hrange : Set.range UpperHalfPlane.coe = {w : ℂ | 0 < w.im} := by
    ext w; constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hw; exact ⟨⟨w, hw⟩, rfl⟩
  have h1 : ∫ z, F z ∂μn n = ∫ z, (wt n z).toReal • F z ∂(volume : Measure ℍ) := by
    unfold μn
    exact integral_withDensity_eq_integral_toReal_smul (measurable_wt n)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top) F
  have h2 : ∫ z, (wt n z).toReal • F z ∂(volume : Measure ℍ) =
      ∫ z : ℍ, (((z.im ^ (n - 2) : ℝ)) : ℂ) * F z ∂(volume.comap UpperHalfPlane.coe) := by
    rw [SL2R.volume_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      SL2R.measurable_im_density (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [wt, ENNReal.toReal_ofReal (pow_nonneg z.im_pos.le _), Complex.real_smul,
      ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg z.im))]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have : z.im ≠ 0 := z.im_pos.ne'
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast this
    push_cast
    field_simp
    ring
  rw [h1, h2]
  have key := hmp.integral_map (μ := volume.comap UpperHalfPlane.coe)
    (fun w : ℂ => (((w.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex w))
  rw [hmp.map_comap, hrange] at key
  refine Eq.trans ?_ key.symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hz : UpperHalfPlane.ofComplex (z : ℂ) = z := UpperHalfPlane.ofComplex_apply z
  simp only [hz]
  rfl

/-- Integrability against `μ_n` on `ℍ` is integrability over the upper half-plane with density `yⁿ⁻²`. -/
lemma integrable_μn_iff_halfplane {n : ℕ} (hn : 2 ≤ n) (F : ℍ → ℂ) (hF : Measurable F) :
    Integrable F (μn n) ↔ IntegrableOn
      (fun z : ℂ => (((z.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
  have hmp : MeasurableEmbedding UpperHalfPlane.coe := UpperHalfPlane.measurableEmbedding_coe
  have hrange : Set.range UpperHalfPlane.coe = {w : ℂ | 0 < w.im} := by
    ext w; constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hw; exact ⟨⟨w, hw⟩, rfl⟩
  have hfin : ∀ᵐ z : ℍ ∂(volume : Measure ℍ), wt n z < ⊤ :=
    Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top
  have h1 : Integrable F (μn n) ↔ Integrable (fun z => (wt n z).toReal • F z) (volume : Measure ℍ) := by
    unfold μn
    exact integrable_withDensity_iff_integrable_smul' (measurable_wt n) hfin
  have h2 : Integrable (fun z => (wt n z).toReal • F z) (volume : Measure ℍ) ↔
      Integrable (fun z : ℍ => (((z.im ^ (n - 2) : ℝ)) : ℂ) * F z) (volume.comap UpperHalfPlane.coe) := by
    rw [SL2R.volume_eq_withDensity, integrable_withDensity_iff_integrable_smul'
      SL2R.measurable_im_density (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    refine integrable_congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [wt, ENNReal.toReal_ofReal (pow_nonneg z.im_pos.le _), Complex.real_smul,
      ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg z.im))]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have : z.im ≠ 0 := z.im_pos.ne'
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast this
    push_cast
    field_simp
    ring
  rw [h1, h2]
  have key := hmp.integrable_map_iff (μ := volume.comap UpperHalfPlane.coe)
    (g := fun w : ℂ => (((w.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex w))
  rw [hmp.map_comap, hrange] at key
  rw [IntegrableOn, key]
  refine integrable_congr (Filter.Eventually.of_forall fun z => ?_)
  have hz : UpperHalfPlane.ofComplex (z : ℂ) = z := UpperHalfPlane.ofComplex_apply z
  simp only [Function.comp_apply, hz]
  rfl

/-- The holomorphic function `Φ_g(w) = (((a + ib) w + (c + id))ⁿ)⁻¹ = (jac g w)⁻ⁿ · e₀(gᵀ w)`. -/
def coeffFun (n : ℕ) (g : SL2R) (w : ℂ) : ℂ :=
  (((g 0 0 + g 0 1 * Complex.I) * w + (g 1 0 + g 1 1 * Complex.I)) ^ n)⁻¹

/-- The factorisation `(a + ib) z + (c + id) = (b z + d) ((a z + c)/(b z + d) + i)`. -/
lemma coeff_factor (g : SL2R) (z : ℍ) :
    ((g 0 0 + g 0 1 * Complex.I) * (z : ℂ) + (g 1 0 + g 1 1 * Complex.I)) =
      jac g z * (((tsmul g z : ℍ) : ℂ) + Complex.I) := by
  have hj := jac_ne_zero g z
  rw [coe_tsmul]
  simp only [jac] at hj ⊢
  field_simp
  ring

/-- The matrix coefficient integrand: `conj(e₀(z)) · jac⁻ⁿ e₀(gᵀ z) = Φ_g(z) · conj((z+i)⁻ⁿ)`. -/
lemma pairing_lowest (n : ℕ) (g : SL2R) (z : ℍ) :
    (starRingEnd ℂ) (lowestVec n z) * (jac g z ^ (-(n : ℤ)) * lowestVec n (tsmul g z)) =
      coeffFun n g z * (starRingEnd ℂ) ((((z : ℂ) + Complex.I) ^ n)⁻¹) := by
  have hj := jac_ne_zero g z
  have hz : ((tsmul g z : ℍ) : ℂ) + Complex.I ≠ 0 := coe_add_I_ne_zero (tsmul g z)
  simp only [lowestVec, coeffFun, coeff_factor, zpow_neg, zpow_natCast, mul_pow, mul_inv]
  ring

/-- The matrix coefficient `⟨e₀, D_n(g) e₀⟩` as an integral over `ℍ`. -/
lemma inner_lowest_eq {n : ℕ} (hn : 2 ≤ n) (g : SL2R) :
    ⟪lowestClass hn, discreteAction n g (lowestClass hn)⟫_ℂ =
      ∫ z : ℍ, (starRingEnd ℂ) (lowestVec n z) * (jac g z ^ (-(n : ℤ)) * lowestVec n (tsmul g z)) ∂μn n := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 : lowestClass hn =ᵐ[μn n] lowestVec n := MemLp.coeFn_toLp _
  have h2 := coeFn_discreteIso n g (lowestClass hn)
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp h1
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  simp only [Function.comp_apply] at hz3
  rw [discreteAction_apply, hz1, hz2, hz3]
  simp [RCLike.inner_apply, mul_comm]

/-- The matrix coefficient integrand is integrable against `μ_n`. -/
lemma integrable_pairing {n : ℕ} (hn : 2 ≤ n) (g : SL2R) :
    Integrable (fun z : ℍ => (starRingEnd ℂ) (lowestVec n z) *
      (jac g z ^ (-(n : ℤ)) * lowestVec n (tsmul g z))) (μn n) := by
  have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (lowestClass hn) (discreteAction n g (lowestClass hn))
  refine hi.congr ?_
  have h1 : lowestClass hn =ᵐ[μn n] lowestVec n := MemLp.coeFn_toLp _
  have h2 := coeFn_discreteIso n g (lowestClass hn)
  have h3 := (quasiMeasurePreserving_tsmul n g).ae_eq_comp h1
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  simp only [Function.comp_apply] at hz3
  rw [discreteAction_apply, hz1, hz2, hz3]
  simp [RCLike.inner_apply, mul_comm]

/-- `Φ_g` is holomorphic on the upper half-plane. -/
lemma differentiableOn_coeffFun (n : ℕ) (g : SL2R) :
    DifferentiableOn ℂ (coeffFun n g) {z : ℂ | 0 < z.im} := by
  intro w hw
  have hw' : (0 : ℝ) < w.im := hw
  set z : ℍ := ⟨w, hw'⟩
  have hne : ((g 0 0 + g 0 1 * Complex.I) * w + (g 1 0 + g 1 1 * Complex.I)) ≠ 0 := by
    have := coeff_factor g z
    have hz : (z : ℂ) = w := rfl
    rw [hz] at this
    rw [this]
    exact mul_ne_zero (jac_ne_zero g z) (coe_add_I_ne_zero (tsmul g z))
  have : DifferentiableAt ℂ (coeffFun n g) w := by
    unfold coeffFun
    refine DifferentiableAt.inv ?_ (pow_ne_zero _ hne)
    fun_prop
  exact this.differentiableWithinAt

/-- **The matrix coefficient of the lowest weight vector of `D_n⁺`**:
`⟨e₀, D_n(g) e₀⟩ = (4π/(n-1)) (-2i)⁻ⁿ (((c-b) + i(a+d))ⁿ)⁻¹`. -/
theorem coeff_lowest {n : ℕ} (hn : 2 ≤ n) (g : SL2R) :
    ⟪lowestClass hn, discreteAction n g (lowestClass hn)⟫_ℂ =
      ((4 * π / (n - 1) : ℝ) : ℂ) * ((-2 * Complex.I) ^ n)⁻¹ * coeffFun n g Complex.I := by
  rw [inner_lowest_eq hn g]
  set F : ℍ → ℂ := fun z => (starRingEnd ℂ) (lowestVec n z) *
    (jac g z ^ (-(n : ℤ)) * lowestVec n (tsmul g z)) with hF
  have hFc : Measurable F := by
    have hc : Continuous F := by
      simp only [hF]
      refine (Complex.continuous_conj.comp (continuous_lowestVec n)).mul
        ((continuous_jac_zpow g _).mul ((continuous_lowestVec n).comp (continuous_tsmul g)))
    exact hc.measurable
  rw [integral_μn_eq_halfplane hn F]
  have hcongr : ∀ w ∈ {z : ℂ | 0 < z.im},
      (((w.im ^ (n - 2) : ℝ)) : ℂ) * F (UpperHalfPlane.ofComplex w) =
        coeffFun n g w * (starRingEnd ℂ) (((w + Complex.I) ^ n)⁻¹) * (((w.im ^ (n - 2) : ℝ)) : ℂ) := by
    intro w hw
    have hw' : (0 : ℝ) < w.im := hw
    have hz : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    have := pairing_lowest n g (UpperHalfPlane.ofComplex w)
    simp only [hF]
    rw [this, hz]; ring
  have hint : IntegrableOn (fun w : ℂ => coeffFun n g w * (starRingEnd ℂ) (((w + Complex.I) ^ n)⁻¹) *
      (((w.im ^ (n - 2) : ℝ)) : ℂ)) {z : ℂ | 0 < z.im} := by
    have := (integrable_μn_iff_halfplane hn F hFc).1 (integrable_pairing hn g)
    exact this.congr_fun (fun w hw => hcongr w hw) (measurableSet_lt measurable_const Complex.measurable_im)
  rw [setIntegral_congr_fun (measurableSet_lt measurable_const Complex.measurable_im) hcongr]
  exact SL2RPlancherel.bergman_reproducing hn (differentiableOn_coeffFun n g) hint

/-- `∫_1^∞ (1+t)^{-(m+1)} dt = 2^{-m}/m` for `m ≥ 1`. -/
lemma integral_Ioi_one_add_pow {m : ℕ} (hm : 1 ≤ m) :
    IntegrableOn (fun t : ℝ => ((1 + t) ^ (m + 1))⁻¹) (Ioi (1 : ℝ)) ∧
      ∫ t in Ioi (1 : ℝ), ((1 + t) ^ (m + 1))⁻¹ = (2 ^ m)⁻¹ / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  set g : ℝ → ℝ := fun t => -(1 / (m : ℝ)) * (1 + t) ^ (-(m : ℤ)) with hg
  have hd : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt g (((1 + x) ^ (m + 1))⁻¹) x := by
    intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have : (1 : ℝ) < x := hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have h2 := ((hasDerivAt_zpow (-(m : ℤ)) (1 + x) (Or.inl hx1)).comp x h1).const_mul (-(1 / (m : ℝ)))
    refine HasDerivAt.congr_deriv (f := g) h2 ?_
    rw [mul_one, zpow_sub₀ hx1, zpow_neg, zpow_natCast, zpow_one, pow_succ]
    simp only [Int.cast_neg, Int.cast_natCast]
    field_simp
  have hpos : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ ((1 + x) ^ (m + 1))⁻¹ := fun x hx => by
    have : (0 : ℝ) < 1 + x := by have : (1 : ℝ) < x := hx; linarith
    positivity
  have hlim : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (1 + t) ^ (-(m : ℤ))) Filter.atTop (nhds 0) := by
      have := tendsto_zpow_atTop_zero (𝕜 := ℝ) (n := -(m : ℤ)) (by omega)
      exact this.comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa [hg] using h1.const_mul (-(1 / (m : ℝ)))
  have hcont : ContinuousWithinAt g (Ici (1 : ℝ)) 1 := by
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hg]
    refine continuousAt_const.mul ((continuousAt_const.add continuousAt_id).zpow₀ _ (Or.inl (by norm_num)))
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hcont hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hd hpos hlim]
  simp only [hg]
  rw [zero_sub, zpow_neg, zpow_natCast]
  norm_num
  field_simp

/-- `(a+d)² + (b-c)² = 2 (1 + cosh d(g))` on `SL(2,ℝ)`. -/
lemma sq_sum_eq (g : SL2R) :
    (g 1 0 - g 0 1) ^ 2 + (g 0 0 + g 1 1) ^ 2 = 2 * (1 + coshDistR g) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  unfold coshDistR
  nlinarith [hdet]

/-- **`|⟨e₀, D_n(g) e₀⟩|²` is a function of `cosh d(g)`**:
`(4π/(n-1))² 4⁻ⁿ (2(1 + cosh d(g)))⁻ⁿ`. -/
theorem norm_sq_coeff_lowest {n : ℕ} (hn : 2 ≤ n) (g : SL2R) :
    ‖⟪lowestClass hn, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2 =
      ((4 * π / (n - 1)) ^ 2 * ((4 : ℝ) ^ n)⁻¹) * ((2 * (1 + coshDistR g)) ^ n)⁻¹ := by
  rw [coeff_lowest hn g]
  have hz : (g 0 0 + g 0 1 * Complex.I) * Complex.I + (g 1 0 + g 1 1 * Complex.I) =
      ((g 1 0 - g 0 1 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring_nf; simp [Complex.I_sq]; ring
  have hc : coeffFun n g Complex.I = ((((g 1 0 - g 0 1 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * Complex.I) ^ n)⁻¹ := by
    unfold coeffFun; rw [hz]
  have hnorm : ‖(((g 1 0 - g 0 1 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      2 * (1 + coshDistR g) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, ← sq_sum_eq g]
  rw [hc, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, norm_pow, Complex.norm_real]
  have h2 : ‖(-2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2]
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  have hpos : 0 ≤ 2 * (1 + coshDistR g) := by rw [← hnorm]; positivity
  have hn2 : ‖(((g 1 0 - g 0 1 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * Complex.I)‖ =
      Real.sqrt (2 * (1 + coshDistR g)) := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [hn2]
  have hsq : Real.sqrt (2 * (1 + coshDistR g)) ^ 2 = 2 * (1 + coshDistR g) := Real.sq_sqrt hpos
  have hsq' : (Real.sqrt (2 * (1 + coshDistR g)) ^ n) ^ 2 = (2 * (1 + coshDistR g)) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, hsq]
  calc (4 * π / (↑n - 1) * ((2 : ℝ) ^ n)⁻¹ * (Real.sqrt (2 * (1 + coshDistR g)) ^ n)⁻¹) ^ 2
      = (4 * π / (↑n - 1)) ^ 2 * (((2 : ℝ) ^ n) ^ 2)⁻¹ * ((Real.sqrt (2 * (1 + coshDistR g)) ^ n) ^ 2)⁻¹ := by
        rw [mul_pow, mul_pow, inv_pow, inv_pow]
    _ = _ := by
        rw [hsq', ← pow_mul, mul_comm n 2, pow_mul]
        norm_num

/-- **The formal degree integral of the lowest weight vector of `D_n⁺`**:
`∫_{SL(2,ℝ)} |⟨e₀, D_n(g) e₀⟩|² dg = 4π² (4π/(n-1))² 4⁻ⁿ 2⁻ⁿ 2^{-(n-1)}/(n-1)`. -/
theorem lintegral_norm_sq_coeff_lowest {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ g, ENNReal.ofReal (‖⟪lowestClass hn, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2) ∂haarR =
      ENNReal.ofReal (4 * π ^ 2 * ((4 * π / (n - 1)) ^ 2 * ((4 : ℝ) ^ n)⁻¹) * (((2 : ℝ) ^ n)⁻¹ *
        (((2 : ℝ) ^ (n - 1))⁻¹ / ((n - 1 : ℕ) : ℝ)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  set K : ℝ := (4 * π / ((m + 1 : ℕ) - 1)) ^ 2 * ((4 : ℝ) ^ (m + 1))⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  set Φ : ℝ → ENNReal := fun t => ENNReal.ofReal (K * ((2 * (1 + t)) ^ (m + 1))⁻¹) with hΦ
  have hΦm : Measurable Φ := by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have h1 : ∀ g : SL2R, ENNReal.ofReal (‖⟪lowestClass hn, discreteAction (m + 1) g (lowestClass hn)⟫_ℂ‖ ^ 2) =
      Φ (coshDistR g) := fun g => by
    rw [norm_sq_coeff_lowest hn g]
  simp only [h1]
  rw [SL2R.lintegral_coshDistR hΦm]
  obtain ⟨hint, hval⟩ := integral_Ioi_one_add_pow hm
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => K * (2 ^ (m + 1))⁻¹ * ((1 + t) ^ (m + 1))⁻¹ :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
      have : (0 : ℝ) < 1 + t := by have : (1 : ℝ) < t := ht; linarith
      positivity)
  have hlin : ∫⁻ t in Ioi (1 : ℝ), Φ t =
      ENNReal.ofReal (K * (2 ^ (m + 1))⁻¹ * ((2 ^ m)⁻¹ / m)) := by
    have e1 : ∀ t ∈ Ioi (1 : ℝ), Φ t = ENNReal.ofReal (K * (2 ^ (m + 1))⁻¹ * ((1 + t) ^ (m + 1))⁻¹) := by
      intro t ht
      simp only [hΦ]
      congr 1
      rw [mul_pow, mul_inv]; ring
    rw [setLIntegral_congr_fun measurableSet_Ioi e1,
      ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) hnn, integral_const_mul, hval]
  rw [hlin]
  have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [Nat.add_sub_cancel]
  ring

/-- **The norm of the lowest weight vector**: `‖(z + i)⁻ⁿ‖² = 4π/((n-1) 4ⁿ)` in `L²(ℍ, μ_n)`. -/
theorem norm_sq_lowestClass {n : ℕ} (hn : 2 ≤ n) :
    ‖lowestClass hn‖ ^ 2 = 4 * π / (((n : ℝ) - 1) * (4 : ℝ) ^ n) := by
  have h := norm_sq_coeff_lowest hn 1
  have hdisc : discreteAction n 1 (lowestClass hn) = lowestClass hn := by
    rw [discreteAction_apply]; exact discreteIso_one n _
  have hc : coshDistR (1 : SL2R) = 1 := by
    simp [coshDistR]
  rw [hdisc, inner_self_eq_norm_sq_to_K, hc, show (2 * (1 + 1 : ℝ)) = 4 by norm_num] at h
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at h
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hpos : 0 < ‖lowestClass hn‖ ^ 2 := by
    have := norm_pos_iff.2 (lowestClass_ne_zero hn); positivity
  have hrhs : (4 * π / (((n : ℝ) - 1) * (4 : ℝ) ^ n)) ^ 2 =
      (4 * π / ((n : ℝ) - 1)) ^ 2 * ((4 : ℝ) ^ n)⁻¹ * ((4 : ℝ) ^ n)⁻¹ := by
    field_simp
  have hsq : (‖lowestClass hn‖ ^ 2) ^ 2 = (4 * π / (((n : ℝ) - 1) * (4 : ℝ) ^ n)) ^ 2 := by
    rw [hrhs, ← h]
  exact (sq_eq_sq₀ hpos.le (by positivity)).1 hsq

/-- **The formal degree of the holomorphic discrete series `D_n⁺`** (Schur orthogonality on the lowest weight vector):
`∫_{SL(2,ℝ)} |⟨e₀, D_n(g) e₀⟩|² dg = (8π²/(n-1)) ‖e₀‖⁴`, with `dg` the Haar measure normalised by
`∫ Φ(cosh d(g)) dg = 4π² ∫_{t>1} Φ(t) dt`. -/
theorem formal_degree_lowest {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ g, ENNReal.ofReal (‖⟪lowestClass hn, discreteAction n g (lowestClass hn)⟫_ℂ‖ ^ 2) ∂haarR =
      ENNReal.ofReal (8 * π ^ 2 / ((n : ℝ) - 1) * (‖lowestClass hn‖ ^ 2) ^ 2) := by
  rw [lintegral_norm_sq_coeff_lowest hn, norm_sq_lowestClass hn]
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : (m : ℝ) ≠ 0 := by
    have : 1 ≤ m := by omega
    positivity
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, h4, ← pow_mul]
  field_simp
  ring

end Lightlike.Lorentz
