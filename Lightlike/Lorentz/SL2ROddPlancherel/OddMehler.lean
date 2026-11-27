import Mathlib
import Lightlike.Lorentz.SL2ROddPlancherel.BaseCoefficient

/-!
# Mehler's formula and the radial transform of the odd base coefficient

For `ξ > 0` the odd base coefficient has the Mehler-type representation

  `2 cosh(ξ/2) Φ^{odd}_ν(ξ) = ∫_{-ξ}^{ξ} e^{iνt/2} · 2 cosh(t/2) / √(2(cosh ξ - cosh t)) dt`   (`oddCoeff_mehler`),

obtained from the even Mehler formula of `PrincipalSpherical.lean` by the same substitution `t = log u_ξ(x)`,
because `(1 + u) u^{iρ-1} = 2 cosh(t/2) u^{(iν-1)/2}` for `u = e^t`. Integrating against a radial test function
`F(cosh ξ) sinh ξ`, with `G(v) = F(v)/√(2(1 + v))` (`oddG`, so `F(cosh ξ) = 2 cosh(ξ/2) G(cosh ξ)`), the order of
integration is swapped (`integral_sinh_oddKernel_swap`) and the Abel substitution gives

  `∫_{ξ>0} sinh ξ F(cosh ξ) Φ^{odd}_ν(ξ) dξ = (1/2) ∫ e^{iρt} · 2 cosh(t/2) · 𝒜G(t) dt`,  `ρ = ν/2`,

the Fourier transform of the **odd Abel transform** `2 cosh(t/2) 𝒜G(t)` (`integral_sinh_mul_oddCoeff`,
`oddAbel`, `oddTransform`). Compare the even case `integral_sinh_mul_mcoefP_zero_zero`, where the right side is
`(1/2) ∫ e^{iρt} 𝒜F(t) dt`.
-/

open MeasureTheory Set Complex Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

open Lightlike.Lorentz.SL2R Lightlike.Lorentz.SL2RPlancherel

/-- **The odd Mehler kernel** `e^{iνt/2} · 2 cosh(t/2)/√(2(cosh ξ - cosh t))`. -/
def oddKernel (ν ξ t : ℝ) : ℂ := mehlerKernel ν ξ t * ((2 * Real.cosh (t / 2) : ℝ) : ℂ)

/-- `(1 + e^ℓ) e^{(iν - 2)ℓ/2} = 2 cosh(ℓ/2) e^{(iν - 1)ℓ/2}`. -/
lemma one_add_exp_mul_exp (ν ℓ : ℝ) :
    (1 + ((Real.exp ℓ : ℝ) : ℂ)) * Complex.exp (weightExp 1 ν * (ℓ : ℂ)) =
      Complex.exp (wP ν * (ℓ : ℂ)) * ((2 * Real.cosh (ℓ / 2) : ℝ) : ℂ) := by
  have hA : Complex.exp (wP ν * (ℓ : ℂ)) =
      Complex.exp (weightExp 1 ν * (ℓ : ℂ)) * Complex.exp ((ℓ : ℂ) / 2) := by
    rw [← Complex.exp_add]; congr 1; rw [weightExp_one, wP]; ring
  have hB : ((Real.exp ℓ : ℝ) : ℂ) = Complex.exp ((ℓ : ℂ) / 2) * Complex.exp ((ℓ : ℂ) / 2) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; ring
  have hC : ((2 * Real.cosh (ℓ / 2) : ℝ) : ℂ) =
      Complex.exp ((ℓ : ℂ) / 2) + (Complex.exp ((ℓ : ℂ) / 2))⁻¹ := by
    rw [Real.cosh_eq]; push_cast; rw [← Complex.exp_neg]; ring_nf
  have hne : Complex.exp ((ℓ : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
  rw [hA, hB, hC]
  field_simp
  ring

/-- **The Jacobian identity of the odd substitution**: for `x > 0`,
`2 cosh(ξ/2) · (even part) = (1/2) |t'(x)| · oddKernel(log u_ξ(x))`. -/
lemma two_cosh_mul_oddEven (ν : ℝ) {ξ x : ℝ} (hξ : 0 < ξ) (hx : 0 < x) :
    ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddEven ν ξ x =
      (1 / 2 : ℂ) * (|mehlerDeriv ξ x| • oddKernel ν ξ (Real.log (sphU ξ x))) := by
  have hk := abs_mehlerDeriv_smul (ν := ν) hξ hx
  have hkey : (1 + ((sphU ξ x : ℝ) : ℂ)) * Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℝ)) =
      Complex.exp (wP ν * (Real.log (sphU ξ x) : ℝ)) *
        ((2 * Real.cosh (Real.log (sphU ξ x) / 2) : ℝ) : ℂ) := by
    have := one_add_exp_mul_exp ν (Real.log (sphU ξ x))
    rwa [Real.exp_log (sphU_pos ξ x)] at this
  have hc : ((Real.cosh (ξ / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.cosh (ξ / 2) := Real.cosh_pos _
    exact_mod_cast this.ne'
  have hx1 : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    exact_mod_cast this.ne'
  unfold oddKernel oddEven
  rw [← smul_mul_assoc, hk, sphIntegrand]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_pow, Complex.ofReal_ofNat] at hkey ⊢
  rw [show (2 : ℂ) * (Real.cosh (ξ / 2) : ℂ) *
      ((1 + (sphU ξ x : ℂ)) / (2 * (Real.cosh (ξ / 2) : ℂ) * (1 + (x : ℂ) ^ 2)) *
        Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℂ))) =
      (1 + (sphU ξ x : ℂ)) * Complex.exp (weightExp 1 ν * (Real.log (sphU ξ x) : ℂ)) /
        (1 + (x : ℂ) ^ 2) by field_simp, hkey]
  ring

/-- **Mehler's formula for the odd base coefficient.** -/
theorem oddCoeff_mehler (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddCoeff ν ξ = ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t := by
  rw [oddCoeff_eq_integral, ← integral_const_mul]
  have hint : Integrable (fun x => ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddEven ν ξ x) :=
    (integrable_oddEven ν ξ).const_mul _
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
  have hneg : ∫ x in Iic (0 : ℝ), ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddEven ν ξ x =
      ∫ x in Ioi (0 : ℝ), ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddEven ν ξ x := by
    have := integral_comp_neg_Iic (0 : ℝ) (fun x => ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) * oddEven ν ξ x)
    simp only [oddEven_neg, neg_zero] at this
    exact this
  rw [hneg, ← two_mul, ← image_log_sphU hξ,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun x _ => (hasDerivAt_log_sphU ξ x).hasDerivWithinAt) (strictMonoOn_log_sphU hξ).injOn,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have := two_cosh_mul_oddEven ν hξ hx
  rw [this]
  ring

lemma norm_oddKernel_le (ν ξ t : ℝ) (ht : |t| ≤ ξ) :
    ‖oddKernel ν ξ t‖ ≤ ‖mehlerKernel ν ξ t‖ * (2 * Real.cosh (ξ / 2)) := by
  unfold oddKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have : Real.cosh (t / 2) ≤ Real.cosh (ξ / 2) := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_div, abs_div, abs_two]
    have : |ξ| = ξ := abs_of_nonneg ((abs_nonneg t).trans ht)
    rw [this]; linarith
  linarith

lemma measurable_oddKernel (ν ξ : ℝ) : Measurable (oddKernel ν ξ) := by
  unfold oddKernel mehlerKernel
  fun_prop

lemma integrableOn_oddKernel (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    IntegrableOn (oddKernel ν ξ) (Ioo (-ξ) ξ) := by
  have hm : IntegrableOn (mehlerKernel ν ξ) (Ioo (-ξ) ξ) := integrableOn_mehlerKernel ν hξ
  refine Integrable.mono' (hm.norm.mul_const (2 * Real.cosh (ξ / 2)))
    (measurable_oddKernel ν ξ).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact norm_oddKernel_le ν ξ t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)

lemma integral_norm_oddKernel_le (ν : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    ∫ t in Ioo (-ξ) ξ, ‖oddKernel ν ξ t‖ ≤
      (2 * Real.cosh (ξ / 2)) * (2 * Real.exp (ξ / 2) * Real.pi) := by
  calc ∫ t in Ioo (-ξ) ξ, ‖oddKernel ν ξ t‖
      ≤ ∫ t in Ioo (-ξ) ξ, ‖mehlerKernel ν ξ t‖ * (2 * Real.cosh (ξ / 2)) :=
        setIntegral_mono_on (integrableOn_oddKernel ν hξ).norm
          ((integrableOn_mehlerKernel ν hξ).norm.mul_const _) measurableSet_Ioo
          fun t ht => norm_oddKernel_le ν ξ t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
    _ = (∫ t in Ioo (-ξ) ξ, ‖mehlerKernel ν ξ t‖) * (2 * Real.cosh (ξ / 2)) := integral_mul_const _ _
    _ ≤ (2 * Real.exp (ξ / 2) * Real.pi) * (2 * Real.cosh (ξ / 2)) :=
        mul_le_mul_of_nonneg_right (integral_norm_mehlerKernel_le ν hξ) (by positivity)
    _ = _ := by ring

/-- The integrand on `{|t| < ξ}` of the odd order swap. -/
def oddJoint (ν : ℝ) (G : ℝ → ℂ) (ξ t : ℝ) : ℂ :=
  (Ioo (-ξ) ξ).indicator (fun t => (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * oddKernel ν ξ t) t

lemma oddJoint_eq_indicator_Ioi (ν : ℝ) (G : ℝ → ℂ) (ξ t : ℝ) :
    oddJoint ν G ξ t = (Ioi |t|).indicator
      (fun ξ => (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * oddKernel ν ξ t) ξ := by
  have h : (-ξ < t ∧ t < ξ) ↔ |t| < ξ := abs_lt.symm
  simp only [oddJoint, Set.indicator, Set.mem_Ioo, Set.mem_Ioi, h]

lemma measurable_oddJoint (ν : ℝ) {G : ℝ → ℂ} (hG : Continuous G) :
    Measurable (Function.uncurry (oddJoint ν G)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | -p.1 < p.2 ∧ p.2 < p.1} :=
    (measurableSet_lt measurable_fst.neg measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hm : Measurable fun p : ℝ × ℝ =>
      (Real.sinh p.1 : ℂ) * G (Real.cosh p.1) * oddKernel ν p.1 p.2 := by
    have hGm := hG.measurable
    unfold oddKernel mehlerKernel
    fun_prop
  have e : Function.uncurry (oddJoint ν G) = {p : ℝ × ℝ | -p.1 < p.2 ∧ p.2 < p.1}.indicator
      fun p => (Real.sinh p.1 : ℂ) * G (Real.cosh p.1) * oddKernel ν p.1 p.2 := by
    funext p
    simp only [Function.uncurry, oddJoint, Set.indicator, Set.mem_Ioo, Set.mem_ofPred_eq]
  rw [e]
  exact hm.indicator hs

lemma integrable_oddJoint (ν : ℝ) {G : ℝ → ℂ} (hG : Continuous G) (hc : HasCompactSupport G) :
    Integrable (Function.uncurry (oddJoint ν G)) (volume.prod volume) := by
  have hAc : Continuous fun ξ => (Real.sinh ξ : ℂ) * G (Real.cosh ξ) :=
    (Complex.continuous_ofReal.comp Real.continuous_sinh).mul (hG.comp Real.continuous_cosh)
  have hAcs : HasCompactSupport fun ξ => (Real.sinh ξ : ℂ) * G (Real.cosh ξ) :=
    (hasCompactSupport_comp_cosh hc).mul_left
  have hJm := (measurable_oddJoint ν hG).aestronglyMeasurable (μ := volume.prod volume)
  rw [integrable_prod_iff hJm]
  refine ⟨Filter.Eventually.of_forall fun ξ => ?_, ?_⟩
  · simp only [Function.uncurry_apply_pair, oddJoint]
    by_cases hξ : 0 < ξ
    · exact (show IntegrableOn (fun t => (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * oddKernel ν ξ t)
        (Ioo (-ξ) ξ) volume from (integrableOn_oddKernel ν hξ).const_mul _).integrable_indicator
        measurableSet_Ioo
    · rw [Ioo_eq_empty (by linarith), indicator_empty]
      exact integrable_zero _ _ _
  · have hB : Integrable fun ξ => (2 * Real.cosh (ξ / 2)) * (2 * Real.exp (ξ / 2) * Real.pi) *
        ‖(Real.sinh ξ : ℂ) * G (Real.cosh ξ)‖ :=
      (((continuous_const.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul
        (continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 2)) |>.mul
          continuous_const)).mul hAc.norm).integrable_of_hasCompactSupport hAcs.norm.mul_left
    refine hB.mono' hJm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have e : (fun t => ‖Function.uncurry (oddJoint ν G) (ξ, t)‖) = (Ioo (-ξ) ξ).indicator
        fun t => ‖(Real.sinh ξ : ℂ) * G (Real.cosh ξ)‖ * ‖oddKernel ν ξ t‖ := by
      funext t
      simp only [Function.uncurry_apply_pair, oddJoint, norm_indicator_eq_indicator_norm, norm_mul]
    rw [e, integral_indicator measurableSet_Ioo, integral_const_mul]
    by_cases hξ : 0 < ξ
    · calc ‖(Real.sinh ξ : ℂ) * G (Real.cosh ξ)‖ * ∫ t in Ioo (-ξ) ξ, ‖oddKernel ν ξ t‖
          ≤ ‖(Real.sinh ξ : ℂ) * G (Real.cosh ξ)‖ *
              ((2 * Real.cosh (ξ / 2)) * (2 * Real.exp (ξ / 2) * Real.pi)) :=
            mul_le_mul_of_nonneg_left (integral_norm_oddKernel_le ν hξ) (norm_nonneg _)
        _ = _ := by ring
    · rw [Ioo_eq_empty (by linarith), Measure.restrict_empty, integral_zero_measure, mul_zero]
      positivity

/-- **The odd order swap**: `∫_{ξ>0} sinh ξ G(cosh ξ) ∫_{-ξ}^{ξ} oddKernel dt dξ
= ∫_ℝ e^{iνt/2} 2cosh(t/2) ∫_{w>0} G(cosh t + w²/2) dw dt`. -/
theorem integral_sinh_oddKernel_swap (ν : ℝ) {G : ℝ → ℂ} (hG : Continuous G)
    (hc : HasCompactSupport G) :
    ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t =
      ∫ t : ℝ, Complex.exp (I * ν * t / 2) * ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
        ∫ w in Ioi (0 : ℝ), G (Real.cosh t + w ^ 2 / 2) := by
  have hi : ∀ ξ, ∫ t, oddJoint ν G ξ t =
      (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t := fun ξ => by
    simp only [oddJoint]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul]
  have hii : ∀ t, ∫ ξ, oddJoint ν G ξ t =
      Complex.exp (I * ν * t / 2) * ((2 * Real.cosh (t / 2) : ℝ) : ℂ) *
        ∫ w in Ioi (0 : ℝ), G (Real.cosh t + w ^ 2 / 2) := fun t => by
    simp only [oddJoint_eq_indicator_Ioi]
    rw [integral_indicator measurableSet_Ioi, ← integral_Ioi_abs_sinh_div_sqrt,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [oddKernel, mehlerKernel, Complex.ofReal_div]
    ring
  calc ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * G (Real.cosh ξ) *
        ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t
      = ∫ ξ, (Real.sinh ξ : ℂ) * G (Real.cosh ξ) * ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun ξ hξ => ?_
        have hξ' : ξ ≤ 0 := not_lt.1 hξ
        rw [Ioo_eq_empty (by linarith), Measure.restrict_empty, integral_zero_measure, mul_zero]
    _ = ∫ ξ, ∫ t, oddJoint ν G ξ t := by simp only [hi]
    _ = ∫ t, ∫ ξ, oddJoint ν G ξ t := integral_integral_swap (integrable_oddJoint ν hG hc)
    _ = _ := by simp only [hii]

/-- `√(2(1 + |v|))` is `2 cosh(ξ/2)` at `v = cosh ξ`. -/
lemma sqrt_two_one_add_cosh (ξ : ℝ) :
    Real.sqrt (2 * (1 + |Real.cosh ξ|)) = 2 * Real.cosh (ξ / 2) := by
  have h := Real.cosh_two_mul (ξ / 2)
  rw [show 2 * (ξ / 2) = ξ by ring] at h
  have h2 := Real.cosh_sq (ξ / 2)
  rw [abs_of_pos (Real.cosh_pos ξ), show 2 * (1 + Real.cosh ξ) = (2 * Real.cosh (ξ / 2)) ^ 2 by
    nlinarith]
  exact Real.sqrt_sq (by positivity)

/-- **The odd weight** `G(v) = F(v)/√(2(1 + |v|))`; at `v = cosh ξ`, `F(cosh ξ) = 2 cosh(ξ/2) G(cosh ξ)`. -/
def oddG (F : ℝ → ℂ) (v : ℝ) : ℂ := F v * ((Real.sqrt (2 * (1 + |v|)) : ℝ) : ℂ)⁻¹

lemma continuous_oddG {F : ℝ → ℂ} (hF : Continuous F) : Continuous (oddG F) := by
  unfold oddG
  refine hF.mul (Continuous.inv₀ (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (by fun_prop))) fun v => ?_)
  have : (0 : ℝ) < Real.sqrt (2 * (1 + |v|)) := Real.sqrt_pos.mpr (by positivity)
  exact_mod_cast this.ne'

lemma hasCompactSupport_oddG {F : ℝ → ℂ} (hc : HasCompactSupport F) : HasCompactSupport (oddG F) :=
  hc.mul_right

lemma F_cosh_eq (F : ℝ → ℂ) (ξ : ℝ) :
    F (Real.cosh ξ) = oddG F (Real.cosh ξ) * ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) := by
  unfold oddG
  rw [sqrt_two_one_add_cosh]
  have : ((2 * Real.cosh (ξ / 2) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.cosh (ξ / 2) := by positivity
    exact_mod_cast this.ne'
  field_simp

/-- **The odd Abel transform** `2 cosh(t/2) · 𝒜(F/√(2(1 + |v|)))(t)`. -/
def oddAbel (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((2 * Real.cosh (t / 2) : ℝ) : ℂ) * abelTransform (oddG F) t

/-- **The odd radial transform** `ρ ↦ ∫ e^{iρt} 2 cosh(t/2) 𝒜G(t) dt`: the Fourier transform of the odd
Abel transform. -/
def oddTransform (F : ℝ → ℂ) (ρ : ℝ) : ℂ := ∫ t : ℝ, Complex.exp (ρ * t * I) * oddAbel F t

/-- **The radial transform of the odd base coefficient is the Fourier transform of the odd Abel
transform**: for `F` continuous with compact support,
`∫_{ξ>0} sinh ξ F(cosh ξ) Φ^{odd}_ν(ξ) dξ = (1/2) ∫ e^{iρt} 2 cosh(t/2) 𝒜G(t) dt`, `ρ = ν/2`. -/
theorem integral_sinh_mul_oddCoeff (ν : ℝ) {F : ℝ → ℂ} (hF : Continuous F)
    (hc : HasCompactSupport F) :
    ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * F (Real.cosh ξ) * oddCoeff ν ξ =
      (1 / 2) * oddTransform F (ν / 2) := by
  have hG := continuous_oddG hF
  have hGc := hasCompactSupport_oddG hc
  have h1 : ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * F (Real.cosh ξ) * oddCoeff ν ξ =
      ∫ ξ in Ioi (0 : ℝ), (Real.sinh ξ : ℂ) * oddG F (Real.cosh ξ) *
        ∫ t in Ioo (-ξ) ξ, oddKernel ν ξ t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    rw [← oddCoeff_mehler ν hξ, F_cosh_eq F ξ]
    ring
  rw [h1, integral_sinh_oddKernel_swap ν hG hGc, oddTransform, ← integral_const_mul]
  congr 1
  funext t
  have hab : abelTransform (oddG F) t = 2 * ∫ w in Ioi (0 : ℝ), oddG F (Real.cosh t + w ^ 2 / 2) := by
    have hint : Integrable fun w : ℝ => oddG F (Real.cosh t + w ^ 2 / 2) :=
      (hG.comp (by fun_prop)).integrable_of_hasCompactSupport (hasCompactSupport_comp_abel hGc t)
    rw [abelTransform, ← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn
      hint.integrableOn]
    have := integral_comp_neg_Iic (0 : ℝ) (fun w => oddG F (Real.cosh t + w ^ 2 / 2))
    simp only [neg_sq, neg_zero] at this
    rw [this, two_mul]
  rw [oddAbel, hab]
  have he : Complex.exp (I * ν * t / 2) = Complex.exp (((ν / 2 : ℝ) : ℂ) * t * I) := by
    congr 1; push_cast; ring
  rw [he]
  ring

end Lightlike.Lorentz.SL2ROddPlancherel
