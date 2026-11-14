module

public import Lightlike.Lorentz.SphericalPlancherel

/-!
# Trust checks for the radial Plancherel formula of SL(2,ℂ) (milestone HA2)

1. **Non-vacuity.** For the smooth bump `testF` (equal to `1` near `t = 2`), the radial function
   `testF ∘ coshDist` has positive `L²` norm, so both sides of `spherical_plancherel` are positive
   (`testF_plancherel_pos`). In general a profile that is nonzero somewhere on `(1, ∞)` gives a
   nonzero function (`integral_norm_sq_coshDist_pos`).
2. **Known constant.** The constant `(2π⁴)⁻¹` is the classical `(2π²)⁻¹` of hyperbolic space and of
   radial functions on `ℝ³` (Helgason), rescaled by the volume `π²` of the fibre `SU(2)` in the
   normalisation `dg = 4π³ sinh² r dr`; see the docstring of `spherical_plancherel`.
3. **Wrong inputs give different answers.** With the constant `(2π²)⁻¹` used directly on the group
   the formula fails for `testF` (`testF_wrong_constant`). With the density `ρ² + 1` in place of
   `ρ²` it fails for every nonzero radial function (`spherical_plancherel_wrong_density`), in
   particular for `testF` (`testF_wrong_density`).

The numerical cross-check `scripts/lorentz/plancherel_check.py` evaluates both sides for a
concrete profile by quadrature, with the flat spherical function and the density `ρ² + 1` as
controls.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ContDiff FourierTransform

namespace Lightlike.Lorentz

/-- **Positivity**: a radial function whose profile is nonzero at some `t₀ > 1` has positive `L²`
norm. -/
theorem integral_norm_sq_coshDist_pos {F : ℝ → ℂ} (hF : Continuous F) (hc : HasCompactSupport F)
    {t₀ : ℝ} (ht : 1 < t₀) (hF0 : F t₀ ≠ 0) : 0 < ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC := by
  rw [integral_norm_sq_coshDist hF]
  have hcont : Continuous fun r => ‖sinhProfile F r‖ ^ 2 := by
    unfold sinhProfile; fun_prop
  have hcs : HasCompactSupport fun r => ‖sinhProfile F r‖ ^ 2 :=
    (hasCompactSupport_sinhProfile hc).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  have ha : 0 < Real.arcosh t₀ := Real.arcosh_pos ht
  have hpos : 0 < ∫ r in Ioi 0, ‖sinhProfile F r‖ ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun r => by positivity)
      (hcont.integrable_of_hasCompactSupport hcs).integrableOn]
    refine ((isOpen_compl_singleton.preimage hcont).inter isOpen_Ioi).measure_pos _
      ⟨Real.arcosh t₀, ?_, ha⟩
    show ‖sinhProfile F (Real.arcosh t₀)‖ ^ 2 ≠ 0
    simp only [sinhProfile, Real.cosh_arcosh ht.le, ne_eq, pow_eq_zero_iff two_ne_zero,
      norm_eq_zero, mul_eq_zero, Complex.ofReal_eq_zero, not_or]
    exact ⟨(Real.sinh_pos_iff.mpr ha).ne', hF0⟩
  have hπ := Real.pi_pos
  positivity

/-- The bump used in the checks: a smooth function equal to `1` on `[3/2, 5/2]` and supported in
`[1, 3]`. -/
noncomputable def testBump : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The test profile `F = testBump`, as a complex function. -/
noncomputable def testF (t : ℝ) : ℂ := (testBump t : ℂ)

/-- The test profile is smooth. -/
lemma contDiff_testF : ContDiff ℝ ∞ testF :=
  Complex.ofRealCLM.contDiff.comp testBump.contDiff

/-- The test profile is compactly supported. -/
lemma hasCompactSupport_testF : HasCompactSupport testF :=
  testBump.hasCompactSupport.comp_left Complex.ofReal_zero

/-- The test profile is `1` at `t = 2`. -/
lemma testF_two : testF 2 = 1 := by
  simp [testF, testBump.one_of_mem_closedBall (Metric.mem_closedBall_self testBump.rIn_pos.le)]

/-- **Non-vacuity**: for the test profile both sides of the Plancherel formula are positive. -/
theorem testF_plancherel_pos :
    0 < ∫ g, ‖testF (coshDist g)‖ ^ 2 ∂haarC ∧
      0 < ∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform testF ρ‖ ^ 2 := by
  have h1 := integral_norm_sq_coshDist_pos contDiff_testF.continuous hasCompactSupport_testF
    one_lt_two (by rw [testF_two]; exact one_ne_zero)
  refine ⟨h1, ?_⟩
  rw [spherical_plancherel contDiff_testF hasCompactSupport_testF] at h1
  exact pos_of_mul_pos_right h1 (by positivity)

/-- **Wrong constant**: the hyperbolic-space constant `(2π²)⁻¹`, used directly with the Haar
measure of the group, does not give the `L²` norm of the test function. -/
theorem testF_wrong_constant :
    ∫ g, ‖testF (coshDist g)‖ ^ 2 ∂haarC ≠
      (2 * Real.pi ^ 2)⁻¹ * ∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform testF ρ‖ ^ 2 := by
  have hI := testF_plancherel_pos.2
  rw [spherical_plancherel contDiff_testF hasCompactSupport_testF]
  have hπ : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hlt : (2 * Real.pi ^ 4)⁻¹ < (2 * Real.pi ^ 2)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by positivity)]
    nlinarith [pow_lt_pow_right₀ hπ (show 2 < 4 by norm_num)]
  exact (mul_lt_mul_of_pos_right hlt hI).ne

/-- **Wrong density**: with the density `ρ² + 1` in place of `ρ²` the Plancherel formula fails
for every radial function of positive norm. -/
theorem spherical_plancherel_wrong_density {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hpos : 0 < ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC) :
    ∫ g, ‖F (coshDist g)‖ ^ 2 ∂haarC ≠
      (2 * Real.pi ^ 4)⁻¹ * ∫ ρ in Ioi 0, (ρ ^ 2 + 1) * ‖sphTransform F ρ‖ ^ 2 := by
  have hP := spherical_plancherel hF hc
  have hπ := Real.pi_pos
  by_cases hint : IntegrableOn (fun ρ => (ρ ^ 2 + 1) * ‖sphTransform F ρ‖ ^ 2) (Ioi 0)
  · have hq : ∀ ρ ∈ Ioi (0 : ℝ), ‖sphTransform F ρ‖ ^ 2 =
        4 * Real.pi ^ 6 * ‖𝓕 (sinhSchwartz hF hc) ((2 * Real.pi)⁻¹ * ρ)‖ ^ 2 / ρ ^ 2 :=
      fun ρ hρ => by
        have hρ' : (0 : ℝ) < ρ := hρ
        rw [← sq_mul_norm_sq_sphTransform hF hc hρ']
        field_simp
    have hcF : Continuous fun ρ : ℝ =>
        4 * Real.pi ^ 6 * ‖𝓕 (sinhSchwartz hF hc) ((2 * Real.pi)⁻¹ * ρ)‖ ^ 2 :=
      continuous_const.mul (((𝓕 (sinhSchwartz hF hc)).continuous.comp
        (continuous_const.mul continuous_id)).norm.pow 2)
    have hqm : AEStronglyMeasurable (fun ρ => ‖sphTransform F ρ‖ ^ 2) (volume.restrict (Ioi 0)) :=
      ((hcF.continuousOn.div (continuous_pow 2).continuousOn
        fun ρ hρ => pow_ne_zero 2 (ne_of_gt hρ)).aestronglyMeasurable measurableSet_Ioi).congr
        ((ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => (hq ρ hρ).symm)
    have hq_int : IntegrableOn (fun ρ => ‖sphTransform F ρ‖ ^ 2) (Ioi 0) :=
      Integrable.mono' hint hqm (Filter.Eventually.of_forall fun ρ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ρ, sq_nonneg ‖sphTransform F ρ‖,
          mul_nonneg (sq_nonneg ρ) (sq_nonneg ‖sphTransform F ρ‖)])
    have hq2_int : IntegrableOn (fun ρ => ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2) (Ioi 0) :=
      Integrable.mono' hint ((continuous_pow 2).aestronglyMeasurable.mul hqm)
        (Filter.Eventually.of_forall fun ρ => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          nlinarith [sq_nonneg ‖sphTransform F ρ‖])
    have hsplit : ∫ ρ in Ioi 0, (ρ ^ 2 + 1) * ‖sphTransform F ρ‖ ^ 2 =
        (∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2) + ∫ ρ in Ioi 0, ‖sphTransform F ρ‖ ^ 2 := by
      rw [← integral_add hq2_int hq_int]
      congr 1
      funext ρ
      ring
    have hq_pos : 0 < ∫ ρ in Ioi 0, ‖sphTransform F ρ‖ ^ 2 := by
      refine lt_of_le_of_ne (setIntegral_nonneg measurableSet_Ioi fun _ _ => by positivity)
        fun h0 => ?_
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => by positivity) hq_int).mp h0.symm
      have h2 : ∫ ρ in Ioi 0, ρ ^ 2 * ‖sphTransform F ρ‖ ^ 2 = ∫ ρ in Ioi (0 : ℝ), (0 : ℝ) :=
        integral_congr_ae (hz.mono fun ρ hρ => by
          simp only [Pi.zero_apply] at hρ
          simp only [hρ, mul_zero])
      rw [integral_zero] at h2
      rw [hP, h2, mul_zero] at hpos
      exact lt_irrefl _ hpos
    intro h
    rw [hP, hsplit] at h
    have : (2 * Real.pi ^ 4)⁻¹ * ∫ ρ in Ioi 0, ‖sphTransform F ρ‖ ^ 2 = 0 := by linarith
    exact (mul_pos (by positivity) hq_pos).ne' this
  · rw [integral_undef hint, mul_zero]
    exact hpos.ne'

/-- The wrong density `ρ² + 1` fails for the test function. -/
theorem testF_wrong_density :
    ∫ g, ‖testF (coshDist g)‖ ^ 2 ∂haarC ≠
      (2 * Real.pi ^ 4)⁻¹ * ∫ ρ in Ioi 0, (ρ ^ 2 + 1) * ‖sphTransform testF ρ‖ ^ 2 :=
  spherical_plancherel_wrong_density contDiff_testF hasCompactSupport_testF
    testF_plancherel_pos.1

end Lightlike.Lorentz
