import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PhiBound

/-!
# `Φ g` as an element of `L²(0, ∞)`

For a Schwartz function `g` the weighted Fourier transform `Φ g` (`phi`) is continuous and square
integrable on `ℝ` (`integrable_norm_sq_phi`), so it defines a class `phiL2 g ∈ L²(0, ∞)`.
The map `g ↦ phiL2 g` is additive and satisfies `‖phiL2 g‖² ≤ ‖g‖² + ‖g'‖²`
(`norm_phiL2_sq_le`), which is the continuity statement used for the surjectivity of the spherical
Plancherel isometry `sphericalL2` for `SL(2,ℝ)` (milestone HA3).
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- Norm of an `L²` class in terms of the integral (same statement as `norm_toLp_two` in
`SphericalL2.lean`, repeated to avoid the import). -/
theorem norm_toLp_two' {μ : Measure ℝ} {f : ℝ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = (∫ a, ‖f a‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem continuous_phiW : Continuous phiW := by
  unfold phiW
  refine Continuous.div_const ?_ _
  refine Real.continuous_sqrt.comp ?_
  have ht : Continuous fun ρ : ℝ => Real.tanh (Real.pi * ρ) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) fun x => (Real.cosh_pos _).ne'
  exact continuous_id.mul ht

theorem continuous_phi (g : SchwartzMap ℝ ℂ) : Continuous (phi g) := by
  unfold phi
  refine (Complex.continuous_ofReal.comp continuous_phiW).mul ?_
  exact (SchwartzMap.fourierTransformCLM ℂ g).continuous.comp (continuous_id.div_const _)

/-- `‖Φ g‖²` is integrable on `ℝ`. -/
theorem integrable_norm_sq_phi (g : SchwartzMap ℝ ℂ) :
    Integrable (fun ρ => ‖phi g ρ‖ ^ 2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set dg : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ g with hdg
  set G : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ g with hG
  set G' : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ dg with hG'
  have hdgf : (dg : ℝ → ℂ) = deriv g := funext fun x => SchwartzMap.derivCLM_apply ℂ g x
  have hGG' : ∀ ξ : ℝ, G' ξ = ((2 * Real.pi * Complex.I * ξ : ℂ)) • G ξ := by
    intro ξ
    have h := congrFun (Real.fourier_deriv (E := ℂ) g.integrable g.differentiable
      (by rw [← hdgf]; exact dg.integrable)) ξ
    rw [← hdgf] at h
    exact h
  have hnorm : ∀ ξ : ℝ, ‖G' ξ‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 * ‖G ξ‖ ^ 2 := by
    intro ξ
    rw [hGG', norm_smul, mul_pow]
    congr 1
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_real, abs_of_pos hπ]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have hint : ∀ S : SchwartzMap ℝ ℂ, Integrable (fun x => ‖S x‖ ^ 2) := fun S =>
    (memLp_two_iff_integrable_sq_norm S.continuous.aestronglyMeasurable).1 (S.memLp 2)
  have hI1 : Integrable (fun ρ : ℝ => ‖G (ρ / (2 * Real.pi))‖ ^ 2) :=
    (hint G).comp_div (by positivity)
  have hI2 : Integrable (fun ρ : ℝ => ‖G' (ρ / (2 * Real.pi))‖ ^ 2) :=
    (hint G').comp_div (by positivity)
  have hMi : Integrable (fun ρ : ℝ => (‖G (ρ / (2 * Real.pi))‖ ^ 2 +
      ‖G' (ρ / (2 * Real.pi))‖ ^ 2 / (4 * Real.pi ^ 2)) / (4 * Real.pi)) :=
    ((hI1.add (hI2.div_const _)).div_const _)
  refine hMi.mono' ((continuous_phi g).norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ρ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  unfold phi
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply phiW_sq_mul_le ρ _ _ (by positivity)
  rw [hnorm]
  congr 1
  field_simp

/-- `Φ g` is in `L²(0, ∞)`. -/
theorem memLp_phi_Ioi (g : SchwartzMap ℝ ℂ) :
    MemLp (phi g) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_two_iff_integrable_sq_norm (continuous_phi g).aestronglyMeasurable).2
    (integrable_norm_sq_phi g).integrableOn

/-- `Φ g` as an element of `L²(0, ∞)`. -/
def phiL2 (g : SchwartzMap ℝ ℂ) : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_phi_Ioi g).toLp (phi g)

theorem phi_sub (g h : SchwartzMap ℝ ℂ) : phi (g - h) = phi g - phi h := by
  funext ρ
  simp only [phi, Pi.sub_apply, map_sub, sub_apply, mul_sub]

theorem phiL2_sub (g h : SchwartzMap ℝ ℂ) : phiL2 (g - h) = phiL2 g - phiL2 h := by
  unfold phiL2
  rw [← MemLp.toLp_sub (memLp_phi_Ioi g) (memLp_phi_Ioi h)]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun ρ => by simp [phi_sub])

/-- `‖phiL2 g‖² = ∫_{(0,∞)} ‖Φ g‖²`. -/
theorem norm_phiL2_sq (g : SchwartzMap ℝ ℂ) :
    ‖phiL2 g‖ ^ 2 = ∫ ρ in Ioi (0 : ℝ), ‖phi g ρ‖ ^ 2 := by
  unfold phiL2
  rw [norm_toLp_two', ← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

/-- **Continuity of `Φ` in `H¹`**: `‖phiL2 g‖² ≤ ‖g‖² + ‖g'‖²`. -/
theorem norm_phiL2_sq_le (g : SchwartzMap ℝ ℂ) :
    ‖phiL2 g‖ ^ 2 ≤ (∫ x, ‖g x‖ ^ 2) + ∫ x, ‖deriv g x‖ ^ 2 := by
  rw [norm_phiL2_sq]; exact integral_norm_sq_phi_le g

end Lightlike.Lorentz.SL2RPlancherel
