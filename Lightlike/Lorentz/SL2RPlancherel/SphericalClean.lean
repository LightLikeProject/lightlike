import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SphericalIdentity

/-!
# The spherical Plancherel identity for the hyperbolic plane, in the variable `ρ`

For `F` smooth with compact support on `[1, ∞)` (a radial function `F ∘ cosh d(i, ·)` on the upper
half-plane) with spherical transform `f̂(ρ) = sphTransformH F ρ`,
`∫_{v>1} |F v|² dv = (1/(4π²)) ∫_{ρ>0} ρ tanh(πρ) |f̂(ρ)|² dρ`.
The density `ρ tanh(πρ)` is the Plancherel density of the spherical principal series of `SL(2,ℝ)`
(milestone HA3).
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The Fourier transform (`𝓕 g ξ = ∫ e^{-2πiξt} g t dt`) of the Abel transform is the spherical
transform at `ρ = 2πξ`; the Abel transform is even. -/
theorem fourier_abelTransform (F : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (abelTransform F) ξ = sphTransformH F (2 * Real.pi * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, sphTransformH_eq_integral_abel]
  rw [← integral_neg_eq_self (fun t : ℝ => Complex.exp (((2 * Real.pi * ξ : ℝ) : ℂ) * (t : ℂ) *
    Complex.I) * abelTransform F t) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, abelTransform_neg]
  congr 2
  push_cast
  ring

/-- **Spherical Plancherel formula for the hyperbolic plane** (test-function form, in `ρ`):
for `F` smooth with compact support,
`π² ∫_{v>1} |F v|² dv = ¼ ∫_{ρ>0} ρ tanh(πρ) |f̂(ρ)|² dρ`, `f̂ = sphTransformH F`. -/
theorem norm_sq_eq_sph (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Real.pi ^ 2 * ∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 =
      (1 / 4 : ℝ) * ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 := by
  have h := norm_sq_eq_fourier F hF hc
  simp only [fourier_abelTransform] at h
  set G : ℝ → ℂ := fun ρ => (((ρ * Real.pi * Real.tanh (Real.pi * ρ) : ℝ) : ℂ) *
    (2 * (starRingEnd ℂ (sphTransformH F ρ) * sphTransformH F ρ))) with hG
  have hcv := integral_comp_mul_left_Ioi G 0 (b := 2 * Real.pi) (by positivity)
  have hGρ : ∀ ρ : ℝ, G ρ = (((2 * Real.pi * (ρ * Real.tanh (Real.pi * ρ) *
      ‖sphTransformH F ρ‖ ^ 2) : ℝ)) : ℂ) := by
    intro ρ
    simp only [hG]
    have : starRingEnd ℂ (sphTransformH F ρ) * sphTransformH F ρ =
        ((‖sphTransformH F ρ‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this]
    push_cast
    ring
  have hJ : ∫ ρ in Ioi (0 : ℝ), G ρ = ((2 * Real.pi *
      ∫ ρ in Ioi (0 : ℝ), ρ * Real.tanh (Real.pi * ρ) * ‖sphTransformH F ρ‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hGρ]
    rw [integral_complex_ofReal, integral_const_mul]
  have hI : ((∫ v in Ioi (1 : ℝ), ‖F v‖ ^ 2 : ℝ) : ℂ) =
      ∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h' : ∫ ξ in Ioi (0 : ℝ), G (2 * Real.pi * ξ) = (2 * Real.pi)⁻¹ • ∫ ρ in Ioi (0 : ℝ), G ρ := by
    rw [hcv]; simp
  apply Complex.ofReal_injective
  push_cast
  rw [hI, h]
  have h'' : (∫ ξ in Ioi (0 : ℝ), G (2 * Real.pi * ξ)) = ∫ ξ in Ioi (0 : ℝ),
      (((2 * Real.pi * ξ) * Real.pi * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (2 * (starRingEnd ℂ (sphTransformH F (2 * Real.pi * ξ)) *
          sphTransformH F (2 * Real.pi * ξ))) := rfl
  rw [← h'', h', hJ]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.real_smul]
  push_cast
  field_simp
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  simp only
  rw [mul_comm ρ Real.pi]

end Lightlike.Lorentz.SL2RPlancherel
