import Lightlike.Asymptotics.Lorentzian.CoherentVertex
import Lightlike.Lorentz.KernelBound

/-!
# The edge integral of the Lorentzian vertex density is the kernel `I`

For `A, B ∈ SL(2,ℂ)` the integral over the chart `w ∈ ℂ` of the density
`(‖A† (w,1)‖² ‖B† (w,1)‖²)⁻¹` of `Ω_e` equals `kernelI ((conj A)⁻¹ * conj B)`, the kernel
`I(g) = π r / sinh r` of `Lightlike/Lorentz/KernelBound.lean` (`r` the hyperbolic distance of `g`
from `1`). The proof moves the chart by the Möbius map of `(conj A)⁻¹`
(`Lightlike.Lorentz.lintegral_mob`), which turns `A†` into the identity. This is the first step of
the joint integrability of the vertex integrand (task T-SF10-P1): the integral over `ℂ^10` of the
modulus bound `∏_e Ω_e` is the product of ten kernels `kernelI`, which is integrable over the four
free vertices (`Lightlike.Lorentz.integrable_linkProd_kernelI`).
-/

open MeasureTheory Matrix
open scoped ENNReal
open Lightlike Lightlike.Lorentz Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- The squared norm of `A† (w, 1)` is `normT (conj A) w`, the quantity `‖gᵀ (w, 1)‖²` of the
Möbius calculus for `g = conj A`. -/
theorem norm_spinAct_adj_lorSpinor_sq (A : SL2C) (w : ℂ) :
    ‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 = normT (conjSL A) w := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, normT, num, den, conjSL_coe, spinAct, lorSpinor, Matrix.conjTranspose_apply,
    Matrix.map_apply, add_comm]

theorem continuous_normT' (g : SL2C) : Continuous (normT g) := by
  unfold normT num den; fun_prop

/-- `normT` of a product: `normT (h g) u = ‖den h u‖² · normT g (mob h u)`. -/
theorem normT_mul_mob (h g : SL2C) {u : ℂ} (hu : den h u ≠ 0) :
    normT (h * g) u = ‖den h u‖ ^ 2 * normT g (mob h u) := by
  have hn := num_mul h g hu
  have hd := den_mul h g hu
  unfold normT
  rw [hn, hd, norm_mul, norm_mul]
  ring

/-- `normT 1 u = 1 + ‖u‖²`. -/
theorem normT_one (u : ℂ) : normT 1 u = 1 + ‖u‖ ^ 2 := by
  simp [normT, add_comm]

/-- **The edge integral is the kernel `I`**:
`∫ (‖A† (w,1)‖² ‖B† (w,1)‖²)⁻¹ dw = I ((conj A)⁻¹ conj B)`. -/
theorem integral_lorEdgeDensity_eq_kernelI (A B : SL2C) :
    ∫ w : ℂ, (‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
      ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ =
      kernelI ((conjSL A)⁻¹ * conjSL B) := by
  set h : SL2C := (conjSL A)⁻¹ with hh
  set F : ℂ → ℝ := fun w => (normT (conjSL A) w * normT (conjSL B) w)⁻¹ with hF
  have hF0 : ∀ w, 0 ≤ F w := fun w => by
    have := normT_pos (conjSL A) w
    have := normT_pos (conjSL B) w
    simp only [hF]; positivity
  have e1 : ∀ w : ℂ, (‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
      ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ = F w := fun w => by
    rw [norm_spinAct_adj_lorSpinor_sq, norm_spinAct_adj_lorSpinor_sq]
  simp_rw [e1]
  have hk : kernelI (h * conjSL B) = ∫ u : ℂ, ((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹ := rfl
  have hint : ∫ w, F w = (∫⁻ w, ENNReal.ofReal (F w)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
      (by
        have : Continuous F := by
          refine Continuous.inv₀ ((continuous_normT' _).mul (continuous_normT' _)) fun w => ?_
          exact (mul_pos (normT_pos _ w) (normT_pos _ w)).ne'
        exact this.aestronglyMeasurable)
  have hk0 : ∀ u, 0 ≤ ((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹ := fun u => by
    have := normT_pos (h * conjSL B) u
    positivity
  have hk' : ∫ u : ℂ, ((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹ =
      (∫⁻ u, ENNReal.ofReal (((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hk0)
      (by
        have : Continuous fun u : ℂ => ((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹ := by
          refine Continuous.inv₀ ?_ fun u => ?_
          · exact (by fun_prop : Continuous fun u : ℂ => 1 + ‖u‖ ^ 2).mul (continuous_normT' _)
          · exact (mul_pos (by positivity) (normT_pos _ u)).ne'
        exact this.aestronglyMeasurable)
  rw [hk, hint, hk']
  congr 1
  rw [lintegral_mob h (fun w => ENNReal.ofReal (F w))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_den_ne_zero h] with u hu
  have hd : 0 < ‖den h u‖ := norm_pos_iff.mpr hu
  have hA : normT (conjSL A) (mob h u) = (1 + ‖u‖ ^ 2) / ‖den h u‖ ^ 2 := by
    have := normT_mul_mob h (conjSL A) hu
    rw [hh, inv_mul_cancel, normT_one] at this
    field_simp
    linarith
  have hB : normT (conjSL B) (mob h u) = normT (h * conjSL B) u / ‖den h u‖ ^ 2 := by
    rw [normT_mul_mob h (conjSL B) hu]
    field_simp
  have hval : (‖den h u‖ ^ 4)⁻¹ * F (mob h u) = ((1 + ‖u‖ ^ 2) * normT (h * conjSL B) u)⁻¹ := by
    simp only [hF]
    rw [hA, hB]
    have : 0 < normT (h * conjSL B) u := normT_pos _ u
    have : 0 < 1 + ‖u‖ ^ 2 := by positivity
    field_simp
  rw [← hval, ENNReal.ofReal_mul (by positivity)]

end Lightlike.Asymptotics.Lorentzian
