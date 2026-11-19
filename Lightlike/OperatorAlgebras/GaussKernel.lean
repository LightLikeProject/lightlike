import Lightlike.OperatorAlgebras.FockExists
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian kernel identity behind von Neumann's projection

`∫ e^{-‖z‖²/4} e^{-‖u - f - z‖²/4} e^{i(σ(f, z) - σ(z, u))/2} dz = (2π)^d e^{-‖u‖²/4} e^{-‖f‖²/4} e^{iσ(f, u)/2}`
(`d = dim_ℂ h`), the twisted convolution `Φ ♮ Φ^{ξ,η} = e^{-π(ξ² + η²)/2} Φ` of Faulhuber, arXiv:2204.01596, Lemma 7.34(b),
in the normalization `W f W g = e^{-iσ(f,g)/2} W (f + g)`.
-/

open MeasureTheory GaussianFourier
open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

attribute [local instance] InnerProductSpace.complexToReal

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- `σ(f, g) = Im⟪f, g⟫` is the real inner product `⟪i f, g⟫_ℝ`. -/
lemma symp_eq_real_inner (f g : h) : symp h f g = ⟪Complex.I • f, g⟫_ℝ := by
  rw [symp, real_inner_eq_re_inner, inner_smul_left]
  simp [Complex.conj_I, Complex.mul_re]

lemma symp_sub_left (f f' g : h) : symp h (f - f') g = symp h f g - symp h f' g := by
  simp [symp, inner_sub_left]

lemma symp_sub_right (f g g' : h) : symp h f (g - g') = symp h f g - symp h f g' := by
  simp [symp, inner_sub_right]

lemma symp_self (f : h) : symp h f f = 0 := by
  simp [symp, ← Complex.ofReal_pow]

lemma symp_smul_real_left (t : ℝ) (f g : h) : symp h ((t : ℂ) • f) g = t * symp h f g := by
  rw [symp, inner_smul_left]
  simp [Complex.mul_im, symp]

lemma symp_half (f u : h) : symp h (f + u) ((1 / 2 : ℝ) • (u - f)) = symp h f u := by
  rw [show ((1 / 2 : ℝ) • (u - f) : h) = ((1 / 2 : ℝ) : ℂ) • (u - f) from (Complex.coe_smul _ _).symm,
    symp, inner_smul_right, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [← symp, symp_sub_right, symp_add_left, symp_add_left, symp_self, symp_self, symp_antisymm f u]
  ring

lemma norm_sq_add_half (v c : h) :
    ‖v + (1 / 2 : ℝ) • c‖ ^ 2 + ‖c - (v + (1 / 2 : ℝ) • c)‖ ^ 2 = 2 * ‖v‖ ^ 2 + ‖c‖ ^ 2 / 2 := by
  have hc : c - (v + (1 / 2 : ℝ) • c) = (1 / 2 : ℝ) • c - v := by module
  rw [hc]
  have := parallelogram_law_with_norm ℝ ((1 / 2 : ℝ) • c) v
  rw [add_comm ((1 / 2 : ℝ) • c) v] at this
  rw [this, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

variable [FiniteDimensional ℂ h] [MeasurableSpace h] [BorelSpace h]

/-- The constant `∫ e^{-‖v‖²/2} dv = (2π)^{dim_ℂ h}`. -/
noncomputable def vnConst (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h] : ℂ :=
  (Real.pi / (1 / 2 : ℂ)) ^ (Module.finrank ℝ h / 2 : ℂ)

/-- **The Gaussian kernel identity** (Faulhuber, Lemma 7.34(b), in the normalization of `CCRRep`). -/
theorem integral_gauss_kernel (f u : h) :
    ∫ z : h, Complex.exp (-(1 / 4 : ℂ) * ‖z‖ ^ 2) * Complex.exp (-(1 / 4 : ℂ) * ‖u - f - z‖ ^ 2) *
        Complex.exp (Complex.I * ((symp h f z - symp h z u) / 2 : ℝ)) =
      vnConst h * Complex.exp (-(1 / 4 : ℂ) * ‖u‖ ^ 2) * Complex.exp (-(1 / 4 : ℂ) * ‖f‖ ^ 2) *
        Complex.exp (Complex.I * (symp h f u / 2 : ℝ)) := by
  set c : h := u - f with hc
  rw [← integral_add_right_eq_self _ ((1 / 2 : ℝ) • c)]
  beta_reduce
  have hpt : ∀ v : h, Complex.exp (-(1 / 4 : ℂ) * ‖v + (1 / 2 : ℝ) • c‖ ^ 2) *
      Complex.exp (-(1 / 4 : ℂ) * ‖c - (v + (1 / 2 : ℝ) • c)‖ ^ 2) *
      Complex.exp (Complex.I * ((symp h f (v + (1 / 2 : ℝ) • c) - symp h (v + (1 / 2 : ℝ) • c) u) / 2 : ℝ)) =
      (Complex.exp (-(‖c‖ ^ 2 / 8 : ℝ)) * Complex.exp (Complex.I * (symp h f u / 2 : ℝ))) *
        Complex.exp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + (Complex.I / 2) * ⟪Complex.I • (f + u), v⟫_ℝ) := by
    intro v
    have hn := norm_sq_add_half v c
    have hs : symp h f (v + (1 / 2 : ℝ) • c) - symp h (v + (1 / 2 : ℝ) • c) u =
        symp h (f + u) v + symp h f u := by
      rw [symp_antisymm (v + (1 / 2 : ℝ) • c) u, sub_neg_eq_add, ← symp_add_left, symp_add_right, hc, symp_half]
    rw [hs, ← symp_eq_real_inner, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hn' : (‖v + (1 / 2 : ℝ) • c‖ : ℂ) ^ 2 + (‖c - (v + (1 / 2 : ℝ) • c)‖ : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + (‖c‖ : ℂ) ^ 2 / 2 := by exact_mod_cast hn
    push_cast
    linear_combination (-(1 / 4 : ℂ)) * hn'
  simp_rw [hpt]
  rw [integral_const_mul, integral_cexp_neg_mul_sq_norm_add (by norm_num) (Complex.I / 2) (Complex.I • (f + u)),
    vnConst]
  have hpar := parallelogram_law_with_norm ℝ u f
  have hpar' : (‖u + f‖ : ℂ) ^ 2 + (‖u - f‖ : ℂ) ^ 2 = 2 * ((‖u‖ : ℂ) ^ 2 + (‖f‖ : ℂ) ^ 2) := by
    exact_mod_cast hpar
  rw [norm_smul, Complex.norm_I, one_mul, add_comm f u]
  have e1 : Complex.exp (-(‖c‖ ^ 2 / 8 : ℝ)) * Complex.exp ((Complex.I / 2) ^ 2 * (‖u + f‖ : ℂ) ^ 2 / (4 * (1 / 2))) =
      Complex.exp (-(1 / 4 : ℂ) * ‖u‖ ^ 2) * Complex.exp (-(1 / 4 : ℂ) * ‖f‖ ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hc]
    push_cast
    linear_combination (norm := ring_nf) (-(1 / 8 : ℂ)) * hpar'
    simp [Complex.I_sq]
  calc _ = (Real.pi / (1 / 2 : ℂ)) ^ (Module.finrank ℝ h / 2 : ℂ) *
        (Complex.exp (-(‖c‖ ^ 2 / 8 : ℝ)) * Complex.exp ((Complex.I / 2) ^ 2 * (‖u + f‖ : ℂ) ^ 2 / (4 * (1 / 2)))) *
        Complex.exp (Complex.I * (symp h f u / 2 : ℝ)) := by ring
    _ = _ := by rw [e1]; ring

end Lightlike.OperatorAlgebras
