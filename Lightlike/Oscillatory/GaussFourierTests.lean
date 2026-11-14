module

public import Lightlike.Oscillatory.GaussFourier
public import Lightlike.Oscillatory.GaussianTests

/-!
# Trust checks for the Fourier transform of a complex Gaussian

For `integral_gaussLin`, `∫ e^{-⟨B x, x⟩/2 + ⟨c, x⟩} dx = G(B) e^{⟨B⁻¹ c, c⟩/2}`:

* **Known value** (`integral_gaussLin_one`): for `B = 1`,
  `∫ e^{-|x|²/2 + ⟨c, x⟩} dx = (2π)^{n/2} e^{⟨c, c⟩/2}`.
* **Known value, the Fourier transform** (`fourier_gauss_one`): with `c = 2πiξ` this is the
  classical `∫ e^{-|x|²/2} e^{2πi⟨ξ, x⟩} dx = (2π)^{n/2} e^{-2π²|ξ|²}`.
* **Independent cross-check** (`integral_gaussLin_diagonal_mathlib`): for diagonal
  `B = diag(b)` with `Re bᵢ > 0` and every `c ∈ ℂⁿ`, the right-hand side of `integral_gaussLin` is
  shown to equal the integral computed from Mathlib's product formula
  `GaussianFourier.integral_cexp_neg_sum_mul_add`, without the ODE argument.
* **Wrong constant** (`integral_gaussLin_wrong_constant`): if `e^{⟨B⁻¹ c, c⟩/2}` is replaced by
  `e^{a ⟨B⁻¹ c, c⟩}` with real `a`, the formula holds for `B = 1`, `c = 1` on `ℝ¹` only when
  `a = 1/2`.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset
open scoped Real

namespace Lightlike.Oscillatory

/-- Known value: `∫ e^{-|x|²/2 + ⟨c, x⟩} dx = (2π)^{n/2} e^{⟨c, c⟩/2}`. -/
theorem integral_gaussLin_one {n : ℕ} (c : Fin n → ℂ) :
    ∫ x, gaussLin (1 : Matrix (Fin n) (Fin n) ℂ) c x =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * cexp ((c ⬝ᵥ c) / 2) := by
  rw [integral_gaussLin isSymm_one (fun x hx => re_qform_one_pos x hx), inv_one, one_mulVec,
    integral_gauss_one]

/-- Known value, the Fourier transform of the standard Gaussian:
`∫ e^{-|x|²/2} e^{2πi⟨ξ, x⟩} dx = (2π)^{n/2} e^{-2π²|ξ|²}`. -/
theorem fourier_gauss_one {n : ℕ} (ξ : Fin n → ℝ) :
    ∫ x, gaussLin (1 : Matrix (Fin n) (Fin n) ℂ) (fun i => 2 * π * I * ξ i) x =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * cexp (-(2 * π ^ 2 * ∑ i, (ξ i : ℂ) ^ 2)) := by
  rw [integral_gaussLin_one]
  congr 2
  simp only [dotProduct, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hI : I * I = -1 := I_mul_I
  linear_combination (2 * (π : ℂ) ^ 2 * (ξ i : ℂ) ^ 2) * hI

/-- The integrand of `integral_gaussLin` for a diagonal matrix, in the form of Mathlib's
`GaussianFourier.integral_cexp_neg_sum_mul_add`. -/
theorem gaussLin_diagonal {n : ℕ} (b c : Fin n → ℂ) (x : Fin n → ℝ) :
    gaussLin (diagonal b) c x = cexp (-∑ i, b i / 2 * (x i : ℂ) ^ 2 + ∑ i, c i * x i) := by
  rw [gaussLin, linForm, qform_diagonal, neg_div, Finset.sum_div]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Independent cross-check for diagonal matrices: for `Re bᵢ > 0` and every `c`, the
right-hand side of `integral_gaussLin` equals the integral as computed from Mathlib's product
formula `GaussianFourier.integral_cexp_neg_sum_mul_add`. The proof does not use
`integral_gaussLin`. -/
theorem integral_gaussLin_diagonal_mathlib {n : ℕ} (b : Fin n → ℂ) (hb : ∀ i, 0 < (b i).re)
    (c : Fin n → ℂ) :
    (∫ x, cexp (-qform (diagonal b) x / 2)) * cexp ((c ⬝ᵥ ((diagonal b)⁻¹ *ᵥ c)) / 2) =
      ∫ x, gaussLin (diagonal b) c x := by
  have hb0 : ∀ i, b i ≠ 0 := fun i h => by
    have := hb i; rw [h, zero_re] at this; exact lt_irrefl 0 this
  have hb2 : ∀ i, 0 < (b i / 2).re := fun i => by rw [div_ofNat_re]; linarith [hb i]
  have hinv : (diagonal b)⁻¹ = diagonal b⁻¹ := by
    refine inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hb0 i)
  simp_rw [gaussLin_diagonal]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add hb2, integral_gauss_diagonal_prod b hb, hinv,
    dotProduct, Finset.sum_div, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  rw [mulVec_diagonal, Pi.inv_apply]
  field_simp [hb0 i]
  ring

/-- Wrong constant: on `ℝ¹` with `B = 1` and `c = 1`, the factor `e^{⟨B⁻¹ c, c⟩/2}` of
`integral_gaussLin` cannot be replaced by `e^{a ⟨B⁻¹ c, c⟩}` for any real `a ≠ 1/2`. -/
theorem integral_gaussLin_wrong_constant (a : ℝ)
    (h : ∫ x, gaussLin (1 : Matrix (Fin 1) (Fin 1) ℂ) (fun _ => 1) x =
      (∫ x, cexp (-qform (1 : Matrix (Fin 1) (Fin 1) ℂ) x / 2)) *
        cexp (a * ((fun _ => (1 : ℂ)) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ *ᵥ fun _ => 1)))) :
    a = 1 / 2 := by
  rw [integral_gaussLin_one, integral_gauss_one, inv_one, one_mulVec] at h
  have hP : (((2 * π) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
  have h2 := mul_left_cancel₀ hP h
  have hdot : (fun _ => (1 : ℂ)) ⬝ᵥ (fun _ : Fin 1 => (1 : ℂ)) = 1 := by simp [dotProduct]
  rw [hdot, mul_one, show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp,
    ← ofReal_exp] at h2
  exact (Real.exp_injective (ofReal_injective h2)).symm

end Lightlike.Oscillatory
