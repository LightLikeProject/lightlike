module

public import Lightlike.Lorentz.SL2RPlancherel.KKParseval

/-!
# Orthogonality of the characters on the box `(0,1]²`

`integral_box_char`: for `n : Fin 2 → ℤ`, `∫_{(0,1]²} e^{-2πi (n₀ x₀ + n₁ x₁)} dx` is `1` if `n = 0` and `0`
otherwise. With it the `K × K`-Fourier component `kkCoeff` of a function whose profile is a finite trigonometric
polynomial can be read off (`kkCoeff_char`).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `∫_0^1 e^{-2πi p x} dx = 1` for `p = 0` and `0` otherwise. -/
lemma integral_Ioc_exp_int (p : ℤ) :
    ∫ x in Ioc (0 : ℝ) 1, Complex.exp (-(2 * π * Complex.I * (p : ℂ) * (x : ℂ))) = if p = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  by_cases hp : p = 0
  · subst hp; simp
  · simp only [hp, ↓reduceIte]
    have hc : (-(2 * π * Complex.I * (p : ℂ)) : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : (p : ℂ) ≠ 0 := by exact_mod_cast hp
      simp [Complex.I_ne_zero, *]
    have h1 : ∀ x : ℝ, Complex.exp (-(2 * π * Complex.I * (p : ℂ) * (x : ℂ))) =
        Complex.exp ((-(2 * π * Complex.I * (p : ℂ))) * (x : ℂ)) := fun x => by ring_nf
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((-(2 * π * Complex.I * (p : ℂ))) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (-(2 * π * Complex.I * (p : ℂ))) * ((1 : ℝ) : ℂ) = ((-p : ℤ) : ℂ) * (2 * π * Complex.I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h2]
    simp

/-- **Orthogonality of characters on the box.** -/
theorem integral_box_char (n : Fin 2 → ℤ) :
    ∫ x in box, Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) =
      if n = 0 then 1 else 0 := by
  have hmp := volume_preserving_finTwoArrow ℝ
  have hbox : box = (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹'
      (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
    ext x
    simp [box, Fin.forall_fin_two, MeasurableEquiv.finTwoArrow]
  set g : ℝ × ℝ → ℂ := fun p => Complex.exp (-(2 * π * Complex.I * (n 0 : ℂ) * (p.1 : ℂ))) *
    Complex.exp (-(2 * π * Complex.I * (n 1 : ℂ) * (p.2 : ℂ))) with hg
  have h1 : ∀ x : Fin 2 → ℝ, Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) =
      g (MeasurableEquiv.finTwoArrow x) := by
    intro x
    simp only [hg, MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo_apply, Fin.sum_univ_two]
    rw [← Complex.exp_add]
    congr 1
    ring
  have h2 := hmp.setIntegral_preimage_emb (MeasurableEquiv.finTwoArrow.measurableEmbedding) g
    (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)
  rw [hbox]
  simp_rw [h1]
  rw [h2, Measure.volume_eq_prod]
  have h3 := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => Complex.exp (-(2 * π * Complex.I * (n 0 : ℂ) * (x : ℂ))))
    (fun y : ℝ => Complex.exp (-(2 * π * Complex.I * (n 1 : ℂ) * (y : ℂ)))) (Ioc (0 : ℝ) 1) (Ioc (0 : ℝ) 1)
  simp only [hg]
  rw [h3, integral_Ioc_exp_int, integral_Ioc_exp_int]
  by_cases h0 : n 0 = 0
  · by_cases h1' : n 1 = 0
    · have : n = 0 := by ext i; fin_cases i <;> simp [h0, h1']
      simp [this]
    · have : n ≠ 0 := fun h => h1' (by simp [h])
      simp [h0, h1', this]
  · have : n ≠ 0 := fun h => h0 (by simp [h])
    simp [h0, this]

end Lightlike.Lorentz.SL2RPlancherel
