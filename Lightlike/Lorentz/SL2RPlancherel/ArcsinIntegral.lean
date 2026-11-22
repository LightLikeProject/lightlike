module

public import Mathlib

/-!
# The arcsine integral

`lintegral_inv_sqrt_sub_sq`: `∫_{-R}^{R} du / √(R² - u²) = π`, as a Lebesgue integral in
`[0,∞]`.  It is the elementary integral behind the radial integral formula on the hyperbolic
plane (the Abel transform), milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- **The arcsine integral**: for `R > 0`, `∫_{-R}^{R} du / √(R² - u²) = π`. -/
lemma lintegral_inv_sqrt_sub_sq {R : ℝ} (hR : 0 < R) :
    ∫⁻ u in Ioo (-R) R, ENNReal.ofReal (1 / √(R ^ 2 - u ^ 2)) = ENNReal.ofReal π := by
  have himg : (fun φ : ℝ => R * Real.sin φ) '' Ioo (-(π / 2)) (π / 2) = Ioo (-R) R := by
    ext u
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      have h1 : Real.sin φ < 1 := by
        have := Real.strictMonoOn_sin (Ioo_subset_Icc_self hφ)
          (⟨by linarith [Real.pi_pos], le_refl _⟩ : π / 2 ∈ Icc (-(π / 2)) (π / 2)) hφ.2
        simpa using this
      have h2 : -1 < Real.sin φ := by
        have := Real.strictMonoOn_sin
          (⟨le_refl _, by linarith [Real.pi_pos]⟩ : -(π / 2) ∈ Icc (-(π / 2)) (π / 2))
          (Ioo_subset_Icc_self hφ) hφ.1
        simpa using this
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      have hu1 : -1 < u / R := by rw [lt_div_iff₀ hR]; linarith
      have hu2 : u / R < 1 := by rw [div_lt_iff₀ hR]; linarith
      refine ⟨Real.arcsin (u / R), ⟨Real.neg_pi_div_two_lt_arcsin.2 hu1,
        Real.arcsin_lt_pi_div_two.2 hu2⟩, ?_⟩
      show R * Real.sin (Real.arcsin (u / R)) = u
      rw [Real.sin_arcsin hu1.le hu2.le]
      field_simp
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun φ => R * Real.cos φ)
    (fun φ _ => ((Real.hasDerivAt_sin φ).const_mul R).hasDerivWithinAt)
    (fun a ha b hb hab => by
      have := Real.injOn_sin (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
        (by simpa [hR.ne'] using hab)
      exact this)]
  have : ∀ φ ∈ Ioo (-(π / 2)) (π / 2),
      ENNReal.ofReal |R * Real.cos φ| * ENNReal.ofReal
        (1 / √(R ^ 2 - (R * Real.sin φ) ^ 2)) = 1 := by
    intro φ hφ
    have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo hφ
    have hsq : √(R ^ 2 - (R * Real.sin φ) ^ 2) = R * Real.cos φ := by
      rw [show R ^ 2 - (R * Real.sin φ) ^ 2 = (R * Real.cos φ) ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq φ]]
      exact Real.sqrt_sq (by positivity)
    rw [hsq, abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    rw [mul_one_div_cancel (by positivity)]
    simp
  rw [setLIntegral_congr_fun measurableSet_Ioo this]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul,
    Real.volume_Ioo]
  congr 1
  ring

end Lightlike.Lorentz.SL2R
