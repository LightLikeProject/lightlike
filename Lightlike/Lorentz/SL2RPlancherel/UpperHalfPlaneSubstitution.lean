module

public import Mathlib

/-!
# Steps (i) and (ii) of the radial integral formula on the hyperbolic plane

For measurable `Φ : ℝ → [0,∞]`,
`∫_{y>0} ∫_x Φ((x²+y²+1)/(2y)) dx dy/y² = ∫_u ∫_s Φ(√(1+u²) cosh s) ds du`,
by the substitutions `x = y u` and `y = e^s / √(1+u²)` and Tonelli.  Milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- Scaling `x = a u` (`a > 0`) in a Lebesgue integral over `ℝ`. -/
lemma lintegral_comp_scale {a : ℝ} (ha : 0 < a) (g : ℝ → ENNReal) :
    ∫⁻ x, g x = ∫⁻ u, ENNReal.ofReal a * g (a * u) := by
  have himg : (fun u : ℝ => a * u) '' univ = univ := by
    ext x
    simp only [image_univ, mem_range, mem_univ, iff_true]
    exact ⟨x / a, by field_simp⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ)) (f := fun u => a * u)
    (f' := fun _ => a) MeasurableSet.univ
    (fun u _ => ((hasDerivAt_id u).const_mul a).hasDerivWithinAt |>.congr_deriv (by simp))
    (fun u _ v _ h => by simpa [ha.ne'] using h) g
  rw [himg] at h
  simpa [abs_of_pos ha] using h

/-- The substitution `y = e^s / c` in the invariant measure `dy / y` of `(0, ∞)`. -/
lemma lintegral_comp_exp_div {c : ℝ} (hc : 0 < c) (Ψ : ℝ → ENNReal) :
    ∫⁻ y in Ioi (0 : ℝ), Ψ y * ENNReal.ofReal (1 / y) = ∫⁻ s, Ψ (Real.exp s / c) := by
  have himg : (fun s : ℝ => Real.exp s / c) '' univ = Ioi 0 := by
    ext y
    simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨s, rfl⟩
      positivity
    · intro hy
      refine ⟨Real.log (y * c), ?_⟩
      rw [Real.exp_log (by positivity)]
      field_simp
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := (univ : Set ℝ))
    (f := fun s => Real.exp s / c) (f' := fun s => Real.exp s / c) MeasurableSet.univ
    (fun s _ => ((Real.hasDerivAt_exp s).div_const c).hasDerivWithinAt)
    (fun a _ b _ hab => Real.exp_injective (by simpa [hc.ne'] using hab))
    (fun y => Ψ y * ENNReal.ofReal (1 / y))
  rw [himg] at h
  rw [h, Measure.restrict_univ]
  refine lintegral_congr (fun s => ?_)
  have hp : 0 < Real.exp s / c := by positivity
  rw [abs_of_pos hp, ← mul_assoc, mul_comm _ (Ψ _), mul_assoc,
    ← ENNReal.ofReal_mul hp.le, mul_one_div_cancel hp.ne']
  simp

/-- **Steps (i) and (ii)**: for measurable `Φ : ℝ → [0,∞]`,
`∫_{y>0} ∫_x Φ((x²+y²+1)/(2y)) dx dy/y² = ∫_u ∫_s Φ(√(1+u²) cosh s) ds du`. -/
lemma lintegral_radial_step {Φ : ℝ → ENNReal} (hΦ : Measurable Φ) :
    ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x : ℝ, Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) * ENNReal.ofReal (1 / y ^ 2) =
      ∫⁻ u : ℝ, ∫⁻ s : ℝ, Φ (√(1 + u ^ 2) * Real.cosh s) := by
  -- (i) x = y u
  have h1 : ∀ y ∈ Ioi (0 : ℝ),
      ∫⁻ x : ℝ, Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) * ENNReal.ofReal (1 / y ^ 2) =
        ∫⁻ u : ℝ, Φ (y * (u ^ 2 + 1) / 2 + 1 / (2 * y)) * ENNReal.ofReal (1 / y) := by
    intro y hy
    have hy : 0 < y := hy
    rw [lintegral_comp_scale hy (fun x => Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) *
      ENNReal.ofReal (1 / y ^ 2))]
    refine lintegral_congr (fun u => ?_)
    have : (y * u) ^ 2 + y ^ 2 + 1 = (y * (u ^ 2 + 1) / 2 + 1 / (2 * y)) * (2 * y) := by
      field_simp
    rw [this, mul_div_cancel_right₀ _ (by positivity), ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
      ← ENNReal.ofReal_mul hy.le]
    congr 2
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi h1]
  -- swap
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr (fun u => ?_)
    have hc : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hc2 : √(1 + u ^ 2) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt (by positivity)
    rw [lintegral_comp_exp_div hc (fun y => Φ (y * (u ^ 2 + 1) / 2 + 1 / (2 * y)))]
    refine lintegral_congr (fun s => ?_)
    congr 1
    rw [Real.cosh_eq]
    have : (u ^ 2 + 1) = √(1 + u ^ 2) ^ 2 := by rw [hc2]; ring
    rw [this]
    have he : Real.exp (-s) = (Real.exp s)⁻¹ := Real.exp_neg s
    rw [he]
    have : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
    field_simp
  · refine Measurable.aemeasurable ?_
    refine (hΦ.comp ?_).mul ?_
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 * (p.2 ^ 2 + 1) / 2 + 1 / (2 * p.1))
    · exact (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.1))

end Lightlike.Lorentz.SL2R
