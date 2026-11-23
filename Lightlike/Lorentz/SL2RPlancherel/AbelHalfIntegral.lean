module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelTransform

/-!
# The Abel transform as a half-order Riemann–Liouville integral

For `c = cosh t` the Abel transform `𝒜F(t) = ∫_ℝ F(c + w²/2) dw` (`abelTransform`) equals
`√2 ∫_{u > c} F(u) (u − c)^{-1/2} du`: the substitution `s = w²/2` on `w > 0` and `u = c + s`.
This exhibits `F ↦ 𝒜F ∘ arcosh` as a fractional integral of order `1/2`, the form in which the
Abel inversion and the Plancherel density `ρ tanh(πρ)` are derived.

No integrability is assumed: Mathlib's integral is `0` on non-integrable functions and the
change-of-variables theorems used hold in that generality.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.Lorentz.SL2RPlancherel

/-- A complex-valued version of `MeasureTheory.integral_comp_abs`: for `f : ℝ → ℂ`,
`∫_ℝ f |x| = 2 ∫_{x > 0} f x`, with no integrability assumption. -/
theorem integral_comp_abs_complex (f : ℝ → ℂ) :
    ∫ x : ℝ, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

/-- The substitution `s = w²/2` on `w > 0`:
`∫_{w>0} F(c + w²/2) dw = ∫_{s>0} (√(2s))⁻¹ F(c + s) ds`. -/
theorem integral_Ioi_sq_div_two (F : ℝ → ℂ) (c : ℝ) :
    ∫ w in Ioi (0 : ℝ), F (c + w ^ 2 / 2) =
      ∫ s in Ioi (0 : ℝ), (Real.sqrt (2 * s))⁻¹ • F (c + s) := by
  have himg : (fun w : ℝ => w ^ 2 / 2) '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact div_pos (pow_pos hw 2) (by norm_num)
    · intro hx
      refine ⟨Real.sqrt (2 * x), Real.sqrt_pos.mpr (by simpa using hx), ?_⟩
      show Real.sqrt (2 * x) ^ 2 / 2 = x
      rw [Real.sq_sqrt (by simpa using hx.le)]
      ring
  have key := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun w : ℝ => w ^ 2 / 2) (f' := fun w => w) measurableSet_Ioi
    (fun x _ => by
      have := ((hasDerivAt_pow 2 x).div_const 2).hasDerivWithinAt (s := Ioi 0)
      convert this using 1
      simp)
    (fun a ha b hb h => by
      have ha' : 0 < a := ha
      have hb' : 0 < b := hb
      have : a ^ 2 = b ^ 2 := by simpa using h
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)])
    (fun s => (Real.sqrt (2 * s))⁻¹ • F (c + s))
  rw [himg] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w hw => ?_)
  have hw' : 0 < w := hw
  have h2 : Real.sqrt (2 * (w ^ 2 / 2)) = w := by
    rw [show 2 * (w ^ 2 / 2) = w ^ 2 by ring, Real.sqrt_sq hw'.le]
  simp only [h2, abs_of_pos hw', smul_smul, mul_inv_cancel₀ hw'.ne', one_smul]

/-- The translation `u = c + s`: `∫_{s>0} G(c + s) ds = ∫_{u>c} G u du`. -/
theorem integral_Ioi_add_left (G : ℝ → ℂ) (c : ℝ) :
    ∫ s in Ioi (0 : ℝ), G (c + s) = ∫ u in Ioi c, G u := by
  have key := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun s : ℝ => c + s) (f' := fun _ => 1) measurableSet_Ioi
    (fun x _ => ((hasDerivAt_id x).const_add c).hasDerivWithinAt)
    (fun a _ b _ h => by simpa using h) G
  rw [Set.image_const_add_Ioi, add_zero] at key
  rw [key]
  simp

/-- **The Abel transform is a half-order fractional integral**:
`∫_ℝ F(c + w²/2) dw = √2 ∫_{u>c} (√(u − c))⁻¹ F(u) du`. In particular
`𝒜F(t) = √2 ∫_{u > cosh t} F(u)/√(u − cosh t) du`. -/
theorem integral_sq_div_two_eq (F : ℝ → ℂ) (c : ℝ) :
    ∫ w : ℝ, F (c + w ^ 2 / 2) =
      (Real.sqrt 2 : ℂ) * ∫ u in Ioi c, (Real.sqrt (u - c))⁻¹ • F u := by
  have h1 := integral_comp_abs_complex (fun w => F (c + w ^ 2 / 2))
  simp only [sq_abs] at h1
  rw [h1, integral_Ioi_sq_div_two]
  have h2 : ∫ s in Ioi (0 : ℝ), (Real.sqrt (2 * s))⁻¹ • F (c + s) =
      ∫ s in Ioi (0 : ℝ), ((Real.sqrt 2)⁻¹ : ℝ) •
        ((fun u => (Real.sqrt (u - c))⁻¹ • F u) (c + s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hs' : 0 ≤ s := le_of_lt hs
    simp only [add_sub_cancel_left, smul_smul, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_inv]
  rw [h2, integral_smul, integral_Ioi_add_left (fun u => (Real.sqrt (u - c))⁻¹ • F u) c,
    Complex.real_smul]
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h22 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  push_cast
  field_simp
  rw [h22]

/-- `𝒜F(t) = √2 ∫_{u > cosh t} F(u)/√(u − cosh t) du`. -/
theorem abelTransform_eq (F : ℝ → ℂ) (t : ℝ) :
    abelTransform F t =
      (Real.sqrt 2 : ℂ) * ∫ u in Ioi (Real.cosh t), (Real.sqrt (u - Real.cosh t))⁻¹ • F u :=
  integral_sq_div_two_eq F (Real.cosh t)

end Lightlike.Lorentz.SL2RPlancherel
