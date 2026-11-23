module

public import Mathlib

/-!
# The substitution `t = c cosh s`

`lintegral_comp_cosh`: for `c > 0`, `∫_ℝ Φ(c cosh s) ds = 2 ∫_{t > c} Φ(t) / √(t² - c²) dt`, as
Lebesgue integrals in `[0,∞]`.  It is step (iii) of the radial integral formula on the hyperbolic
plane (the Abel transform), milestone HA3.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The substitution `t = c cosh s` on a set `S` of nonzero `s` on which `cosh` is injective and
whose image is `(c, ∞)`. -/
private lemma lintegral_cosh_sub {c : ℝ} (hc : 0 < c) (Φ : ℝ → ENNReal) {S : Set ℝ}
    (hS : MeasurableSet S) (h0 : ∀ s ∈ S, s ≠ 0) (hinj : InjOn Real.cosh S)
    (himg : (fun s => c * Real.cosh s) '' S = Ioi c) :
    ∫⁻ s in S, Φ (c * Real.cosh s) =
      ∫⁻ t in Ioi c, Φ t * ENNReal.ofReal (1 / √(t ^ 2 - c ^ 2)) := by
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul hS
    (f' := fun s => c * Real.sinh s)
    (fun s _ => ((Real.hasDerivAt_cosh s).const_mul c).hasDerivWithinAt)
    (fun a ha b hb hab => hinj ha hb (by simpa [hc.ne'] using hab))]
  refine setLIntegral_congr_fun hS (fun s hs => ?_)
  have hsh : 0 < |Real.sinh s| := abs_pos.2 (fun h => h0 s hs (Real.sinh_eq_zero.1 h))
  have hsq : √((c * Real.cosh s) ^ 2 - c ^ 2) = c * |Real.sinh s| := by
    rw [show (c * Real.cosh s) ^ 2 - c ^ 2 = (c * |Real.sinh s|) ^ 2 by
      rw [mul_pow, mul_pow, sq_abs, Real.cosh_sq]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq, abs_mul, abs_of_pos hc, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_one_div_cancel (by positivity)]
  simp

/-- **Substitution `t = c cosh s`**: for `c > 0`,
`∫_ℝ Φ(c cosh s) ds = 2 ∫_{t > c} Φ(t) / √(t² - c²) dt`. -/
lemma lintegral_comp_cosh {c : ℝ} (hc : 0 < c) (Φ : ℝ → ENNReal) :
    ∫⁻ s, Φ (c * Real.cosh s) =
      2 * ∫⁻ t in Ioi c, Φ t * ENNReal.ofReal (1 / √(t ^ 2 - c ^ 2)) := by
  have himg : ∀ S : Set ℝ, (S = Ioi 0 ∨ S = Iio 0) →
      (fun s => c * Real.cosh s) '' S = Ioi c := by
    intro S hS
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs0 : s ≠ 0 := by rcases hS with rfl | rfl <;> simp_all [ne_of_gt, ne_of_lt]
      show c < c * Real.cosh s
      have := Real.one_lt_cosh.2 hs0
      nlinarith
    · intro ht
      have h1 : 1 < t / c := by rw [lt_div_iff₀ hc]; simpa using ht
      have hs := Real.cosh_arcosh h1.le
      have hpos : 0 < Real.arcosh (t / c) := Real.arcosh_pos h1
      rcases hS with rfl | rfl
      · exact ⟨_, hpos, by simp only [hs]; field_simp⟩
      · refine ⟨-Real.arcosh (t / c), by simpa using hpos, ?_⟩
        simp only [Real.cosh_neg, hs]; field_simp
  have hpos := lintegral_cosh_sub hc Φ (S := Ioi 0) measurableSet_Ioi
    (fun s hs => ne_of_gt hs)
    (fun a ha b hb hab => Real.cosh_injOn (le_of_lt ha) (le_of_lt hb) hab)
    (himg _ (Or.inl rfl))
  have hneg := lintegral_cosh_sub hc Φ (S := Iio 0) measurableSet_Iio
    (fun s hs => ne_of_lt hs)
    (fun a ha b hb hab => by
      have ha' : a < 0 := ha
      have hb' : b < 0 := hb
      have := Real.cosh_injOn (show (0 : ℝ) ≤ -a by linarith) (show (0 : ℝ) ≤ -b by linarith)
        (by simpa using hab)
      linarith)
    (himg _ (Or.inr rfl))
  have hsplit : ∫⁻ s, Φ (c * Real.cosh s) =
      (∫⁻ s in Ioi 0, Φ (c * Real.cosh s)) + ∫⁻ s in Iio 0, Φ (c * Real.cosh s) := by
    rw [← lintegral_add_compl _ (measurableSet_Ioi (a := (0 : ℝ))), compl_Ioi,
      setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ)))]
  rw [hsplit, hpos, hneg, two_mul]

end Lightlike.Lorentz.SL2R
