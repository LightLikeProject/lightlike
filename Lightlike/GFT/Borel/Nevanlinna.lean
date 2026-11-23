import Lightlike.GFT.Borel.Exists
import Lightlike.GFT.Borel.Laplace

/-!
# The Nevanlinna–Sokal theorem (task T-GF7-P6)

`SokalHyp.nevanlinna_sokal` (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Theorem 1 with `β = 0`):
the first item is `SokalHyp.hasSum_borelT`; the continuation `B` and its bound are `SokalHyp.exists_continuation`
(T-GF7-P4); the Laplace representation is `SokalHyp.eq_laplace_borelZero` (T-GF7-P5) with `B = b₀` on `(0, ∞)`,
the integrability coming from `|b₀(x)| ≤ |a₀| + M e^{c'x}/(2c')` with `1/R < c' < Re z⁻¹`.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

/-- The Laplace integrand of the continuation is integrable on `(0, ∞)` for `z ∈ C_R`. -/
lemma SokalHyp.integrableOn_laplace (h : SokalHyp f a R K ρ) {B : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B (sokalStrip ρ))
    (hB0 : ∀ c : ℝ, 1 / R < c → ∀ x : ℝ, 0 < x → B x = borelZero f (a 0) x c) {z : ℂ} (hz : z ∈ diskC R) :
    IntegrableOn (fun x : ℝ => cexp (-(x / z)) * B x) (Ioi 0) := by
  have hR := h.R_pos
  have hM : ∀ z ∈ diskC R, ‖f z - a 0‖ ≤ K / ρ * ‖z‖ := fun z hz => by
    have := h.rem 1 z hz
    simpa using this
  set r : ℝ := (z⁻¹).re with hr
  have hrR : 1 / R < r := hz
  set c' : ℝ := (1 / R + r) / 2 with hc'
  have hc1 : 1 / R < c' := by rw [hc']; linarith
  have hc2 : c' < r := by rw [hc']; linarith
  have hc0 : 0 < c' := (one_div_pos.2 hR).trans hc1
  set g : ℝ → ℝ := fun x => ‖a 0‖ * Real.exp (-r * x) + K / ρ / (2 * c') * Real.exp (-(r - c') * x) with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    refine Integrable.add ?_ ?_
    · exact (exp_neg_integrableOn_Ioi 0 ((one_div_pos.2 hR).trans hrR)).const_mul _
    · exact (exp_neg_integrableOn_Ioi 0 (sub_pos.2 hc2)).const_mul _
  have hcont : ContinuousOn (fun x : ℝ => cexp (-(x / z)) * B x) (Ioi 0) := by
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) ?_
    refine hB.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => ?_
    exact ⟨x, le_of_lt hx, by simpa using h.ρ_pos⟩
  refine Integrable.mono' hgi (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx : 0 < x := hx
  have hn : ‖cexp (-((x : ℂ) / z))‖ = Real.exp (-r * x) := by
    rw [Complex.norm_exp]
    congr 1
    have : (x : ℂ) / z = (x : ℂ) * z⁻¹ := by rw [div_eq_mul_inv]
    rw [this]
    simp [hr]
    ring
  have hb : ‖B x‖ ≤ ‖a 0‖ + Real.exp (x * c') * (K / ρ) / (2 * c') := by
    rw [hB0 c' hc1 x hx]
    have h1 := norm_borelZero_sub_le hR hM x hc1
    have h2 := norm_add_le (borelZero f (a 0) x c' - a 0) (a 0)
    rw [sub_add_cancel] at h2
    linarith
  rw [norm_mul, hn]
  have hex : Real.exp (-r * x) * Real.exp (x * c') = Real.exp (-(r - c') * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-r * x) * ‖B x‖ ≤ Real.exp (-r * x) * (‖a 0‖ + Real.exp (x * c') * (K / ρ) / (2 * c')) := by
        gcongr
    _ = g x := by
        rw [hg]
        simp only
        have : Real.exp (-r * x) * (Real.exp (x * c') * (K / ρ) / (2 * c')) =
            K / ρ / (2 * c') * Real.exp (-(r - c') * x) := by
          rw [← hex]
          ring
        rw [mul_add, this]
        ring

/-- **The Nevanlinna–Sokal theorem** (task T-GF7-P6; Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2,
Theorem 1, eqs. (2.4)-(2.6), pp. 5-6, with `β = 0`): statement copied word for word from `Tasks/GF/T_GF7_P6.lean`.
Non-vacuous: `sokalHyp_const`. -/
theorem SokalHyp.nevanlinna_sokal {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) :
    (∀ t : ℂ, ‖t‖ < ρ → HasSum (fun k => a k * t ^ k / (k ! : ℂ)) (borelT a t)) ∧
      ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧ (∀ t : ℂ, ‖t‖ < ρ → B t = borelT a t) ∧
        (∀ ρ' : ℝ, ρ' < ρ → ∃ C : ℝ, ∀ t ∈ sokalStrip ρ', ‖B t‖ ≤ C * Real.exp (‖t‖ / R)) ∧
        ∀ z ∈ diskC R, IntegrableOn (fun x : ℝ => cexp (-(x / z)) * B x) (Ioi 0) ∧
          f z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * B x := by
  refine ⟨fun t ht => h.hasSum_borelT ht, ?_⟩
  obtain ⟨B, hBan, hBt, hBx, hBb⟩ := h.exists_continuation
  refine ⟨B, hBan, hBt, hBb, fun z hz => ⟨h.integrableOn_laplace hBan hBx hz, ?_⟩⟩
  have hc : 1 / R < 1 / R + 1 := by linarith
  rw [h.eq_laplace_borelZero hc hz]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [hBx _ hc x hx]

end Lightlike.FieldTheory.Borel
