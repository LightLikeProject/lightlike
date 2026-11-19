import Lightlike.Asymptotics.Tauberian.Ingham
import Lightlike.Asymptotics.Tauberian.Karamata
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Checks of the Tauberian definitions

* Known values: for Lebesgue measure on `[0, ∞)` the Laplace transform is `1 / β` and the counting
  function is `X`.
* Karamata's theorem for Lebesgue measure (`α = 1`, `ℓ = 1`) returns `counting leb t / t → 1 / Γ 2 = 1`,
  the exact value.
* A wrong model: Lebesgue measure grows polynomially, `β log (1 / β) → 0`, so it does not satisfy the
  hypothesis `β log L(β) → a` for any `a > 0` of `ingham_log`.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- Lebesgue measure on `[0, ∞)`. -/
abbrev leb : Measure ℝ := volume.restrict (Ici 0)

/-- Known value: the Laplace transform of Lebesgue measure on `[0, ∞)` is `1 / β`. -/
lemma laplace_leb {β : ℝ} (hβ : 0 < β) : laplace leb β = 1 / β := by
  unfold laplace leb
  rw [integral_Ici_eq_integral_Ioi]
  have := integral_exp_mul_Ioi (a := -β) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at this
  rw [this]
  field_simp

/-- Known value: the counting function of Lebesgue measure on `[0, ∞)` is `X`. -/
example {X : ℝ} (hX : 0 ≤ X) : counting leb X = X := by
  unfold counting leb
  rw [Measure.restrict_apply measurableSet_Icc, inter_eq_left.2 (fun x hx => hx.1), Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Wrong model: Lebesgue measure does not satisfy the hypothesis `β log L(β) → a` for `a > 0`
(polynomial, not exponential, growth of the Laplace transform). -/
example {a : ℝ} (ha : 0 < a) :
    ¬ Tendsto (fun β : ℝ => β * Real.log (laplace leb β)) (𝓝[>] 0) (𝓝 a) := by
  intro h
  have h0 : Tendsto (fun β : ℝ => β * Real.log (laplace leb β)) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one)
    refine (this.neg).congr' ?_ |> fun h' => by simpa using h'
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβ' : 0 < β := hβ
    have hl : laplace leb β = 1 / β := by
      unfold laplace leb
      rw [integral_Ici_eq_integral_Ioi]
      have := integral_exp_mul_Ioi (a := -β) (by linarith) 0
      simp only [mul_zero, Real.exp_zero] at this
      rw [this]
      field_simp
    rw [hl, one_div, Real.log_inv]
    simp [Real.rpow_one]
    ring
  exact ha.ne' (tendsto_nhds_unique h h0)

/-- Karamata's theorem applied to Lebesgue measure (`α = 1`, `ℓ = 1`): `counting leb t / t → 1`,
matching the known value `counting leb t = t`. -/
example : Tendsto (fun t : ℝ => counting leb t / (t ^ (1 : ℝ) * 1)) atTop (𝓝 (1 / Real.Gamma (1 + 1))) := by
  have hℓ : SlowlyVarying (fun _ : ℝ => (1 : ℝ)) :=
    ⟨Eventually.of_forall fun _ => one_pos, fun c _ => by simp⟩
  have hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) leb := by
    intro β hβ
    unfold leb
    exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_mul_Ioi (by linarith) 0)
  refine karamata ?_ hint one_pos hℓ ?_
  · unfold leb
    rw [Measure.restrict_apply measurableSet_Iio,
      show Iio (0 : ℝ) ∩ Ici 0 = ∅ from
        Set.eq_empty_of_forall_notMem fun x hx => absurd (show x < 0 from hx.1) (not_lt.2 hx.2)]
    exact measure_empty
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβ' : 0 < β := hβ
    rw [laplace_leb hβ']
    simp [Real.rpow_neg_one]
    field_simp

end Lightlike.Tauberian
