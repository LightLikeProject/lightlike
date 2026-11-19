import Lightlike.Asymptotics.Tauberian.Ingham
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Checks of the Tauberian definitions

* Known values: for Lebesgue measure on `[0, ∞)` the Laplace transform is `1 / β` and the counting
  function is `X`.
* A wrong model: Lebesgue measure grows polynomially, `β log (1 / β) → 0`, so it does not satisfy the
  hypothesis `β log L(β) → a` for any `a > 0` of `ingham_log`.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- Lebesgue measure on `[0, ∞)`. -/
abbrev leb : Measure ℝ := volume.restrict (Ici 0)

/-- Known value: the Laplace transform of Lebesgue measure on `[0, ∞)` is `1 / β`. -/
example {β : ℝ} (hβ : 0 < β) : laplace leb β = 1 / β := by
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

end Lightlike.Tauberian
