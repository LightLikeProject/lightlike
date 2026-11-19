import Lightlike.Asymptotics.Tauberian.Window

/-!
# Scaling of the Laplace transform under regular variation

A function `ℓ` is *slowly varying* if it is eventually positive and `ℓ (c t) / ℓ t → 1` as `t → ∞`
for every `c > 0`. If the Laplace transform of `ρ` is regularly varying, `L(β) ~ β^{-α} ℓ(1/β)` as
`β → 0⁺`, then for each `β > 0`, `L(β / t) / (t^α ℓ(t)) → β^{-α}` as `t → ∞`
(`tendsto_scaled_laplace`): the starting point of Karamata's method.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- A **slowly varying** function: eventually positive with `ℓ (c t) / ℓ t → 1` for every `c > 0`. -/
def SlowlyVarying (ℓ : ℝ → ℝ) : Prop :=
  (∀ᶠ t in atTop, 0 < ℓ t) ∧ ∀ c : ℝ, 0 < c → Tendsto (fun t => ℓ (c * t) / ℓ t) atTop (𝓝 1)

/-- **Scaled Laplace transform.** -/
lemma tendsto_scaled_laplace {ρ : Measure ℝ} {α : ℝ} {ℓ : ℝ → ℝ} (hℓ : SlowlyVarying ℓ)
    (hL : Tendsto (fun β : ℝ => laplace ρ β / (β ^ (-α) * ℓ (1 / β))) (𝓝[>] 0) (𝓝 1)) {β : ℝ}
    (hβ : 0 < β) :
    Tendsto (fun t : ℝ => laplace ρ (β / t) / (t ^ α * ℓ t)) atTop (𝓝 (β ^ (-α))) := by
  -- `β / t → 0⁺`
  have hβt : Tendsto (fun t : ℝ => β / t) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop tendsto_id,
      eventually_gt_atTop 0 |>.mono fun t ht => div_pos hβ ht⟩
  have h1 := hL.comp hβt
  have h2 := (hℓ.2 (1 / β) (by positivity))
  have h3 := h1.mul (h2.const_mul (β ^ (-α)))
  rw [show β ^ (-α) = 1 * (β ^ (-α) * 1) by ring]
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hℓ.1,
    (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 1 / β)).eventually hℓ.1] with t ht hℓt hℓt'
  simp only [Function.comp, id] at hℓt' ⊢
  have e1 : (β / t) ^ (-α) = β ^ (-α) * t ^ α := by
    rw [Real.div_rpow hβ.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
  have e2 : 1 / (β / t) = 1 / β * t := by field_simp
  have hℓ' : ℓ (1 / β * t) ≠ 0 := hℓt'.ne'
  have hβα : β ^ (-α) ≠ 0 := (Real.rpow_pos_of_pos hβ _).ne'
  have htα : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  have hℓ'' : ℓ (t / β) ≠ 0 := by
    have : 1 / β * t = t / β := by field_simp
    rwa [this] at hℓ'
  rw [e1, e2]
  field_simp

end Lightlike.Tauberian
