import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The tangent-line bound for the square root

`2 √(a (Δ - k)) ≤ 2 √(a Δ) - √(a/Δ) · k` for `k ≤ Δ`: the concave function `x ↦ 2√(a x)` lies below
its tangent at `Δ`.  Used to bound `exp (2 √(a (Δ - k)))` by `exp (2 √(a Δ)) · exp (-β k)`
with `β = √(a/Δ)`.
-/

open Real

namespace Lightlike.Tauberian

/-- The tangent-line bound. -/
lemma two_sqrt_le_tangent {a Δ k : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hk : k ≤ Δ) :
    2 * √(a * (Δ - k)) ≤ 2 * √(a * Δ) - √(a / Δ) * k := by
  have hq : 0 ≤ Δ - k := by linarith
  set s := √a with hs
  set r := √Δ with hr
  set q := √(Δ - k) with hq'
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hr0 : 0 < r := Real.sqrt_pos.2 hΔ
  have hr2 : r ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have hq2 : q ^ 2 = Δ - k := Real.sq_sqrt hq
  have e1 : √(a * (Δ - k)) = s * q := Real.sqrt_mul ha.le _
  have e2 : √(a * Δ) = s * r := Real.sqrt_mul ha.le _
  have e3 : √(a / Δ) = s / r := Real.sqrt_div ha.le _
  rw [e1, e2, e3]
  have hk' : k = r ^ 2 - q ^ 2 := by rw [hr2, hq2]; ring
  rw [hk', div_mul_eq_mul_div, ← sub_nonneg]
  have : 2 * (s * r) - s * (r ^ 2 - q ^ 2) / r - 2 * (s * q) = s * (r - q) ^ 2 / r := by
    field_simp; ring
  rw [this]; positivity

/-- `exp (2 √(a (Δ - k))) ≤ exp (2 √(a Δ)) · exp (-β k)`, `β = √(a/Δ)`. -/
lemma exp_two_sqrt_le {a Δ k : ℝ} (ha : 0 < a) (hΔ : 0 < Δ) (hk : k ≤ Δ) :
    Real.exp (2 * √(a * (Δ - k))) ≤ Real.exp (2 * √(a * Δ)) * Real.exp (-(√(a / Δ) * k)) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by linarith [two_sqrt_le_tangent ha hΔ hk])

end Lightlike.Tauberian
