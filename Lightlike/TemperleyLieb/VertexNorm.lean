import Mathlib
import Lightlike.TemperleyLieb.Vertex
import Lightlike.TemperleyLieb.Natural

/-!
# The norm of the trivalent vertex in closed form: the first cases

`vertex_norm` shows that the vertex sandwich `p_c · (nestCap · p_a p_b' · nestCup) · p_c` is a scalar multiple
`κ p_c`, without computing `κ`. Here `κ` is computed in the cases `(a, b, i) = (1, 1, 1)` and `(2, 1, 1)`.
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- `(1, 1, 1)`: two strands joined by one cup and cap, `c = 0`; the sandwich is the loop value. -/
theorem vertex_norm_one_one (q : kˣ) :
    nestCap q 0 1 * (jwAt q 0 1 * jwAt q 1 1) * nestCup q 0 1 =
      loopVal q • (1 : Module.End k (ModelSpace k)) := by
  have h := cap_cup (k := k) q 0
  simp only [nestCap, nestCup, jwAt, jw_one, one_mul, mul_one] at *
  rw [h]
  simp [loopVal, Algebra.algebraMap_eq_smul_one]

/-- `(2, 1, 1)`: the projector `p_2 = 1 - δ⁻¹ e₀` on two strands joined to one strand, `c = 1`, where
`p_1 = 1`; the sandwich is `δ - δ⁻¹`, that is `d₂ / d₁`. -/
theorem vertex_norm_two_one (q : kˣ) :
    nestCap q 1 1 * (jwAt q 0 2 * jwAt q 2 1) * nestCup q 1 1 =
      (loopVal q - (loopVal q)⁻¹) • (1 : Module.End k (ModelSpace k)) := by
  have h2 : jwAt q 0 2 = 1 - (loopVal q)⁻¹ • modelE q 0 := by
    have := jw_succ_succ (δ := (loopVal q : k)) (e := modelE q) 0
    simp only [jwAt, zero_add, chebD, jw_one, one_mul, mul_one] at this ⊢
    simpa using this
  have h1 : jwAt q 2 1 = 1 := by simp [jwAt, jw_one]
  have hc := cap_cup (k := k) q 1
  have hz1 : capOp q 1 * modelE q 0 * cupOp q 1 = 1 := by
    have : capOp q 1 * modelE q 0 * cupOp q 1 =
        (capOp q 1 * cupOp q 0) * (capOp q 0 * cupOp q 1) := by
      rw [← cup_cap]; simp only [mul_assoc]
    rw [this, cap_succ_cup, cap_cup_succ, one_mul]
  have hloop : capOp q 1 * cupOp q 1 = loopVal q • (1 : Module.End k (ModelSpace k)) := by
    rw [hc]; simp [loopVal, Algebra.algebraMap_eq_smul_one]
  have : nestCap q 1 1 * (jwAt q 0 2 * jwAt q 2 1) * nestCup q 1 1 =
      capOp q 1 * cupOp q 1 - (loopVal q)⁻¹ • (capOp q 1 * modelE q 0 * cupOp q 1) := by
    simp only [nestCap, nestCup, h2, h1, mul_one, one_mul, add_zero]
    refine LinearMap.ext fun x => ?_
    simp [Module.End.mul_apply, LinearMap.sub_apply, map_sub, map_smul, mul_assoc]
  rw [this, hz1, hloop]
  module

end Lightlike.TemperleyLieb
