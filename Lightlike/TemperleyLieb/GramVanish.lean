import Mathlib
import Lightlike.TemperleyLieb.Gram

/-!
# The Gram pairing vanishes between different total channels

When the numbers of caps and cups differ, the pairing of caps and cups from the middle outward leaves caps (or cups)
at the outside; they meet a projector `p_D` that kills them (`cap_m p_D = 0`, `p_D cup_m = 0`), after the element of `C`
in between has been absorbed (`Z p_D = ε p_D`).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- `cap_m · p_D = 0` for `m + 2 ≤ D`. -/
theorem cap_mul_proj_zero (q : kˣ) (hδ : loopVal q ≠ 0) {D N : ℕ} (hd : ∀ j, j < N → chebD (loopVal q) j ≠ 0)
    (hDN : D ≤ N) {m : ℕ} (hm : m + 2 ≤ D) : (capOp q m : Module.End k (ModelSpace k)) * jwAt q 0 D = 0 := by
  have h1 := modelE_mul_jwAt (k := k) q hDN hd (j := m) (by omega)
  have h2 : (capOp q m : Module.End k (ModelSpace k)) * (cupOp q m * capOp q m * jwAt q 0 D) = 0 := by
    rw [cup_cap, h1, mul_zero]
  have h3 : (capOp q m : Module.End k (ModelSpace k)) * cupOp q m = loopVal q • 1 := by
    rw [cap_cup, Algebra.algebraMap_eq_smul_one]; rfl
  have h4 : loopVal q • ((capOp q m : Module.End k (ModelSpace k)) * jwAt q 0 D) = 0 := by
    calc loopVal q • ((capOp q m : Module.End k (ModelSpace k)) * jwAt q 0 D)
        = (capOp q m * cupOp q m) * capOp q m * jwAt q 0 D := by rw [h3]; simp [smul_mul_assoc]
      _ = capOp q m * (cupOp q m * capOp q m * jwAt q 0 D) := by simp only [mul_assoc]
      _ = 0 := h2
  rcases smul_eq_zero.mp h4 with h | h
  · exact absurd h hδ
  · exact h

/-- `p_D · cup_m = 0` for `m + 2 ≤ D`. -/
theorem proj_mul_cup_zero (q : kˣ) (hδ : loopVal q ≠ 0) {D N : ℕ} (hd : ∀ j, j < N → chebD (loopVal q) j ≠ 0)
    (hDN : D ≤ N) {m : ℕ} (hm : m + 2 ≤ D) : (jwAt q 0 D : Module.End k (ModelSpace k)) * cupOp q m = 0 := by
  have hp := (jwProps_of_le (isTL_shift q 0) N hd D hDN).killR m (by omega)
  have h1 : (jwAt q 0 D : Module.End k (ModelSpace k)) * modelE q m = 0 := by simpa [jwAt] using hp
  have h3 : (capOp q m : Module.End k (ModelSpace k)) * cupOp q m = loopVal q • 1 := by
    rw [cap_cup, Algebra.algebraMap_eq_smul_one]; rfl
  have h4 : loopVal q • ((jwAt q 0 D : Module.End k (ModelSpace k)) * cupOp q m) = 0 := by
    calc loopVal q • ((jwAt q 0 D : Module.End k (ModelSpace k)) * cupOp q m)
        = jwAt q 0 D * cupOp q m * (capOp q m * cupOp q m) := by
          rw [h3]; simp [mul_smul_comm]
      _ = (jwAt q 0 D * (cupOp q m * capOp q m)) * cupOp q m := by simp only [mul_assoc]
      _ = 0 := by rw [cup_cap, h1, zero_mul]
  rcases smul_eq_zero.mp h4 with h | h
  · exact absurd h hδ
  · exact h

end Lightlike.TemperleyLieb
