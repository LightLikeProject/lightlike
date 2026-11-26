import Mathlib
import Lightlike.TemperleyLieb.Vertex
import Lightlike.TemperleyLieb.Natural

/-!
# The norm of the trivalent vertex in closed form: the first cases

`vertex_norm` shows that the vertex sandwich `p_c · (nestCap · p_a p_b' · nestCup) · p_c` is a scalar multiple
`κ p_c`, without computing `κ`. Here `κ` is computed in the cases `(a, b, i) = (1, 1, 1)`, `(2, 1, 1)` and, for
every `a = n + 1`, `(a, 1, 1)` with the value `d_a / d_{a-1}` (`vertex_norm_succ_one`), from the partial trace
of the Jones–Wenzl projector with caps and cups (`cap_jwAt_cup`).
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

/-- The projector on the strands `0, …, n - 1` commutes with the cup at the position `n`. -/
theorem jwAt_comm_cup (q : kˣ) (n : ℕ) : jwAt q 0 n * cupOp q n = cupOp q n * jwAt q 0 n := by
  have hmem : jwAt q 0 n ∈ CSub q (n - 1) := by simpa using jwAt_mem q 0 n
  have hle : CSub q (n - 1) ≤ Subalgebra.centralizer k {cupOp q n} := by
    unfold CSub tlSub
    refine Algebra.adjoin_le ?_
    rintro x ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (e_mul_cup_near q (by omega)).symm
  have h := hle hmem
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h (cupOp q n) (Set.mem_singleton _)).symm

/-- Cancelling the zigzags: `cap_{n+1} (cup_n Y cap_n) cup_{n+1} = Y`. -/
theorem cap_cup_cancel (q : kˣ) (n : ℕ) (Y : Module.End k (ModelSpace k)) :
    capOp q (n + 1) * (cupOp q n * Y * capOp q n) * cupOp q (n + 1) = Y := by
  have hL : capOp q (n + 1) * cupOp q n = 1 := cap_succ_cup q n
  have hR : capOp q n * cupOp q (n + 1) = 1 := cap_cup_succ q n
  calc capOp q (n + 1) * (cupOp q n * Y * capOp q n) * cupOp q (n + 1)
      = (capOp q (n + 1) * cupOp q n) * Y * (capOp q n * cupOp q (n + 1)) := by
        simp only [mul_assoc]
    _ = Y := by rw [hL, hR, one_mul, mul_one]

/-- **Partial trace of a projector, with caps and cups**: closing the last strand of `p_{n+1}` gives
`(d_{n+1} / d_n) p_n`. -/
theorem cap_jwAt_cup (q : kˣ) {n : ℕ} (hp : JwProps (loopVal q) (modelE q) n)
    (hdn : chebD (loopVal q) n ≠ 0) :
    capOp q n * jwAt q 0 (n + 1) * cupOp q n =
      (chebD (loopVal q) (n + 1) / chebD (loopVal q) n) • jwAt q 0 n := by
  have hpt := jw_partial_trace (isTL_shift q 0) hp hdn
  have hpt' : modelE q n * jwAt q 0 (n + 1) * modelE q n =
      (chebD (loopVal q) (n + 1) / chebD (loopVal q) n) • (jwAt q 0 n * modelE q n) := hpt
  have hX : cupOp q n * (capOp q n * jwAt q 0 (n + 1) * cupOp q n) * capOp q n =
      cupOp q n * ((chebD (loopVal q) (n + 1) / chebD (loopVal q) n) • jwAt q 0 n) * capOp q n := by
    have e1 : cupOp q n * (capOp q n * jwAt q 0 (n + 1) * cupOp q n) * capOp q n =
        modelE q n * jwAt q 0 (n + 1) * modelE q n := by
      rw [← cup_cap]; simp only [mul_assoc]
    rw [e1, hpt', ← cup_cap]
    have := jwAt_comm_cup (k := k) q n
    simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    rw [← mul_assoc (jwAt q 0 n), this]
    simp only [mul_assoc]
  have h := congrArg (fun z => capOp q (n + 1) * z * cupOp q (n + 1)) hX
  simp only [cap_cup_cancel] at h
  exact h

/-- **The vertex `(a, 1; a - 1)` with one junction arc**: the sandwich of the nested junction with a
single strand on the right is `d_a / d_{a-1}` times the projector `p_{a-1}`; with the projectors
`p_{a-1}` on both sides, `κ(a, 1, 1) = d_a / d_{a-1}`. -/
theorem vertex_norm_succ_one (q : kˣ) (n : ℕ) (hp : JwProps (loopVal q) (modelE q) n)
    (hdn : chebD (loopVal q) n ≠ 0) :
    jwAt q 0 n * (nestCap q n 1 * (jwAt q 0 (n + 1) * jwAt q (n + 1) 1) * nestCup q n 1) *
        jwAt q 0 n =
      (chebD (loopVal q) (n + 1) / chebD (loopVal q) n) • jwAt q 0 n := by
  have h1 : jwAt q (n + 1) 1 = 1 := by simp [jwAt, jw_one]
  have hidem : jwAt q 0 n * jwAt q 0 n = jwAt q 0 n := hp.idem
  have hcc := cap_jwAt_cup (k := k) q hp hdn
  simp only [nestCap, nestCup, h1, mul_one, one_mul, add_zero]
  rw [hcc, mul_smul_comm, smul_mul_assoc, hidem]
  rw [hidem]

end Lightlike.TemperleyLieb
