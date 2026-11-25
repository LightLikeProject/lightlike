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

/-- The projector absorbs `C (D-1)` on both sides, by the same scalar. -/
theorem proj_absorb (q : kˣ) {D : ℕ} (hd : ∀ j, j < D → chebD (loopVal q) j ≠ 0) {Z : Module.End k (ModelSpace k)}
    (hZ : Z ∈ CSub q (D - 1)) :
    ∃ ε : k, Z * jwAt q 0 D = ε • jwAt q 0 D ∧ jwAt q 0 D * Z = ε • jwAt q 0 D := by
  have hprops := jwProps_of_le (isTL_shift q 0) D hd D le_rfl
  have hjw : jwAt q 0 D = jw (loopVal q) (modelE q) D := rfl
  have hL : ∀ j < D - 1, modelE q j * jwAt q 0 D = 0 := fun j hj => by
    rw [hjw]; exact hprops.killL j (by omega)
  have hR : ∀ j < D - 1, jwAt q 0 D * modelE q j = 0 := fun j hj => by
    rw [hjw]; exact hprops.killR j (by omega)
  obtain ⟨c, h1, h2⟩ := absorb (k := k) (e := modelE q) (p := jwAt q 0 D) hL hR _ hZ
  exact ⟨c, h2, h1⟩

/-- **Extra caps next to the projector die.** -/
theorem caps_mul_proj_zero (q : kˣ) (hδ : loopVal q ≠ 0) {D : ℕ} (hd : ∀ j, j < D → chebD (loopVal q) j ≠ 0)
    (hd' : ∀ j, j < D + 1 → chebD (loopVal q) j ≠ 0) {Z A : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q (D - 1))
    (μ j : ℕ) (hμ : μ + j + 2 ≤ D) :
    A * nestCap q μ (j + 1) * Z * jwAt q 0 D = 0 := by
  obtain ⟨ε, h1, -⟩ := proj_absorb q hd hZ
  have hc := cap_mul_proj_zero (k := k) q hδ hd' (D := D) (N := D + 1) (by omega) (m := μ + j) hμ
  have e : nestCap q μ (j + 1) = nestCap q μ j * capOp q (μ + j) := rfl
  calc A * nestCap q μ (j + 1) * Z * jwAt q 0 D = A * (nestCap q μ j * capOp q (μ + j)) * (Z * jwAt q 0 D) := by
        rw [e]; simp only [mul_assoc]
    _ = 0 := by rw [h1, mul_smul_comm]; simp only [mul_assoc, hc, mul_zero, smul_zero]

/-- **Extra cups next to the projector die.** -/
theorem proj_mul_cups_zero (q : kˣ) (hδ : loopVal q ≠ 0) {D : ℕ} (hd : ∀ j, j < D → chebD (loopVal q) j ≠ 0)
    (hd' : ∀ j, j < D + 1 → chebD (loopVal q) j ≠ 0) {Z A : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q (D - 1))
    (μ j : ℕ) (hμ : μ + j + 2 ≤ D) :
    jwAt q 0 D * Z * nestCup q μ (j + 1) * A = 0 := by
  obtain ⟨ε, -, h2⟩ := proj_absorb q hd hZ
  have hc := proj_mul_cup_zero (k := k) q hδ hd' (D := D) (N := D + 1) (by omega) (m := μ + j) hμ
  have e : nestCup q μ (j + 1) = cupOp q (μ + j) * nestCup q μ j := rfl
  calc jwAt q 0 D * Z * nestCup q μ (j + 1) * A = (jwAt q 0 D * Z) * (cupOp q (μ + j) * nestCup q μ j) * A := by
        rw [e]
    _ = 0 := by rw [h2, smul_mul_assoc, smul_mul_assoc]; simp only [mul_assoc]; rw [← mul_assoc (jwAt q 0 D), hc, zero_mul, smul_zero]

/-- **Caps in excess, case `e ≤ f`**: the word is a stack of `j + 1` outer caps times an element of `C (D₂ - 1)`. -/
theorem unbal_caps_1 (q : kˣ) {N : ℕ} {Z YL YR : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q N)
    (e t d' j lam l l' l'' : ℕ) (hYL : YL ∈ CSub q (N - 2 * e)) (hYR : YR ∈ CSub q (N - 2 * e - 2 * t))
    (h1 : l + 2 * e ≤ N + 1) (h1' : l' + t + 2 * e ≤ N + 1)
    (h2 : lam + (j + 1) + d' + 2 * t ≤ N - 2 * e + 1) (h2' : l' + 2 * t ≤ N - 2 * e + 1)
    (h3 : lam + (j + 1) + 2 * d' ≤ N - 2 * e - 2 * t + 1) (h3' : l'' + 2 * d' ≤ N - 2 * e - 2 * t + 1) :
    ∃ Z3 ∈ CSub q (N - 2 * e - 2 * t - 2 * d'),
      nestCap q lam (((j + 1) + d') + t) * YL * nestCap q l e * Z * nestCup q l' (t + e) * YR * nestCup q l'' d' =
        nestCap q lam (j + 1) * Z3 := by
  have hZ1 := nestCap_mul_nestCup_mem_gen q l (l' + t) e N hZ h1 h1'
  have hY1 : YL * (nestCap q l e * Z * nestCup q (l' + t) e) ∈ CSub q (N - 2 * e) := Subalgebra.mul_mem _ hYL hZ1
  have hZ2 := nestCap_mul_nestCup_mem_gen q (lam + ((j + 1) + d')) l' t (N - 2 * e) hY1
    (by omega) h2'
  have hZ2' : nestCap q (lam + ((j + 1) + d')) t * (YL * (nestCap q l e * Z * nestCup q (l' + t) e)) *
      nestCup q l' t * YR ∈ CSub q (N - 2 * e - 2 * t) := Subalgebra.mul_mem _ hZ2 hYR
  have hZ3 := nestCap_mul_nestCup_mem_gen q (lam + (j + 1)) l'' d' (N - 2 * e - 2 * t) hZ2' h3 h3'
  refine ⟨_, hZ3, ?_⟩
  rw [nestCap_add q lam ((j + 1) + d') t, nestCap_add q lam (j + 1) d', nestCup_add]
  simp only [mul_assoc]

end Lightlike.TemperleyLieb
