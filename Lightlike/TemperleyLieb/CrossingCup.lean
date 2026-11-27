import Mathlib
import Lightlike.TemperleyLieb.Crossing
import Lightlike.TemperleyLieb.Natural

/-!
# Crossings and cups in the Temperley–Lieb model

The model crossings `σ_m = a + a⁻¹ e_m` at `q = a²` (`crossA`) satisfy the Reidemeister moves with the cups of the
model: a crossing on a cup is the kink factor `-a⁻³` (`crossA_cup_self`, Reidemeister I), a strand crossing over both
legs of a cup slides it (`crossA_crossA_cup`, `crossA_crossA_cup'`, Reidemeister II), and a strand crossing a block
passes every cup in its path (`strandT_cup`). Crossings away from a cup commute with it after the index shift
(`crossA_cup_far`, `crossA_cup_near`, `strandT_cup_far`, `strandT_cup_near`). These are the steps of the twist
eigenvalue of a vertex (the braiding of the Crane–Yetter vertex).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- The model generators at `q = a²`, as a family. -/
noncomputable def eA (a : kˣ) : ℕ → Module.End k (ModelSpace k) := fun j => modelE (a ^ 2) j

/-- The model crossing `σ_m = a + a⁻¹ e_m` at `q = a²`. -/
noncomputable abbrev crossA (a : kˣ) (m : ℕ) : Module.End k (ModelSpace k) := cross (a : k) (eA a) m

lemma e_cup_self_smul (a : kˣ) (m : ℕ) :
    eA a m * cupOp (a ^ 2) m = (-((a : k) ^ 2 + (a : k)⁻¹ ^ 2)) • cupOp (a ^ 2) m := by
  unfold eA
  rw [e_mul_cup_self, ← Algebra.commutes, ← Algebra.smul_def, Units.val_pow_eq_pow_val]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
  ring

/-- **Reidemeister I**: a crossing on a cup is the kink factor, `σ_m cup_m = -a⁻³ cup_m`. -/
theorem crossA_cup_self (a : kˣ) (m : ℕ) : crossA a m * cupOp (a ^ 2) m = (-(a : k)⁻¹ ^ 3) • cupOp (a ^ 2) m := by
  unfold crossA cross
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, e_cup_self_smul, smul_smul, ← add_smul]
  congr 1
  have ha : (a : k) ≠ 0 := a.ne_zero
  field_simp
  ring

/-- **Reidemeister II for a cup**: a strand crossing over both legs of a cup slides it, `σ_m σ_{m+1} cup_m = cup_{m+1}`. -/
theorem crossA_crossA_cup (a : kˣ) (m : ℕ) :
    crossA a m * crossA a (m + 1) * cupOp (a ^ 2) m = cupOp (a ^ 2) (m + 1) := by
  have h1 : eA a (m + 1) * cupOp (a ^ 2) m = cupOp (a ^ 2) (m + 1) := e_mul_cup_succ _ m
  have h2 : eA a m * cupOp (a ^ 2) (m + 1) = cupOp (a ^ 2) m := e_mul_cup_pred _ m
  have h3 := e_cup_self_smul a m
  have ha : (a : k) ≠ 0 := a.ne_zero
  unfold crossA cross
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, h1, h2, h3, smul_add,
    smul_smul]
  match_scalars <;> field_simp <;> ring

/-- The mirror slide `σ_{m+1} σ_m cup_{m+1} = cup_m`. -/
theorem crossA_crossA_cup' (a : kˣ) (m : ℕ) :
    crossA a (m + 1) * crossA a m * cupOp (a ^ 2) (m + 1) = cupOp (a ^ 2) m := by
  have h1 : eA a (m + 1) * cupOp (a ^ 2) m = cupOp (a ^ 2) (m + 1) := e_mul_cup_succ _ m
  have h2 : eA a m * cupOp (a ^ 2) (m + 1) = cupOp (a ^ 2) m := e_mul_cup_pred _ m
  have h3 : eA a (m + 1) * cupOp (a ^ 2) (m + 1) = (-((a : k) ^ 2 + (a : k)⁻¹ ^ 2)) • cupOp (a ^ 2) (m + 1) :=
    e_cup_self_smul a (m + 1)
  have ha : (a : k) ≠ 0 := a.ne_zero
  unfold crossA cross
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, h1, h2, h3, smul_add,
    smul_smul]
  match_scalars <;> field_simp <;> ring

/-- `T(s, j + l) = T(s, j) T(s + j, l)`. -/
theorem strandT_add {A : Type*} [Ring A] [Algebra k A] (a : k) (e : ℕ → A) (s j : ℕ) :
    ∀ l, strandT a e s (j + l) = strandT a e s j * strandT a e (s + j) l
  | 0 => by simp [strandT]
  | l + 1 => by
    rw [← add_assoc, strandT, strandT_add a e s j l, strandT, mul_assoc, show s + (j + l) = s + j + l by omega]

/-- A model crossing beyond a cup moves past it: `σ_{l+2} cup_m = cup_m σ_l` for `m ≤ l`. -/
theorem crossA_cup_far (a : kˣ) {m l : ℕ} (h : m ≤ l) :
    crossA a (l + 2) * cupOp (a ^ 2) m = cupOp (a ^ 2) m * crossA a l := by
  unfold crossA cross eA
  rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul, mul_one,
    e_mul_cup_far _ h]

/-- A model crossing before a cup commutes with it: `σ_l cup_m = cup_m σ_l` for `l + 2 ≤ m`. -/
theorem crossA_cup_near (a : kˣ) {m l : ℕ} (h : l + 2 ≤ m) :
    crossA a l * cupOp (a ^ 2) m = cupOp (a ^ 2) m * crossA a l := by
  unfold crossA cross eA
  rw [add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm, one_mul, mul_one,
    e_mul_cup_near _ h]

/-- `T(t, n)` beyond a cup moves past it. -/
theorem strandT_cup_far (a : kˣ) {m t : ℕ} (h : m ≤ t) :
    ∀ n, strandT (a : k) (eA a) (t + 2) n * cupOp (a ^ 2) m = cupOp (a ^ 2) m * strandT (a : k) (eA a) t n
  | 0 => by simp [strandT]
  | n + 1 => by
    simp only [strandT]
    rw [mul_assoc, show t + 2 + n = t + n + 2 by omega, crossA_cup_far a (show m ≤ t + n by omega), ← mul_assoc,
      strandT_cup_far a h n, mul_assoc]

/-- `T(s, n)` before a cup commutes with it. -/
theorem strandT_cup_near (a : kˣ) {m s : ℕ} :
    ∀ n, s + n + 1 ≤ m → strandT (a : k) (eA a) s n * cupOp (a ^ 2) m = cupOp (a ^ 2) m * strandT (a : k) (eA a) s n
  | 0, _ => by simp [strandT]
  | n + 1, h => by
    simp only [strandT]
    rw [mul_assoc, crossA_cup_near a (show s + n + 2 ≤ m by omega), ← mul_assoc, strandT_cup_near a n (by omega),
      mul_assoc]

/-- **A strand crossing over a cup in its path** (Reidemeister II): `T(s, n + 2) cup_{s+j} = cup_{s+j+1} T(s, n)`
for `j ≤ n`. -/
theorem strandT_cup (a : kˣ) (s : ℕ) {j n : ℕ} (hj : j ≤ n) :
    strandT (a : k) (eA a) s (n + 2) * cupOp (a ^ 2) (s + j) =
      cupOp (a ^ 2) (s + j + 1) * strandT (a : k) (eA a) s n := by
  obtain ⟨l, rfl⟩ : ∃ l, n = j + l := ⟨n - j, by omega⟩
  rw [show j + l + 2 = j + 2 + l by omega, strandT_add, strandT_add (a : k) (eA a) s j 2, strandT_add (a : k) (eA a) s j l,
    mul_assoc, show s + (j + 2) = s + j + 2 by omega, strandT_cup_far a le_rfl l, ← mul_assoc, mul_assoc (strandT _ _ s j)]
  have h2 : strandT (a : k) (eA a) (s + j) 2 * cupOp (a ^ 2) (s + j) = cupOp (a ^ 2) (s + j + 1) := by
    simp only [strandT, one_mul]
    rw [show s + j + 0 = s + j by omega]
    exact crossA_crossA_cup a (s + j)
  rw [h2, ← mul_assoc, strandT_cup_near a j (by omega), mul_assoc]

end Lightlike.TemperleyLieb


