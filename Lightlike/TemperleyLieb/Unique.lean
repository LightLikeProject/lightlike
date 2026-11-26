import Mathlib
import Lightlike.TemperleyLieb.JonesWenzl

/-!
# Uniqueness of the Jones–Wenzl projector

For any family `f` (not necessarily Temperley–Lieb), `jw δ f m` is built from `1` by the recursion of
`JonesWenzl.lean`.  Three elementary facts follow by induction on `m`:
* `jw_mul_of_kill`: if `e j * Y = 0` for `j + 1 < m` then `jw δ e m * Y = Y`;
* `mul_jw_of_kill`: if `Y * e j = 0` for `j + 1 < m` then `Y * jw δ e m = Y`;
* `mul_jw_self`: if `P * f j = 0` for `j + 1 < m` then `P * jw δ f m = P` (and the mirror).
Hence two projectors on the same strands, each killed by the generators of the other, coincide
(`jw_unique`).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A] {δ : k}

/-- If `Y` is killed on the left by `e_j` for `j + 1 < m`, then `jw m` acts as the identity on `Y`. -/
theorem jw_mul_of_kill (e : ℕ → A) (m : ℕ) (Y : A) (h : ∀ j, j + 1 < m → e j * Y = 0) :
    jw δ e m * Y = Y := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [jw_zero]
    · simp [jw_one]
    · rw [jw_succ_succ, sub_mul, smul_mul_assoc, mul_assoc, mul_assoc, ih (m + 1) (by omega)
        (fun j hj => h j (by omega)), h m (by omega)]
      simp

/-- If `Y` is killed on the right by `e_j` for `j + 1 < m`, then `jw m` acts as the identity on `Y`. -/
theorem mul_jw_of_kill (e : ℕ → A) (m : ℕ) (Y : A) (h : ∀ j, j + 1 < m → Y * e j = 0) :
    Y * jw δ e m = Y := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | m
    · simp [jw_zero]
    · simp [jw_one]
    · rw [jw_succ_succ, mul_sub, mul_smul_comm, ← mul_assoc, ← mul_assoc,
        ih (m + 1) (by omega) (fun j hj => h j (by omega)), h m (by omega)]
      simp

/-- If `P` is killed on the right by the generators `f_j`, `j + 1 < m`, then `P · jw f m = P`. -/
theorem mul_jw_self (f : ℕ → A) (m : ℕ) (P : A) (h : ∀ j, j + 1 < m → P * f j = 0) :
    P * jw δ f m = P := mul_jw_of_kill f m P h

/-- If `P` is killed on the left by the generators `f_j`, `j + 1 < m`, then `jw f m · P = P`. -/
theorem jw_mul_self (f : ℕ → A) (m : ℕ) (P : A) (h : ∀ j, j + 1 < m → f j * P = 0) :
    jw δ f m * P = P := jw_mul_of_kill f m P h

/-- **Uniqueness.** Let `P = jw δ e m` and `Y = jw δ f m` for two families.  If `P` is killed on the right by
every `f_j` and `Y` is killed on the left by every `e_j` (`j + 1 < m`), then `P = Y`. -/
theorem jw_unique (e f : ℕ → A) (m : ℕ) (h1 : ∀ j, j + 1 < m → jw δ e m * f j = 0)
    (h2 : ∀ j, j + 1 < m → e j * jw δ f m = 0) : jw δ e m = jw δ f m := by
  have a := mul_jw_self (δ := δ) f m (jw δ e m) h1
  have b := jw_mul_of_kill (δ := δ) e m (jw δ f m) h2
  rw [← a, b]

end Lightlike.TemperleyLieb
