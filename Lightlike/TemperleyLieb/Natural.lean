import Mathlib
import Lightlike.TemperleyLieb.CupCap

/-!
# Naturality of cups and caps against the generators

For the operators `capOp q m` and `cupOp q m` of `CupCap.lean`: the generators `e j` far from the junction slide
through (`cap_mul_e_far`, ...), and the three generators next to the junction are absorbed using the zigzag
relations (`cap_mul_e_pred`, `cap_mul_e_self`, `cap_mul_e_succ`, and the same for cups).
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- `cap_m e_{m-1} = cap_{m-1}`. -/
theorem cap_mul_e_pred (q : kˣ) (m : ℕ) : capOp q (m + 1) * modelE q m = capOp q m := by
  rw [← cup_cap, ← mul_assoc, cap_succ_cup, one_mul]

/-- `cap_m e_m = δ cap_m`. -/
theorem cap_mul_e_self (q : kˣ) (m : ℕ) :
    capOp q m * modelE q m = algebraMap k _ (-(q : k) - ((q⁻¹ : kˣ) : k)) * capOp q m := by
  rw [← cup_cap, ← mul_assoc, cap_cup]

/-- `cap_m e_{m+1} = cap_{m+1}`. -/
theorem cap_mul_e_succ (q : kˣ) (m : ℕ) : capOp q m * modelE q (m + 1) = capOp q (m + 1) := by
  rw [← cup_cap, ← mul_assoc, cap_cup_succ, one_mul]

/-- `e_{m} cup_{m+1} = cup_m`. -/
theorem e_mul_cup_pred (q : kˣ) (m : ℕ) : modelE q m * cupOp q (m + 1) = cupOp q m := by
  rw [← cup_cap, mul_assoc, cap_cup_succ, mul_one]

/-- `e_m cup_m = δ cup_m`. -/
theorem e_mul_cup_self (q : kˣ) (m : ℕ) :
    modelE q m * cupOp q m = cupOp q m * algebraMap k _ (-(q : k) - ((q⁻¹ : kˣ) : k)) := by
  rw [← cup_cap, mul_assoc, cap_cup]

/-- `e_{m+1} cup_m = cup_{m+1}`. -/
theorem e_mul_cup_succ (q : kˣ) (m : ℕ) : modelE q (m + 1) * cupOp q m = cupOp q (m + 1) := by
  rw [← cup_cap, mul_assoc, cap_succ_cup, mul_one]

/-- Removing two bits commutes with setting bits further to the right (shifted by two). -/
lemma removeTwo_set2_far (σ : ℕ → Bool) {m j : ℕ} (h : m + 2 ≤ j) (x y : Bool) :
    removeTwo (set2 σ j x y) m = set2 (removeTwo σ m) (j - 2) x y := by
  funext n
  simp only [removeTwo, set2, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all <;> omega

/-- Removing two bits commutes with setting bits further to the left. -/
lemma removeTwo_set2_near (σ : ℕ → Bool) {m j : ℕ} (h : j + 2 ≤ m) (x y : Bool) :
    removeTwo (set2 σ j x y) m = set2 (removeTwo σ m) j x y := by
  funext n
  simp only [removeTwo, set2, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all <;> omega

/-- Bits to the right of the removed pair shift down by two. -/
lemma removeTwo_apply_ge (σ : ℕ → Bool) {m n : ℕ} (h : m ≤ n) : removeTwo σ m n = σ (n + 2) := by
  simp only [removeTwo]; split_ifs <;> first | rfl | omega

/-- Bits to the left of the removed pair stay. -/
lemma removeTwo_apply_lt (σ : ℕ → Bool) {m n : ℕ} (h : n < m) : removeTwo σ m n = σ n := by
  simp only [removeTwo]; split_ifs <;> first | rfl | omega

/-- `set2` leaves other positions alone. -/
lemma set2_ne (σ : ℕ → Bool) {j n : ℕ} (h0 : n ≠ j) (h1 : n ≠ j + 1) (x y : Bool) :
    set2 σ j x y n = σ n := by
  simp [set2, Function.update_apply, h0, h1]

/-- A generator to the right of the cap slides through, shifting by two. -/
theorem cap_mul_e_far (q : kˣ) {m j : ℕ} (h : m ≤ j) :
    capOp q m * modelE q (j + 2) = modelE q j * capOp q m := by
  refine model_ext fun σ => ?_
  have b0 : removeTwo σ m j = σ (j + 2) := removeTwo_apply_ge σ h
  have b1 : removeTwo σ m (j + 1) = σ (j + 3) := removeTwo_apply_ge σ (by omega)
  have s0 : ∀ x y, set2 σ (j + 2) x y m = σ m := fun x y => set2_ne σ (by omega) (by omega) x y
  have s1 : ∀ x y, set2 σ (j + 2) x y (m + 1) = σ (m + 1) := fun x y =>
    set2_ne σ (by omega) (by omega) x y
  have r : ∀ x y, removeTwo (set2 σ (j + 2) x y) m = set2 (removeTwo σ m) j x y := fun x y => by
    have := removeTwo_set2_far σ (m := m) (j := j + 2) (by omega) x y
    simpa using this
  rcases h2 : σ (j + 2) with _ | _ <;> rcases h3 : σ (j + 3) with _ | _
  all_goals
    simp only [Module.End.mul_apply, modelE_single, one_smul, eBasis, h2, h3, b0, b1, map_sub, map_smul,
      capOp_single, capBasis, s0, s1, r, map_zero, smul_zero, sub_zero, smul_sub, smul_smul]
    try (simp only [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul]
         try (rw [mul_comm]))

/-- Bits to the right of the inserted pair shift up by two. -/
lemma insertTwo_apply_ge (σ : ℕ → Bool) (m : ℕ) (x y : Bool) {n : ℕ} (h : m ≤ n) :
    insertTwo σ m x y (n + 2) = σ n := by
  simp only [insertTwo]; split_ifs <;> first | rfl | omega | (congr 1)

/-- Bits to the left of the inserted pair stay. -/
lemma insertTwo_apply_lt (σ : ℕ → Bool) (m : ℕ) (x y : Bool) {n : ℕ} (h : n < m) :
    insertTwo σ m x y n = σ n := by
  simp only [insertTwo]; split_ifs <;> first | rfl | omega

/-- Inserting a pair commutes with setting bits further to the right (shifted by two). -/
lemma insertTwo_set2_far (σ : ℕ → Bool) {m j : ℕ} (h : m ≤ j) (a b x y : Bool) :
    insertTwo (set2 σ j a b) m x y = set2 (insertTwo σ m x y) (j + 2) a b := by
  funext n
  simp only [insertTwo, set2, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all <;> omega

/-- A generator to the right of the cup slides through, shifting by two. -/
theorem e_mul_cup_far (q : kˣ) {m j : ℕ} (h : m ≤ j) :
    modelE q (j + 2) * cupOp q m = cupOp q m * modelE q j := by
  refine model_ext fun σ => ?_
  have b0 : ∀ x y, insertTwo σ m x y (j + 2) = σ j := fun x y => insertTwo_apply_ge σ m x y h
  have b1 : ∀ x y, insertTwo σ m x y (j + 3) = σ (j + 1) := fun x y =>
    insertTwo_apply_ge σ m x y (n := j + 1) (by omega)
  have r : ∀ a b x y, insertTwo (set2 σ j a b) m x y = set2 (insertTwo σ m x y) (j + 2) a b :=
    fun a b x y => insertTwo_set2_far σ h a b x y
  rcases h2 : σ j with _ | _ <;> rcases h3 : σ (j + 1) with _ | _
  all_goals
    simp only [Module.End.mul_apply, modelE_single, one_smul, eBasis, h2, h3, b0, b1, map_sub, map_smul,
      cupOp_single, cupBasis, r, map_zero, smul_zero, sub_zero, smul_sub, smul_smul]
    try (simp only [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul])
    try (simp only [mul_comm])
    try abel

/-- A generator to the left of the cap commutes with it. -/
theorem cap_mul_e_near (q : kˣ) {m j : ℕ} (h : j + 2 ≤ m) :
    capOp q m * modelE q j = modelE q j * capOp q m := by
  refine model_ext fun σ => ?_
  have b0 : removeTwo σ m j = σ j := removeTwo_apply_lt σ (by omega)
  have b1 : removeTwo σ m (j + 1) = σ (j + 1) := removeTwo_apply_lt σ (by omega)
  have s0 : ∀ x y, set2 σ j x y m = σ m := fun x y => set2_ne σ (by omega) (by omega) x y
  have s1 : ∀ x y, set2 σ j x y (m + 1) = σ (m + 1) := fun x y =>
    set2_ne σ (by omega) (by omega) x y
  have r : ∀ x y, removeTwo (set2 σ j x y) m = set2 (removeTwo σ m) j x y := fun x y =>
    removeTwo_set2_near σ h x y
  rcases h2 : σ j with _ | _ <;> rcases h3 : σ (j + 1) with _ | _
  all_goals
    simp only [Module.End.mul_apply, modelE_single, one_smul, eBasis, h2, h3, b0, b1, map_sub, map_smul,
      capOp_single, capBasis, s0, s1, r, map_zero, smul_zero, sub_zero, smul_sub, smul_smul]
    try (simp only [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul])
    try (simp only [mul_comm])
    try abel

/-- Inserting a pair commutes with setting bits further to the left. -/
lemma insertTwo_set2_near (σ : ℕ → Bool) {m j : ℕ} (h : j + 2 ≤ m) (a b x y : Bool) :
    insertTwo (set2 σ j a b) m x y = set2 (insertTwo σ m x y) j a b := by
  funext n
  simp only [insertTwo, set2, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega) | simp_all <;> omega

/-- A generator to the left of the cup commutes with it. -/
theorem e_mul_cup_near (q : kˣ) {m j : ℕ} (h : j + 2 ≤ m) :
    modelE q j * cupOp q m = cupOp q m * modelE q j := by
  refine model_ext fun σ => ?_
  have b0 : ∀ x y, insertTwo σ m x y j = σ j := fun x y => insertTwo_apply_lt σ m x y (by omega)
  have b1 : ∀ x y, insertTwo σ m x y (j + 1) = σ (j + 1) := fun x y =>
    insertTwo_apply_lt σ m x y (by omega)
  have r : ∀ a b x y, insertTwo (set2 σ j a b) m x y = set2 (insertTwo σ m x y) j a b :=
    fun a b x y => insertTwo_set2_near σ h a b x y
  rcases h2 : σ j with _ | _ <;> rcases h3 : σ (j + 1) with _ | _
  all_goals
    simp only [Module.End.mul_apply, modelE_single, one_smul, eBasis, h2, h3, b0, b1, map_sub, map_smul,
      cupOp_single, cupBasis, r, map_zero, smul_zero, sub_zero, smul_sub, smul_smul]
    try (simp only [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul])
    try (simp only [mul_comm])
    try abel

end Lightlike.TemperleyLieb
