import Mathlib
import Lightlike.TemperleyLieb.CupCap

/-!
# The vertical flip: the basis pairing of the model

`pairB x y = Σ_σ x_σ y_σ` is the symmetric bilinear form of the basis of words. For it the cap and the cup at the
same positions are adjoint up to the scalar `-q⁻¹` (`pairB_capOp`), so the generators `modelE = cup cap` are
self-adjoint. This is the vertical flip of the diagrams; it relates the pairings `U_L' U_R` and `U_R' U_L` of the
tree vectors.
-/

namespace Lightlike.TemperleyLieb

open Finsupp
open scoped Classical

variable {k : Type*} [Field k]

/-- The basis pairing `pairB x y = Σ_σ x_σ y_σ`. -/
noncomputable def pairB (x y : ModelSpace k) : k := x.sum fun σ c => c * y σ

lemma pairB_single_left (σ : ℕ → Bool) (c : k) (y : ModelSpace k) : pairB (single σ c) y = c * y σ := by
  simp [pairB]

lemma pairB_add_left (x x' y : ModelSpace k) : pairB (x + x') y = pairB x y + pairB x' y := by
  unfold pairB; rw [sum_add_index'] <;> intros <;> ring

lemma pairB_smul_left (c : k) (x y : ModelSpace k) : pairB (c • x) y = c * pairB x y := by
  unfold pairB; rw [sum_smul_index'] <;> intros
  · rw [Finsupp.mul_sum]; refine Finsupp.sum_congr fun _ _ => by ring
  · ring

lemma pairB_zero_left (y : ModelSpace k) : pairB 0 y = 0 := by simp [pairB]

lemma pairB_add_right (x y y' : ModelSpace k) : pairB x (y + y') = pairB x y + pairB x y' := by
  unfold pairB; simp only [Finsupp.add_apply, mul_add, Finsupp.sum_add]

lemma pairB_smul_right (c : k) (x y : ModelSpace k) : pairB x (c • y) = c * pairB x y := by
  unfold pairB; simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun _ _ => by ring

lemma pairB_comm (x y : ModelSpace k) : pairB x y = pairB y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp [pairB]
  | add x x' hx hx' => rw [pairB_add_left, hx, hx', pairB_add_right]
  | single σ c =>
    rw [pairB_single_left]
    induction y using Finsupp.induction_linear with
    | zero => simp [pairB]
    | add y y' hy hy' => rw [Finsupp.add_apply, mul_add, hy, hy', pairB_add_left]
    | single τ d =>
      rw [pairB_single_left, single_apply, single_apply]
      by_cases h : τ = σ
      · subst h; simp; ring
      · simp [h, Ne.symm h]

lemma insertTwo_eq_iff (τ σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    insertTwo τ i x y = σ ↔ removeTwo σ i = τ ∧ σ i = x ∧ σ (i + 1) = y := by
  constructor
  · rintro rfl
    refine ⟨removeTwo_insertTwo τ i x y, ?_, ?_⟩ <;> simp [insertTwo]
  · rintro ⟨h1, h2, h3⟩
    rw [← h1, ← h2, ← h3]; exact insertTwo_removeTwo σ i

/-- **The cap and the cup are adjoint** for the basis pairing, up to `-q⁻¹`. -/
theorem pairB_capOp (q : kˣ) (i : ℕ) (x y : ModelSpace k) :
    pairB (capOp q i x) y = -((q⁻¹ : kˣ) : k) * pairB x (cupOp q i y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp [pairB_zero_left]
  | add x x' hx hx' => rw [map_add, pairB_add_left, hx, hx', pairB_add_left]; ring
  | single σ c =>
    rw [capOp_single, pairB_smul_left, pairB_single_left]
    induction y using Finsupp.induction_linear with
    | zero => simp [capBasis, pairB]
    | add y y' hy hy' =>
      rw [map_add, Finsupp.add_apply, mul_add, mul_add, ← hy, ← hy', pairB_add_right, mul_add]
    | single τ d =>
      rw [cupOp_single, cupBasis]
      unfold capBasis
      rw [pairB_single_left]
      simp only [Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, single_apply]
      have e1 := insertTwo_eq_iff τ σ i false true
      have e2 := insertTwo_eq_iff τ σ i true false
      have hq0 : (q : k) ≠ 0 := q.ne_zero
      by_cases hr : removeTwo σ i = τ
      · subst hr
        rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _ <;>
          simp [capWeight, e1, e2, h0, h1, Units.val_inv_eq_inv_val] <;> field_simp <;> ring
      · have n1 : ¬ insertTwo τ i false true = σ := fun h => hr (e1.mp h).1
        have n2 : ¬ insertTwo τ i true false = σ := fun h => hr (e2.mp h).1
        simp [hr, Ne.symm hr, n1, n2]

end Lightlike.TemperleyLieb
