import Mathlib
import Lightlike.TemperleyLieb.CupCap
import Lightlike.TemperleyLieb.Vertex
import Lightlike.TemperleyLieb.Reduction

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

/-- The cup is adjoint to the cap, up to `-q`. -/
theorem pairB_cupOp (q : kˣ) (i : ℕ) (x y : ModelSpace k) :
    pairB (cupOp q i x) y = -(q : k) * pairB x (capOp q i y) := by
  have h := pairB_capOp q i y x
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  rw [pairB_comm (cupOp q i x), pairB_comm x, h]
  linear_combination (-(pairB y (cupOp q i x))) * hq

/-- A self-adjoint operator for the basis pairing. -/
def IsSelfAdj (T : Module.End k (ModelSpace k)) : Prop := ∀ x y, pairB (T x) y = pairB x (T y)

lemma IsSelfAdj.one : IsSelfAdj (1 : Module.End k (ModelSpace k)) := fun _ _ => rfl

lemma IsSelfAdj.sub {S T : Module.End k (ModelSpace k)} (hS : IsSelfAdj S) (hT : IsSelfAdj T) :
    IsSelfAdj (S - T) := by
  intro x y
  have hneg : ∀ z : ModelSpace k, -z = (-1 : k) • z := fun z => by simp
  simp only [LinearMap.sub_apply, sub_eq_add_neg, hneg, pairB_add_left, pairB_add_right, pairB_smul_left,
    pairB_smul_right, hS x y, hT x y]

lemma IsSelfAdj.smul {T : Module.End k (ModelSpace k)} (c : k) (hT : IsSelfAdj T) : IsSelfAdj (c • T) := by
  intro x y; simp only [LinearMap.smul_apply, pairB_smul_left, pairB_smul_right, hT x y]

lemma IsSelfAdj.sandwich {A B : Module.End k (ModelSpace k)} (hA : IsSelfAdj A) (hB : IsSelfAdj B) :
    IsSelfAdj (A * B * A) := by
  intro x y; simp only [Module.End.mul_apply]; rw [hA, hB, hA]

lemma IsSelfAdj.mul_comm {A B : Module.End k (ModelSpace k)} (hA : IsSelfAdj A) (hB : IsSelfAdj B)
    (h : A * B = B * A) : IsSelfAdj (A * B) := by
  intro x y
  simp only [Module.End.mul_apply]
  rw [hA, hB]
  have := congrArg (fun T : Module.End k (ModelSpace k) => T y) h
  simp only [Module.End.mul_apply] at this
  rw [this]

/-- The generators are self-adjoint. -/
theorem isSelfAdj_modelE (q : kˣ) (j : ℕ) : IsSelfAdj (modelE q j : Module.End k (ModelSpace k)) := by
  intro x y
  rw [← cup_cap]
  simp only [Module.End.mul_apply]
  rw [pairB_cupOp, pairB_capOp]
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination (pairB x (cupOp q j (capOp q j y))) * hq

/-- The Jones–Wenzl projectors are self-adjoint. -/
theorem isSelfAdj_jwAt (q : kˣ) (s : ℕ) : ∀ n, IsSelfAdj (jwAt q s n : Module.End k (ModelSpace k))
  | 0 => by simpa [jwAt, jw_zero] using IsSelfAdj.one
  | 1 => by simpa [jwAt, jw_one] using IsSelfAdj.one
  | n + 2 => by
    unfold jwAt
    rw [jw_succ_succ]
    exact (isSelfAdj_jwAt q s (n + 1)).sub (((isSelfAdj_jwAt q s (n + 1)).sandwich (isSelfAdj_modelE q _)).smul _)

/-- Nested cups are adjoint to nested caps, up to `(-q)^i`. -/
theorem pairB_nestCup (q : kˣ) (l : ℕ) : ∀ i (x y : ModelSpace k),
    pairB (nestCup q l i x) y = (-(q : k)) ^ i * pairB x (nestCap q l i y)
  | 0, x, y => by simp [nestCup, nestCap]
  | i + 1, x, y => by
    simp only [nestCup, nestCap, Module.End.mul_apply]
    rw [pairB_cupOp, pairB_nestCup q l i, pow_succ]; ring

end Lightlike.TemperleyLieb
