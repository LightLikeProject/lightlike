import Mathlib
import Lightlike.TemperleyLieb.Model

/-!
# Cups and caps on the infinite tensor power

On `ModelSpace k` (finitely supported combinations of bit sequences) the operator `cupOp q i` inserts the
state `|01⟩ - q |10⟩` at the positions `i, i + 1` (shifting the later bits up by two), and `capOp q i`
contracts the positions `i, i + 1` with the functional `⟨01| ↦ -q⁻¹`, `⟨10| ↦ 1` (shifting the later bits down).
Then `cap_i ∘ cup_i = δ`, `cup_i ∘ cap_i = e_i` (`cup_cap`), and the zigzag relations hold
(`cap_cup_succ`, `cap_succ_cup`).  Together with the Jones–Wenzl projectors of `JonesWenzl.lean` these are the
morphisms of the Temperley–Lieb category, realized as operators on one space.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- Remove the bits at the positions `i` and `i + 1`, shifting the later bits down by two. -/
def removeTwo (σ : ℕ → Bool) (i : ℕ) : ℕ → Bool := fun n => if n < i then σ n else σ (n + 2)

/-- Insert the bits `x, y` at the positions `i` and `i + 1`, shifting the later bits up by two. -/
def insertTwo (σ : ℕ → Bool) (i : ℕ) (x y : Bool) : ℕ → Bool := fun n =>
  if n < i then σ n else if n = i then x else if n = i + 1 then y else σ (n - 2)

/-- Removing what was inserted. -/
lemma removeTwo_insertTwo (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    removeTwo (insertTwo σ i x y) i = σ := by
  funext n
  simp only [removeTwo, insertTwo]
  split_ifs <;> first | rfl | omega

/-- Inserting what was removed. -/
lemma insertTwo_removeTwo (σ : ℕ → Bool) (i : ℕ) :
    insertTwo (removeTwo σ i) i (σ i) (σ (i + 1)) = σ := by
  funext n
  simp only [removeTwo, insertTwo]
  split_ifs <;> first | rfl | (subst_vars; rfl) | (congr 1; omega) | omega

/-- The cap weights: `⟨01| ↦ -q⁻¹`, `⟨10| ↦ 1`. -/
def capWeight (q : kˣ) : Bool → Bool → k
  | false, true => -((q⁻¹ : kˣ) : k)
  | true, false => 1
  | _, _ => 0

/-- The cap at the positions `i, i + 1`, on basis vectors. -/
noncomputable def capBasis (q : kˣ) (i : ℕ) (σ : ℕ → Bool) : ModelSpace k :=
  single (removeTwo σ i) (capWeight q (σ i) (σ (i + 1)))

/-- The cup at the positions `i, i + 1`, on basis vectors. -/
noncomputable def cupBasis (q : kˣ) (i : ℕ) (σ : ℕ → Bool) : ModelSpace k :=
  single (insertTwo σ i false true) 1 - (q : k) • single (insertTwo σ i true false) 1

/-- The cap operator. -/
noncomputable def capOp (q : kˣ) (i : ℕ) : Module.End k (ModelSpace k) :=
  Finsupp.lsum k (fun σ => LinearMap.toSpanSingleton k _ (capBasis q i σ))

/-- The cup operator. -/
noncomputable def cupOp (q : kˣ) (i : ℕ) : Module.End k (ModelSpace k) :=
  Finsupp.lsum k (fun σ => LinearMap.toSpanSingleton k _ (cupBasis q i σ))

/-- The cap on a basis vector. -/
@[simp] lemma capOp_single (q : kˣ) (i : ℕ) (σ : ℕ → Bool) (c : k) :
    capOp q i (single σ c) = c • capBasis q i σ := by
  simp [capOp]

/-- The cup on a basis vector. -/
@[simp] lemma cupOp_single (q : kˣ) (i : ℕ) (σ : ℕ → Bool) (c : k) :
    cupOp q i (single σ c) = c • cupBasis q i σ := by
  simp [cupOp]

/-- Inserting at the position of the removed bits is `set2`. -/
lemma insertTwo_removeTwo_eq_set2 (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    insertTwo (removeTwo σ i) i x y = set2 σ i x y := by
  funext n
  simp only [removeTwo, insertTwo, set2, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- First zigzag: removing at `i` what was inserted at `i + 1`. -/
lemma removeTwo_insertTwo_succ (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    removeTwo (insertTwo σ (i + 1) x y) i = Function.update σ i y := by
  funext n
  simp only [removeTwo, insertTwo, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- Second zigzag: removing at `i + 1` what was inserted at `i`. -/
lemma removeTwo_succ_insertTwo (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    removeTwo (insertTwo σ i x y) (i + 1) = Function.update σ i x := by
  funext n
  simp only [removeTwo, insertTwo, Function.update_apply]
  split_ifs <;> first | rfl | omega | (congr 1; omega)

/-- **Loop value**: `cap_i ∘ cup_i = δ`. -/
theorem cap_cup (q : kˣ) (i : ℕ) :
    capOp q i * cupOp q i = algebraMap k _ (-(q : k) - ((q⁻¹ : kˣ) : k)) := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, cupOp_single, one_smul, cupBasis, map_sub, map_smul, capOp_single,
    capBasis, removeTwo_insertTwo, capWeight, insertTwo]
  simp
  module

/-- **`e_i = cup_i ∘ cap_i`**. -/
theorem cup_cap (q : kˣ) (i : ℕ) : cupOp q i * capOp q i = modelE q i := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, capOp_single, one_smul, capBasis, cupOp_single, cupBasis,
    insertTwo_removeTwo_eq_set2, modelE_single, eBasis]
  rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _
  · simp [capWeight]
  · have e0 : set2 σ i false true = σ := by rw [← h0, ← h1]; exact set2_self σ i
    simp only [capWeight, e0, Units.val_inv_eq_inv_val]
    simp only [smul_sub, smul_smul]
    have hu : (q : k) ≠ 0 := q.ne_zero
    match_scalars <;> field_simp
  · have e0 : set2 σ i true false = σ := by rw [← h0, ← h1]; exact set2_self σ i
    simp only [capWeight, e0]
    simp only [smul_sub, smul_smul]
    match_scalars <;> simp
  · simp [capWeight]

/-- **Zigzag**: `cap_i ∘ cup_{i+1} = 1`. -/
theorem cap_cup_succ (q : kˣ) (i : ℕ) : capOp q i * cupOp q (i + 1) = 1 := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, cupOp_single, one_smul, cupBasis, map_sub, map_smul, capOp_single,
    capBasis, removeTwo_insertTwo_succ, Module.End.one_apply]
  have b0 : insertTwo σ (i + 1) false true i = σ i := by simp [insertTwo]
  have b0' : insertTwo σ (i + 1) true false i = σ i := by simp [insertTwo]
  have b1 : insertTwo σ (i + 1) false true (i + 1) = false := by simp [insertTwo]
  have b1' : insertTwo σ (i + 1) true false (i + 1) = true := by simp [insertTwo]
  rw [b0, b0', b1, b1']
  rcases h0 : σ i with _ | _
  · have : Function.update σ i false = σ := by rw [← h0]; exact Function.update_eq_self i σ
    simp [capWeight, this]
  · have : Function.update σ i true = σ := by rw [← h0]; exact Function.update_eq_self i σ
    simp [capWeight, this]

/-- **Zigzag**: `cap_{i+1} ∘ cup_i = 1`. -/
theorem cap_succ_cup (q : kˣ) (i : ℕ) : capOp q (i + 1) * cupOp q i = 1 := by
  refine model_ext fun σ => ?_
  simp only [Module.End.mul_apply, cupOp_single, one_smul, cupBasis, map_sub, map_smul, capOp_single,
    capBasis, removeTwo_succ_insertTwo, Module.End.one_apply]
  have b1 : insertTwo σ i false true (i + 1) = true := by simp [insertTwo]
  have b1' : insertTwo σ i true false (i + 1) = false := by simp [insertTwo]
  have b2 : insertTwo σ i false true (i + 1 + 1) = σ i := by
    unfold insertTwo
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  have b2' : insertTwo σ i true false (i + 1 + 1) = σ i := by
    unfold insertTwo
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  rw [b1, b1', b2, b2']
  rcases h0 : σ i with _ | _
  · have : Function.update σ i false = σ := by rw [← h0]; exact Function.update_eq_self i σ
    simp [capWeight, this]
  · have : Function.update σ i true = σ := by rw [← h0]; exact Function.update_eq_self i σ
    simp [capWeight, this]

end Lightlike.TemperleyLieb
