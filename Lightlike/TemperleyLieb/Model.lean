import Mathlib
import Lightlike.TemperleyLieb.Basic

/-!
# The model of the Temperley–Lieb algebra on the infinite tensor power of `k²`

`ModelSpace k = (ℕ → Bool) →₀ k`: a basis vector is a sequence of bits (the infinite tensor power of the
two-dimensional space with basis `0, 1`).  The generator `modelE q i` acts on the positions `i, i + 1`
by the matrix of `cup ∘ cap` with `cup 1 = |01⟩ - q |10⟩`, `cap |01⟩ = -q⁻¹`, `cap |10⟩ = 1`, that is
`|10⟩ ↦ |01⟩ - q |10⟩`, `|01⟩ ↦ |10⟩ - q⁻¹ |01⟩`, `|00⟩, |11⟩ ↦ 0`; the loop value is `δ = -q - q⁻¹`.
Since the operators are local, the Temperley–Lieb relations hold for every index (`modelE_isTL`), with no
length bookkeeping; the tensor powers of finite length are the subspaces of sequences constant below a bound.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable (k : Type*) [Field k]

/-- The model space: finitely supported combinations of bit sequences. -/
abbrev ModelSpace := (ℕ → Bool) →₀ k

variable {k}

/-- Set the bits at the positions `i` and `i + 1`. -/
def set2 (σ : ℕ → Bool) (i : ℕ) (x y : Bool) : ℕ → Bool :=
  Function.update (Function.update σ i x) (i + 1) y

/-- The action of `e_i` on a basis vector. -/
noncomputable def eBasis (q : kˣ) (i : ℕ) (σ : ℕ → Bool) : ModelSpace k :=
  match σ i, σ (i + 1) with
  | true, false => single (set2 σ i false true) 1 - (q : k) • single σ 1
  | false, true => single (set2 σ i true false) 1 - ((q⁻¹ : kˣ) : k) • single σ 1
  | _, _ => 0

/-- The generator `e_i` of the model. -/
noncomputable def modelE (q : kˣ) (i : ℕ) : Module.End k (ModelSpace k) :=
  Finsupp.lsum k (fun σ => LinearMap.toSpanSingleton k _ (eBasis q i σ))

/-- The action of `e_i` on a basis vector. -/
@[simp] lemma modelE_single (q : kˣ) (i : ℕ) (σ : ℕ → Bool) (c : k) :
    modelE q i (single σ c) = c • eBasis q i σ := by
  simp [modelE]

/-- Setting the bits to their current values changes nothing. -/
lemma set2_self (σ : ℕ → Bool) (i : ℕ) : set2 σ i (σ i) (σ (i + 1)) = σ := by
  funext n
  simp only [set2, Function.update_apply]
  split_ifs with h1 h2 <;> simp_all

/-- A second `set2` at the same position overrides the first. -/
lemma set2_set2 (σ : ℕ → Bool) (i : ℕ) (x y x' y' : Bool) :
    set2 (set2 σ i x y) i x' y' = set2 σ i x' y' := by
  funext n
  simp only [set2, Function.update_apply]
  split_ifs <;> simp_all

/-- `e_i² = δ e_i` on basis vectors. -/
lemma modelE_sq (q : kˣ) (i : ℕ) (σ : ℕ → Bool) :
    modelE q i (eBasis q i σ) = (-(q : k) - ((q⁻¹ : kˣ) : k)) • eBasis q i σ := by
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _
  · simp [eBasis, h0, h1]
  · -- σ = |01⟩ : e σ = |10⟩ - q⁻¹ |01⟩
    have a1 : (set2 σ i true false) i = true := by simp [set2]
    have a2 : (set2 σ i true false) (i + 1) = false := by simp [set2]
    have b : set2 (set2 σ i true false) i false true = σ := by
      rw [set2_set2, ← set2_self σ i, h0, h1, set2_set2]
    simp only [eBasis, h0, h1, map_sub, map_smul, modelE_single, a1, a2, b, one_smul]
    generalize (single σ (1 : k) : ModelSpace k) = A
    generalize (single (set2 σ i true false) (1 : k) : ModelSpace k) = B
    simp only [Units.val_inv_eq_inv_val]
    have hA : ((q : k) * (q : k)⁻¹) • A = A := by rw [mul_inv_cancel₀ q.ne_zero, one_smul]
    linear_combination (norm := module) (-1 : k) • hA
  · have a1 : (set2 σ i false true) i = false := by simp [set2]
    have a2 : (set2 σ i false true) (i + 1) = true := by simp [set2]
    have b : set2 (set2 σ i false true) i true false = σ := by
      rw [set2_set2, ← set2_self σ i, h0, h1, set2_set2]
    simp only [eBasis, h0, h1, map_sub, map_smul, modelE_single, a1, a2, b, one_smul]
    simp only [smul_sub, smul_smul]
    generalize (single σ (1 : k) : ModelSpace k) = A
    generalize (single (set2 σ i false true) (1 : k) : ModelSpace k) = B
    simp only [Units.val_inv_eq_inv_val]
    have hA : ((q : k) * (q : k)⁻¹) • A = A := by rw [mul_inv_cancel₀ q.ne_zero, one_smul]
    linear_combination (norm := module) (-1 : k) • hA
  · simp [eBasis, h0, h1]

/-- Set the bits at the positions `i, i+1, i+2`. -/
def trip (σ : ℕ → Bool) (i : ℕ) (a b c : Bool) : ℕ → Bool :=
  Function.update (Function.update (Function.update σ i a) (i + 1) b) (i + 2) c

/-- `set2` at `i` as a triple update. -/
lemma set2_eq_trip_zero (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    set2 σ i x y = trip σ i x y (σ (i + 2)) := by
  funext n
  simp only [set2, trip, Function.update_apply]
  split_ifs <;> simp_all

/-- `set2` at `i + 1` as a triple update. -/
lemma set2_eq_trip_succ (σ : ℕ → Bool) (i : ℕ) (x y : Bool) :
    set2 σ (i + 1) x y = trip σ i (σ i) x y := by
  funext n
  simp only [set2, trip, Function.update_apply]
  split_ifs <;> simp_all

/-- Bit `i` of a triple update. -/
@[simp] lemma trip_zero (σ : ℕ → Bool) (i : ℕ) (a b c : Bool) : trip σ i a b c i = a := by
  simp [trip]

/-- Bit `i + 1` of a triple update. -/
@[simp] lemma trip_one (σ : ℕ → Bool) (i : ℕ) (a b c : Bool) : trip σ i a b c (i + 1) = b := by
  simp [trip]

/-- Bit `i + 2` of a triple update. -/
@[simp] lemma trip_two (σ : ℕ → Bool) (i : ℕ) (a b c : Bool) : trip σ i a b c (i + 2) = c := by
  simp [trip]

/-- A triple update overrides an earlier one at the same position. -/
@[simp] lemma trip_trip (σ : ℕ → Bool) (i : ℕ) (a b c a' b' c' : Bool) :
    trip (trip σ i a b c) i a' b' c' = trip σ i a' b' c' := by
  funext n
  simp only [trip, Function.update_apply]
  split_ifs <;> simp_all

/-- Setting a triple to its current values changes nothing. -/
lemma trip_self (σ : ℕ → Bool) (i : ℕ) : trip σ i (σ i) (σ (i + 1)) (σ (i + 2)) = σ := by
  funext n
  simp only [trip, Function.update_apply]
  split_ifs <;> simp_all

/-- A triple update with the current values changes nothing. -/
lemma trip_eq_self {σ : ℕ → Bool} {i : ℕ} {a b c : Bool} (h0 : σ i = a) (h1 : σ (i + 1) = b)
    (h2 : σ (i + 2) = c) : trip σ i a b c = σ := by
  subst h0 h1 h2; exact trip_self σ i

/-- The braid relation `e_i e_{i+1} e_i = e_i` on basis vectors. -/
lemma modelE_braid_l (q : kˣ) (i : ℕ) (σ : ℕ → Bool) :
    modelE q i (modelE q (i + 1) (eBasis q i σ)) = eBasis q i σ := by
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  have z0 : ∀ (τ : ℕ → Bool) (x y : Bool), set2 τ i x y = trip τ i x y (τ (i + 2)) :=
    fun τ x y => set2_eq_trip_zero τ i x y
  have z1 : ∀ (τ : ℕ → Bool) (x y : Bool), set2 τ (i + 1) x y = trip τ i (τ i) x y :=
    fun τ x y => set2_eq_trip_succ τ i x y
  have e2 : i + 1 + 1 = i + 2 := rfl
  rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _ <;> rcases h2 : σ (i + 2) with _ | _
  all_goals
    simp only [eBasis, map_sub, map_smul, modelE_single, h0, h1, h2, z0, z1, e2,
      trip_zero, trip_one, trip_two, trip_trip, one_smul, smul_sub, smul_smul, map_zero, smul_zero,
      sub_zero, zero_sub, map_neg, neg_sub, trip_eq_self h0 h1 h2, trip_eq_self h0 h1 h2]
    try simp only [Units.val_inv_eq_inv_val, map_neg, map_sub, map_smul, modelE_single, z0, z1, e2, h0, h1, h2,
      trip_zero, trip_one, trip_two, trip_trip, one_smul, smul_sub, smul_smul, trip_eq_self h0 h1 h2,
      eBasis]
    try (have hu : (q : k) ≠ 0 := q.ne_zero
         match_scalars <;> field_simp)

/-- The braid relation `e_{i+1} e_i e_{i+1} = e_{i+1}` on basis vectors. -/
lemma modelE_braid_r (q : kˣ) (i : ℕ) (σ : ℕ → Bool) :
    modelE q (i + 1) (modelE q i (eBasis q (i + 1) σ)) = eBasis q (i + 1) σ := by
  have z0 : ∀ (τ : ℕ → Bool) (x y : Bool), set2 τ i x y = trip τ i x y (τ (i + 2)) :=
    fun τ x y => set2_eq_trip_zero τ i x y
  have z1 : ∀ (τ : ℕ → Bool) (x y : Bool), set2 τ (i + 1) x y = trip τ i (τ i) x y :=
    fun τ x y => set2_eq_trip_succ τ i x y
  have e2 : i + 1 + 1 = i + 2 := rfl
  rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _ <;> rcases h2 : σ (i + 2) with _ | _
  all_goals
    simp only [eBasis, map_sub, map_smul, modelE_single, h0, h1, h2, z0, z1, e2,
      trip_zero, trip_one, trip_two, trip_trip, one_smul, smul_sub, smul_smul, map_zero, smul_zero,
      sub_zero, zero_sub, map_neg, neg_sub, trip_eq_self h0 h1 h2]
    try simp only [Units.val_inv_eq_inv_val, map_neg, map_sub, map_smul, modelE_single, z0, z1, e2, h0, h1, h2,
      trip_zero, trip_one, trip_two, trip_trip, one_smul, smul_sub, smul_smul, trip_eq_self h0 h1 h2,
      eBasis]
    try (have hu : (q : k) ≠ 0 := q.ne_zero
         match_scalars <;> field_simp)

/-- `set2` at a later position does not change bit `i`. -/
lemma set2_lt_zero (σ : ℕ → Bool) {i j : ℕ} (h : i + 2 ≤ j) (x y : Bool) :
    set2 σ j x y i = σ i := by
  simp only [set2, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- `set2` at a later position does not change bit `i + 1`. -/
lemma set2_lt_one (σ : ℕ → Bool) {i j : ℕ} (h : i + 2 ≤ j) (x y : Bool) :
    set2 σ j x y (i + 1) = σ (i + 1) := by
  simp only [set2, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- `set2` at an earlier position does not change bit `j`. -/
lemma set2_gt_zero (σ : ℕ → Bool) {i j : ℕ} (h : i + 2 ≤ j) (x y : Bool) :
    set2 σ i x y j = σ j := by
  simp only [set2, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- `set2` at an earlier position does not change bit `j + 1`. -/
lemma set2_gt_one (σ : ℕ → Bool) {i j : ℕ} (h : i + 2 ≤ j) (x y : Bool) :
    set2 σ i x y (j + 1) = σ (j + 1) := by
  simp only [set2, Function.update_apply]
  split_ifs <;> first | rfl | omega

/-- `set2` at distant positions commutes. -/
lemma set2_comm (σ : ℕ → Bool) {i j : ℕ} (h : i + 2 ≤ j) (a b c d : Bool) :
    set2 (set2 σ j a b) i c d = set2 (set2 σ i c d) j a b := by
  funext n
  simp only [set2, Function.update_apply]
  split_ifs <;> simp_all <;> omega

/-- Distant generators commute, on basis vectors. -/
lemma modelE_comm (q : kˣ) {i j : ℕ} (h : i + 2 ≤ j) (σ : ℕ → Bool) :
    modelE q i (eBasis q j σ) = modelE q j (eBasis q i σ) := by
  rcases h0 : σ i with _ | _ <;> rcases h1 : σ (i + 1) with _ | _ <;>
    rcases h2 : σ j with _ | _ <;> rcases h3 : σ (j + 1) with _ | _
  all_goals
    simp only [eBasis, map_sub, map_smul, modelE_single, h0, h1, h2, h3, set2_lt_zero σ h,
      set2_lt_one σ h, set2_gt_zero σ h, set2_gt_one σ h, set2_comm σ h, one_smul, smul_sub, map_zero,
      smul_zero, sub_zero, smul_smul]
    try module

/-- Two linear maps out of the model space agree if they agree on basis vectors. -/
lemma model_ext {f g : Module.End k (ModelSpace k)}
    (h : ∀ σ : ℕ → Bool, f (single σ 1) = g (single σ 1)) : f = g := by
  refine Finsupp.lhom_ext fun σ c => ?_
  have : single σ c = c • single σ (1 : k) := by simp
  rw [this, map_smul, map_smul, h σ]

/-- **The Temperley–Lieb relations hold in the model**, with loop value `δ = -q - q⁻¹`. -/
theorem modelE_isTL (q : kˣ) : IsTL (-(q : k) - ((q⁻¹ : kˣ) : k)) (modelE q : ℕ → Module.End k (ModelSpace k)) where
  sq i := by
    refine model_ext fun σ => ?_
    simp only [Module.End.mul_apply, modelE_single, one_smul, modelE_sq, Module.algebraMap_end_apply]
  braid_l i := by
    refine model_ext fun σ => ?_
    simpa using modelE_braid_l q i σ
  braid_r i := by
    refine model_ext fun σ => ?_
    simpa using modelE_braid_r q i σ
  comm i j h := by
    refine model_ext fun σ => ?_
    simpa using modelE_comm q h σ

end Lightlike.TemperleyLieb
