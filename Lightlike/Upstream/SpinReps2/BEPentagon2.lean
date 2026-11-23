module

public import Lightlike.Upstream.SpinReps2.BEPentagon

/-!
# The recoupling pentagon, part 2: orthonormality and the pentagon for recoupling coefficients

Second half of the proof of the Biedenharn–Elliott identity for Physlib's 6j symbol `sixJSym`
(first half: `Lightlike.Upstream.SpinReps2.BEPentagon`).

## Implementation notes

`quadForm` is the contravariant form on `V(a) ⊗ V(b) ⊗ V(c) ⊗ V(d)`. The `((12)3)4` states `T1`
are orthonormal for it (`quadForm_T1_T1`). Pairing `T1` with `T3 = 1(2(34))` is computed twice:
through two recoupling moves (`quadForm_T1_T3_two`, via `(12)(34)`) and through three
(`quadForm_T1_T3_three`, via `1((23)4)` and `(1(23))4`). Equating the two results gives the
pentagon identity for the proof-free recoupling coefficient `rc`.

## Main results

* `PhyslibAlpha.Sl2.Pentagon.quadForm_T1_T1`: orthonormality of the `((12)3)4` states.
* `PhyslibAlpha.Sl2.Pentagon.pentagon_rc`: the pentagon identity for recoupling coefficients.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset
open scoped TensorProduct

namespace PhyslibAlpha.Sl2.Pentagon

variable {a b c d : ℕ}

variable (a b c d) in
/-- The contravariant form on the four-fold product. -/
noncomputable def quadForm : LinearMap.BilinForm ℝ (Quad a b c d) :=
  LinearMap.BilinForm.tmul (tripleForm a b c) (invForm ℝ d)

lemma quadForm_tmul (x x' : Triple a b c) (y y' : StandardSl2Module ℝ d) :
    quadForm a b c d (x ⊗ₜ y) (x' ⊗ₜ y') = tripleForm a b c x x' * invForm ℝ d y y' := by
  rw [quadForm, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, mul_comm]

/-- The first-scheme states of a triple product are orthonormal (ℕ-indexed form of Physlib's
`tripleForm_vecA`). -/
lemma tripleForm_stateA_stateA (hab : 0 < a + b) (hc : 0 < c) {k₁ k₁' : Fin (min a b + 1)}
    {k₂ k₂' l l' : ℕ} (h₂ : k₂ ≤ a + b - 2 * (k₁ : ℕ)) (h₂' : k₂ ≤ c)
    (h₃ : k₂' ≤ a + b - 2 * (k₁' : ℕ)) (h₃' : k₂' ≤ c) (hl : l ≤ a + b - 2 * (k₁ : ℕ) + c - 2 * k₂) :
    tripleForm a b c (stateA hab k₁ k₂ l) (stateA hab k₁' k₂' l') =
      if k₁ = k₁' ∧ k₂ = k₂' ∧ l = l' then 1 else 0 := by
  by_cases hk : k₁ = k₁'
  · subst hk
    rw [stateA, stateA, tripleForm_rTensor_embed,
      tensorForm_coupledVec (by omega) h₂ h₂' h₃ h₃' hl]
    simp only [true_and]
  · rw [stateA, stateA, tripleForm_rTensor_embed_of_ne hab _ hk, ite_eq_right (fun h => hk h.1)]

/-- Pairing a `((12)3)4` state with a product basis vector `stateA ⊗ u_δ'` picks out one
Clebsch–Gordan coefficient. -/
lemma quadForm_T1_tmul (hab : 0 < a + b) (hc : 0 < c) {k₁₂ k₁₂' : Fin (min a b + 1)}
    {k₁₂₃ k₁₂₃' k₄ L l' δ' : ℕ}
    (h₁ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ)) (h₁' : k₁₂₃ ≤ c)
    (h₂ : k₁₂₃' ≤ a + b - 2 * (k₁₂' : ℕ)) (h₂' : k₁₂₃' ≤ c)
    (hl' : l' ≤ a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') (hδ' : δ' ≤ d) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (stateA hab k₁₂' k₁₂₃' l' ⊗ₜ normVec d δ') =
      if k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃' then
        cgCoefficient (a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃) d k₄ L l' δ' else 0 := by
  rw [T1, liftR, map_sum, LinearMap.sum_apply]
  simp_rw [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    quadForm_tmul]
  by_cases hk : k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃'
  · obtain ⟨rfl, rfl⟩ := hk
    rw [ite_eq_left ⟨rfl, rfl⟩, sum_eq_single l', sum_eq_single δ']
    · rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₁ h₁' hl', invForm_normVec hδ' hδ']
      simp
    · intro δ hδ hne
      rw [invForm_normVec (by simp only [mem_range] at hδ; omega) hδ', ite_eq_right hne]
      ring
    · intro h; simp only [mem_range] at h; omega
    · intro l hl hne
      refine sum_eq_zero fun δ _ => ?_
      rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₁ h₁' (by simp only [mem_range] at hl; omega),
        ite_eq_right (fun h => hne h.2.2)]
      ring
    · intro h; simp only [mem_range] at h; omega
  · rw [ite_eq_right hk]
    refine sum_eq_zero fun l hl => sum_eq_zero fun δ _ => ?_
    rw [tripleForm_stateA_stateA hab hc h₁ h₁' h₂ h₂' (by simp only [mem_range] at hl; omega),
      ite_eq_right (fun h => hk ⟨h.1, h.2.1⟩)]
    ring

/-- **The `((12)3)4` states are orthonormal.** -/
theorem quadForm_T1_T1 (hab : 0 < a + b) (hc : 0 < c) (hd : 0 < d) {k₁₂ k₁₂' : Fin (min a b + 1)}
    {k₁₂₃ k₁₂₃' k₄ k₄' L L' : ℕ}
    (h₁ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ)) (h₁' : k₁₂₃ ≤ c)
    (h₂ : k₁₂₃' ≤ a + b - 2 * (k₁₂' : ℕ)) (h₂' : k₁₂₃' ≤ c)
    (h₃ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃) (h₃' : k₄ ≤ d)
    (h₄ : k₄' ≤ a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') (h₄' : k₄' ≤ d)
    (hL : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ + d - 2 * k₄) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T1 hab k₁₂' k₁₂₃' k₄' L') =
      if k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃' ∧ k₄ = k₄' ∧ L = L' then 1 else 0 := by
  have hT : T1 (d := d) hab k₁₂' k₁₂₃' k₄' L' =
      ∑ l' ∈ range (a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃' + 1), ∑ δ' ∈ range (d + 1),
        cgCoefficient (a + b - 2 * (k₁₂' : ℕ) + c - 2 * k₁₂₃') d k₄' L' l' δ' •
          (stateA hab k₁₂' k₁₂₃' l' ⊗ₜ normVec d δ') := rfl
  rw [hT, map_sum]
  simp_rw [map_sum, map_smul, smul_eq_mul]
  rw [sum_congr rfl fun l' hl' => sum_congr rfl fun δ' hδ' => by
    rw [quadForm_T1_tmul hab hc h₁ h₁' h₂ h₂' (by simp only [mem_range] at hl'; omega)
      (by simp only [mem_range] at hδ'; omega)]]
  by_cases hk : k₁₂ = k₁₂' ∧ k₁₂₃ = k₁₂₃'
  · obtain ⟨rfl, rfl⟩ := hk
    simp only [true_and, ite_true]
    rw [sum_congr rfl fun l' _ => sum_congr rfl fun δ' _ => mul_comm _ _,
      sum_cgCoefficient_mul (by omega) h₃ h₃' h₄ h₄' hL]
  · rw [ite_eq_right (fun h => hk ⟨h.1, h.2.1⟩)]
    refine sum_eq_zero fun l' _ => sum_eq_zero fun δ' _ => ?_
    rw [ite_eq_right hk, mul_zero]

/-! ## The pentagon for recoupling coefficients -/

/-- Different `k₁₂`-components of `V(a) ⊗ V(b)` are orthogonal in the four-fold product. -/
lemma quadForm_E12_E12_of_ne (hab : 0 < a + b) {k₁₂ k₁₂' : Fin (min a b + 1)} (hk : k₁₂ ≠ k₁₂')
    (u : Triple (a + b - 2 * (k₁₂ : ℕ)) c d) (v : Triple (a + b - 2 * (k₁₂' : ℕ)) c d) :
    quadForm a b c d (E12 hab k₁₂ u) (E12 hab k₁₂' v) = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul p z =>
    induction v using TensorProduct.inductionOn with
    | tmul p' z' =>
      rw [E12, E12, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, quadForm_tmul,
        tripleForm_rTensor_embed_of_ne hab _ hk, zero_mul]
    | add v v' hv hv' => rw [map_add, map_add, hv, hv', add_zero]
  | add u u' hu hu' => rw [map_add, map_add, LinearMap.add_apply, hu, hu', add_zero]

/-- `⟨((12)3)4 | (12)(34)⟩` for the same `j₁₂`: one recoupling coefficient of `(j₁₂ c d)`. -/
lemma quadForm_T1_T2 (hab : 0 < a + b) (k₁₂ : Fin (min a b + 1))
    (h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (hcd : 0 < c + d) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ))
    (hc : 0 < c) (hd : 0 < d) (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d) {K : ℕ}
    {k₃₄ : Fin (min c d + 1)} (hB : ValidB (a + b - 2 * (k₁₂ : ℕ)) c d K k₃₄) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL : L ≤ a + b - 2 * (k₁₂ : ℕ) + c + d - 2 * K) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T2 hab k₁₂ hcd k₃₄ (K - k₃₄) L) =
      (if ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁₂₃ then recoupling h12c hcd K L k₁₂₃ k₃₄
        else 0) * (if k₄ = K - k₁₂₃ then 1 else 0) := by
  have hk₁₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁₂₃.isLt)
  rw [T2_eq_sum_T1 hab k₁₂ h12c hcd h12 hd hB hL, map_sum, sum_eq_single k₁₂₃]
  · rw [map_smul, smul_eq_mul]
    by_cases hA : ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁₂₃
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      rw [ite_eq_left ⟨hA1, hA2, hA3⟩, quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 hk₁₂₃.1 hk₁₂₃.2
        hk₄.1 hk₄.2 hA2 hA3 hL1]
      by_cases hk4 : k₄ = K - k₁₂₃
      · rw [ite_eq_left ⟨rfl, rfl, hk4, rfl⟩, ite_eq_left hk4]
      · rw [ite_eq_right (fun h => hk4 h.2.2.1), ite_eq_right hk4]
    · rw [ite_eq_right hA, zero_mul, zero_mul]
  · intro k₁' _ hne
    rw [map_smul]
    by_cases hA : ValidA (a + b - 2 * (k₁₂ : ℕ)) c d K k₁'
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have hk₁' := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁'.isLt)
      rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 hk₁'.1 hk₁'.2 hk₄.1 hk₄.2 hA2 hA3 hL1,
        ite_eq_right (show ¬(k₁₂ = k₁₂ ∧ (k₁₂₃ : ℕ) = k₁' ∧ k₄ = K - k₁' ∧ L = L) from
          fun h => hne (Fin.ext h.2.1.symm)), smul_zero]
    · rw [ite_eq_right hA, zero_smul]
  · simp

/-- **The two-move side of the pentagon**: `⟨((12)3)4 | 1(2(34))⟩` through `(12)(34)`. -/
theorem quadForm_T1_T3_two (hab : 0 < a + b) (hcd : 0 < c + d) (ha : 0 < a) (hc : 0 < c)
    (hd : 0 < d) (k₁₂ : Fin (min a b + 1)) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ))
    (h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c) (k₃₄ : Fin (min c d + 1))
    (h34 : 0 < c + d - 2 * (k₃₄ : ℕ)) (h5 : 0 < b + (c + d - 2 * (k₃₄ : ℕ)))
    (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d)
    (k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) - 2 * k₁) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T3 hcd k₃₄ k₂ k₁ L) =
      (if ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂ then
        recoupling hab h5 (k₂ + k₁) L k₁₂ k₂ else 0) *
      ((if ValidA (a + b - 2 * (k₁₂ : ℕ)) c d (k₂ + k₁ - k₁₂ + k₃₄) k₁₂₃ then
        recoupling h12c hcd (k₂ + k₁ - k₁₂ + k₃₄) L k₁₂₃ k₃₄ else 0) *
      (if k₄ = k₂ + k₁ - k₁₂ + k₃₄ - k₁₂₃ then 1 else 0)) := by
  have hk₂ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂.isLt)
  have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
  rw [show T3 (a := a) hcd k₃₄ (k₂ : ℕ) k₁ L = T3 hcd k₃₄ k₂ (k₂ + k₁ - k₂) L by
      rw [Nat.add_sub_cancel_left],
    T3_eq_sum_T2 hab hcd k₃₄ h5 ha h34 ⟨by omega, by omega, by omega⟩ (by omega), map_sum,
    sum_eq_single k₁₂]
  · rw [map_smul, smul_eq_mul]
    by_cases hA : ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂
    · obtain ⟨hA1, hA2, hA3⟩ := hA
      have h2 := quadForm_T1_T2 hab k₁₂ h12c hcd h12 hc hd k₁₂₃ hk₄
        (K := k₂ + k₁ - k₁₂ + k₃₄) (k₃₄ := k₃₄) ⟨by omega, by omega, by omega⟩ hL1 (by omega)
      rw [show k₂ + k₁ - (k₁₂ : ℕ) + k₃₄ - k₃₄ = k₂ + k₁ - k₁₂ by omega] at h2
      rw [ite_eq_left ⟨hA1, hA2, hA3⟩, h2]
    · rw [ite_eq_right hA, zero_mul, zero_mul]
  · intro k₁₂' _ hne
    rw [map_smul, T2, ← E12_stateA hab k₁₂ h12c k₁₂₃ k₄ L,
      quadForm_E12_E12_of_ne hab (Ne.symm hne), smul_zero]
  · simp

/-- Proof-free, ℕ-indexed recoupling coefficient: Physlib's `recoupling` when all labels are
admissible, `0` otherwise. -/
noncomputable def rc (a b c K l k₁ k₃ : ℕ) : ℝ :=
  if h : 0 < a + b ∧ 0 < b + c ∧ k₁ < min a b + 1 ∧ k₃ < min b c + 1 ∧ ValidA a b c K k₁ ∧
      ValidB a b c K k₃ then recoupling h.1 h.2.1 K l ⟨k₁, h.2.2.1⟩ ⟨k₃, h.2.2.2.1⟩ else 0

lemma ite_recoupling_eq_rc (hab : 0 < a + b) (hbc : 0 < b + c) {K : ℕ} (l : ℕ)
    (k₁ : Fin (min a b + 1)) (k₃ : Fin (min b c + 1)) (hB : ValidB a b c K k₃) :
    (if ValidA a b c K k₁ then recoupling hab hbc K l k₁ k₃ else 0) = rc a b c K l k₁ k₃ := by
  unfold rc
  by_cases hA : ValidA a b c K k₁
  · rw [ite_eq_left hA, dite_eq_left ⟨hab, hbc, k₁.isLt, k₃.isLt, hA, hB⟩]
  · rw [ite_eq_right hA, dite_eq_right (fun h => hA h.2.2.2.2.1)]

lemma rc_of_not_validA {K l k₁ k₃ : ℕ} (h : ¬ ValidA a b c K k₁) : rc a b c K l k₁ k₃ = 0 :=
  dite_eq_right (fun h' => h h'.2.2.2.2.1)

/-- **The three-move side of the pentagon**: `⟨((12)3)4 | 1(2(34))⟩` through `1((23)4)` and
`(1(23))4`. -/
theorem quadForm_T1_T3_three (hab : 0 < a + b) (hbc : 0 < b + c) (hcd : 0 < c + d) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (k₁₂ : Fin (min a b + 1)) {k₁₂₃ k₄ : ℕ}
    (hk₁₂₃ : k₁₂₃ ≤ a + b - 2 * (k₁₂ : ℕ) ∧ k₁₂₃ ≤ c)
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ ∧ k₄ ≤ d) (k₃₄ : Fin (min c d + 1))
    {k₂ : ℕ} (hk₂ : k₂ ≤ b ∧ k₂ ≤ c + d - 2 * (k₃₄ : ℕ)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * k₂) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * k₁₂₃ + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * k₂) - 2 * k₁) :
    quadForm a b c d (T1 hab k₁₂ k₁₂₃ k₄ L) (T3 hcd k₃₄ k₂ k₁ L) =
      ∑ k₂₃ : Fin (min b c + 1), rc b c d (k₃₄ + k₂) 0 k₂₃ k₃₄ *
        ∑ k₁' : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1),
          rc a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) L k₁' (k₃₄ + k₂ - k₂₃) *
            (rc a b c (k₂₃ + k₁') 0 k₁₂ k₂₃ *
              (if k₁₂₃ = k₂₃ + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - k₂₃ + k₁ - k₁' then 1 else 0)) := by
  have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
  rw [show T3 (a := a) hcd k₃₄ k₂ k₁ L = T3 hcd k₃₄ (k₃₄ + k₂ - k₃₄) k₁ L by
      rw [Nat.add_sub_cancel_left],
    T3_eq_sum_T4 hbc hcd hb hd ⟨by omega, by omega, by omega⟩ k₁ L, map_sum]
  refine sum_congr rfl fun k₂₃ _ => ?_
  have hk₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂₃.isLt)
  rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc hbc hcd 0 k₂₃ k₃₄ ⟨by omega, by omega, by omega⟩]
  by_cases hA3 : ValidA b c d (k₃₄ + k₂) k₂₃
  · congr 1
    obtain ⟨h31, h32, h33⟩ := hA3
    have h2 := T4_eq_sum_T5 (a := a) hbc k₂₃ (by omega) (by omega) ha hd
      (K := k₃₄ + k₂ - k₂₃ + k₁)
      (k' := ⟨k₃₄ + k₂ - k₂₃, Nat.lt_succ_iff.mpr (Nat.le_min.mpr ⟨h32, h33⟩)⟩)
      ⟨by simp only; omega, by simp only; omega, by simp only; omega⟩ (L := L)
      (by omega)
    simp only [show k₃₄ + k₂ - (k₂₃ : ℕ) + k₁ - (k₃₄ + k₂ - k₂₃) = k₁ by omega] at h2
    rw [h2, map_sum]
    refine sum_congr rfl fun k₁' _ => ?_
    have hk₁' := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁'.isLt)
    rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc _ _ L k₁' _
      ⟨by simp only; omega, by simp only; omega, by simp only; omega⟩]
    by_cases hA2 : ValidA a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) k₁'
    · congr 1
      obtain ⟨h21, h22, h23⟩ := hA2
      rw [show T5 (d := d) hbc k₂₃ (k₁' : ℕ) (k₃₄ + k₂ - k₂₃ + k₁ - k₁') L =
          T5 hbc k₂₃ (k₂₃ + k₁' - k₂₃) (k₃₄ + k₂ - k₂₃ + k₁ - k₁') L by
          rw [Nat.add_sub_cancel_left],
        T5_eq_sum_T1 hab hbc ha hc ⟨by omega, by omega, by omega⟩, map_sum, sum_eq_single k₁₂]
      · rw [map_smul, smul_eq_mul, ite_recoupling_eq_rc hab hbc 0 k₁₂ k₂₃
          ⟨by omega, by omega, by omega⟩]
        by_cases hA1 : ValidA a b c (k₂₃ + k₁') k₁₂
        · congr 1
          obtain ⟨h11, h12, h13⟩ := hA1
          rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 h12 h13 hk₄.1 hk₄.2 (by omega) h23 hL1]
          simp only [true_and, and_true]
        · rw [rc_of_not_validA hA1, zero_mul, zero_mul]
      · intro k₁₂' _ hne
        rw [map_smul]
        by_cases hA1 : ValidA a b c (k₂₃ + k₁') k₁₂'
        · obtain ⟨h11, h12, h13⟩ := hA1
          rw [quadForm_T1_T1 hab hc hd hk₁₂₃.1 hk₁₂₃.2 h12 h13 hk₄.1 hk₄.2 (by omega) h23 hL1,
            ite_eq_right (show ¬(k₁₂ = k₁₂' ∧ _) from fun h => hne h.1.symm), smul_zero]
        · rw [ite_eq_right hA1, zero_smul]
      · simp
    · rw [rc_of_not_validA hA2, zero_mul, zero_mul]
  · rw [rc_of_not_validA hA3, zero_mul, zero_mul]

/-- **The pentagon (Biedenharn–Elliott) identity for recoupling coefficients.** For positive
`j₁, j₂, j₃, j₄, j₁₂, j₃₄`, expanding `⟨((12)3)4 | 1(2(34))⟩` in two moves (via `(12)(34)`) and
in three moves (via `1((23)4)`, `(1(23))4`) gives the same number:
`R_{a b j₃₄} · R_{j₁₂ c d} = Σ_{j₂₃} R_{b c d} · R_{a j₂₃ d} · R_{a b c}` (labels as in the
statement; the indicators enforce the shared intermediate spins). -/
theorem pentagon_rc (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (k₁₂ : Fin (min a b + 1)) (h12 : 0 < a + b - 2 * (k₁₂ : ℕ)) (k₃₄ : Fin (min c d + 1))
    (h34 : 0 < c + d - 2 * (k₃₄ : ℕ)) (k₁₂₃ : Fin (min (a + b - 2 * (k₁₂ : ℕ)) c + 1)) {k₄ : ℕ}
    (hk₄ : k₄ ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) ∧ k₄ ≤ d)
    (k₂ : Fin (min b (c + d - 2 * (k₃₄ : ℕ)) + 1)) {k₁ : ℕ}
    (hk₁ : k₁ ≤ a ∧ k₁ ≤ b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) {L : ℕ}
    (hL1 : L ≤ a + b - 2 * (k₁₂ : ℕ) + c - 2 * (k₁₂₃ : ℕ) + d - 2 * k₄)
    (hL3 : L ≤ a + (b + (c + d - 2 * (k₃₄ : ℕ)) - 2 * (k₂ : ℕ)) - 2 * k₁) :
    rc a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) L k₁₂ k₂ *
        (rc (a + b - 2 * (k₁₂ : ℕ)) c d (k₂ + k₁ - k₁₂ + k₃₄) L k₁₂₃ k₃₄ *
          (if k₄ = k₂ + k₁ - k₁₂ + k₃₄ - k₁₂₃ then 1 else 0)) =
      ∑ k₂₃ : Fin (min b c + 1), rc b c d (k₃₄ + k₂) 0 k₂₃ k₃₄ *
        ∑ k₁' : Fin (min a (b + c - 2 * (k₂₃ : ℕ)) + 1),
          rc a (b + c - 2 * (k₂₃ : ℕ)) d (k₃₄ + k₂ - k₂₃ + k₁) L k₁' (k₃₄ + k₂ - k₂₃) *
            (rc a b c (k₂₃ + k₁') 0 k₁₂ k₂₃ *
              (if (k₁₂₃ : ℕ) = k₂₃ + k₁' - k₁₂ ∧ k₄ = k₃₄ + k₂ - k₂₃ + k₁ - k₁' then 1 else 0)) := by
  have hab : 0 < a + b := by omega
  have hbc : 0 < b + c := by omega
  have hcd : 0 < c + d := by omega
  have h12c : 0 < a + b - 2 * (k₁₂ : ℕ) + c := by omega
  have h5 : 0 < b + (c + d - 2 * (k₃₄ : ℕ)) := by omega
  have hk₂ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₂.isLt)
  have hk₁₂₃ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₁₂₃.isLt)
  have htwo := quadForm_T1_T3_two hab hcd ha hc hd k₁₂ h12 h12c k₃₄ h34 h5 k₁₂₃ hk₄ k₂ hk₁ hL1 hL3
  have hthree := quadForm_T1_T3_three hab hbc hcd ha hb hc hd k₁₂ hk₁₂₃ hk₄ k₃₄ hk₂ hk₁ hL1 hL3
  rw [← hthree, htwo, ite_recoupling_eq_rc hab h5 L k₁₂ k₂ ⟨by omega, by omega, by omega⟩]
  by_cases hA : ValidA a b (c + d - 2 * (k₃₄ : ℕ)) (k₂ + k₁) k₁₂
  · obtain ⟨hA1, hA2, hA3⟩ := hA
    have hk₃₄ := Nat.le_min.mp (Nat.lt_succ_iff.mp k₃₄.isLt)
    rw [ite_recoupling_eq_rc h12c hcd L k₁₂₃ k₃₄ ⟨by omega, by omega, by omega⟩]
  · rw [rc_of_not_validA hA, zero_mul, zero_mul]

end PhyslibAlpha.Sl2.Pentagon
