import Lightlike.SpinFoam.EPRLStateSum.NodeCoefOrth

/-!
# Transposed orthogonality of the node coefficients for the rotations `1` and `3`

`NodeCoefOrth.lean` proves `Σ_l N_r(i,l) N_r(i',l) = δ_{ii'}`. A tetrahedron label that is summed
once, over two 4-simplices, needs the other contraction `Σ_i N_r(i,l) N_r(i,l') = δ_{ll'}`:

* `sum_rot1Recoupling_mul_left`: the rotation matrix is orthogonal in its first index;
* `sum_comp_orth_left`: composition of such a matrix with coefficients supported on its columns;
* `sum_nodeCoef_one_mul_left`, `sum_nodeCoef_three_mul_left`: `Σ_i N_r(i,l) N_r(i,l') = δ_{ll'}` on
  the admissible labels `l` of the intrinsic `(02)(13)` channel.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

/-- **Orthogonality of the rotation matrix in its first index**:
`Σ_k rot1 k l · rot1 k l' = δ_{ll'}` for admissible `l` (triads `(j₀ j₁ l)`, `(l j₂ j₃)`). -/
theorem sum_rot1Recoupling_mul_left (j₀ j₁ j₂ j₃ l l' : ℕ) :
    ∑ k ∈ range (j₀ + j₃ + 1), rot1Recoupling j₀ j₁ j₂ j₃ k l * rot1Recoupling j₀ j₁ j₂ j₃ k l' =
      if l = l' ∧ Pentagon.Tri j₀ j₁ l ∧ Pentagon.Tri l j₂ j₃ then 1 else 0 := by
  have key := sum_fourRecoupling_mul_left j₀ j₃ j₁ j₂ l l'
  have hterm : ∀ k ∈ range (j₀ + j₃ + 1),
      rot1Recoupling j₀ j₁ j₂ j₃ k l * rot1Recoupling j₀ j₁ j₂ j₃ k l' =
        (fourRecoupling j₀ j₃ j₁ j₂ k l * fourRecoupling j₀ j₃ j₁ j₂ k l') *
          (((-1) ^ ((l + j₂ + j₃) / 2) * (-1) ^ ((l' + j₂ + j₃) / 2)) *
            (((-1 : ℝ) ^ k * (-1) ^ k) * ((-1) ^ ((j₀ + j₃ + k) / 2) * (-1) ^ ((j₀ + j₃ + k) / 2)))) :=
    fun k _ => by
      unfold rot1Recoupling
      ring
  rw [sum_congr rfl hterm]
  simp only [negOnePow_mul_self, mul_one]
  rw [← sum_mul, key]
  have e : Pentagon.Tri l j₃ j₂ ↔ Pentagon.Tri l j₂ j₃ := by
    unfold Pentagon.Tri
    omega
  simp only [e]
  by_cases hll : l = l'
  · subst hll
    rw [negOnePow_mul_self]
    simp
  · simp [hll]

/-- Composition of a matrix `R` (first index `i ∈ S`), orthogonal in `i` on the columns `k`
admissible for `P`, with coefficients `B k l` supported on those columns:
`Σ_i (Σ_k R_{ik} B_{kl}) (Σ_k' R_{ik'} B_{k'l'}) = Σ_k B_{kl} B_{kl'}`. -/
lemma sum_comp_orth_left {S T : Finset ℕ} (R B : ℕ → ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P]
    (l l' : ℕ)
    (horth : ∀ k ∈ T, ∀ k' ∈ T, ∑ i ∈ S, R i k * R i k' = if k = k' ∧ P k then 1 else 0)
    (hsupp : ∀ k ∈ T, ∀ m, B k m ≠ 0 → P k) :
    ∑ i ∈ S, (∑ k ∈ T, R i k * B k l) * (∑ k' ∈ T, R i k' * B k' l') =
      ∑ k ∈ T, B k l * B k l' := by
  have h1 : ∀ i, (∑ k ∈ T, R i k * B k l) * (∑ k' ∈ T, R i k' * B k' l') =
      ∑ k ∈ T, ∑ k' ∈ T, (B k l * B k' l') * (R i k * R i k') := fun i => by
    rw [sum_mul_sum]
    exact sum_congr rfl fun k _ => sum_congr rfl fun k' _ => by ring
  simp only [h1]
  rw [sum_comm]
  have h2 : ∀ k ∈ T, ∑ i ∈ S, ∑ k' ∈ T, (B k l * B k' l') * (R i k * R i k') =
      ∑ k' ∈ T, (B k l * B k' l') * (if k = k' ∧ P k then 1 else 0) := fun k hk => by
    rw [sum_comm]
    refine sum_congr rfl fun k' hk' => ?_
    rw [← mul_sum, horth k hk k' hk']
  rw [sum_congr rfl h2]
  refine sum_congr rfl fun k hk => ?_
  by_cases hP : P k
  · simp [hP, hk]
  · have : B k l = 0 := by
      by_contra hne
      exact hP (hsupp k hk l hne)
    simp [this]

/-- A sum over `range a` of a function supported below `a` and `b` equals the sum over `range b`. -/
lemma sum_range_congr_supp (a b : ℕ) (f : ℕ → ℝ) (h : ∀ k, f k ≠ 0 → k < a ∧ k < b) :
    ∑ k ∈ range a, f k = ∑ k ∈ range b, f k := by
  rw [← sum_filter_ne_zero, ← sum_filter_ne_zero (s := range b)]
  refine sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨_, hk⟩
    exact ⟨(h k hk).2, hk⟩
  · rintro ⟨_, hk⟩
    exact ⟨(h k hk).1, hk⟩

/-- **Transposed orthogonality for rotation `0`**: `Σ_i N₀(i,l) N₀(i,l') = δ_{ll'}`. -/
theorem sum_nodeCoef_zero_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 0 i l * nodeCoef t₀ t₁ t₂ t₃ 0 i l' =
      if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 :=
  sum_fourRecoupling_mul_left t₀ t₁ t₂ t₃ l l'

/-- **Transposed orthogonality for rotation `2`**: `Σ_i N₂(i,l) N₂(i,l') = δ_{ll'}`. -/
theorem sum_nodeCoef_two_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 2 i l * nodeCoef t₀ t₁ t₂ t₃ 2 i l' =
      if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  rw [← sum_fourRecoupling_mul_left t₀ t₁ t₂ t₃ l l']
  refine sum_congr rfl fun i _ => ?_
  have h : ∀ m, nodeCoef t₀ t₁ t₂ t₃ 2 i m = (-1) ^ i * fourRecoupling t₀ t₁ t₂ t₃ i m :=
    fun m => rfl
  rw [h, h]
  have := negOnePow_mul_self i
  calc _ = ((-1 : ℝ) ^ i * (-1) ^ i) * (fourRecoupling t₀ t₁ t₂ t₃ i l *
        fourRecoupling t₀ t₁ t₂ t₃ i l') := by ring
    _ = _ := by rw [this, one_mul]

/-- **Transposed orthogonality for rotation `1`**: `Σ_i N₁(i,l) N₁(i,l') = δ_{ll'}` for the
admissible labels `l` of the intrinsic channel (triads `(t₀ t₂ l)`, `(l t₁ t₃)`). -/
theorem sum_nodeCoef_one_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₃ + 1), nodeCoef t₀ t₁ t₂ t₃ 1 i l * nodeCoef t₀ t₁ t₂ t₃ 1 i l' =
      if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  have hN : ∀ j m, nodeCoef t₀ t₁ t₂ t₃ 1 j m = ∑ k ∈ range (t₀ + t₁ + 1),
      rot1Recoupling t₀ t₁ t₂ t₃ j k * fourRecoupling t₀ t₁ t₂ t₃ k m := fun j m => rfl
  simp only [hN]
  rw [sum_comp_orth_left (S := range (t₀ + t₃ + 1)) (T := range (t₀ + t₁ + 1))
    (fun i k => rot1Recoupling t₀ t₁ t₂ t₃ i k) (fun k m => fourRecoupling t₀ t₁ t₂ t₃ k m)
    (fun k => Pentagon.Tri t₀ t₁ k ∧ Pentagon.Tri k t₂ t₃) l l'
    (fun k _ k' _ => sum_rot1Recoupling_mul_left t₀ t₁ t₂ t₃ k k')
    (fun k _ m hk => by
      obtain ⟨a, b, -, -⟩ := fourRecoupling_support hk
      exact ⟨a, b⟩)]
  exact sum_fourRecoupling_mul_left t₀ t₁ t₂ t₃ l l'

/-- **Transposed orthogonality for rotation `3`**: `Σ_i N₃(i,l) N₃(i,l') = δ_{ll'}` for the
admissible labels `l` of the intrinsic channel (triads `(t₀ t₂ l)`, `(l t₁ t₃)`). -/
theorem sum_nodeCoef_three_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₂ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 3 i l * nodeCoef t₀ t₁ t₂ t₃ 3 i l' =
      if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  have hN : ∀ j m, nodeCoef t₀ t₁ t₂ t₃ 3 j m = ∑ k ∈ range (t₂ + t₃ + 1),
      rot1Recoupling t₂ t₃ t₀ t₁ j k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k m) :=
    fun j m => rfl
  simp only [hN]
  rw [sum_comp_orth_left (S := range (t₂ + t₁ + 1)) (T := range (t₂ + t₃ + 1))
    (fun i k => rot1Recoupling t₂ t₃ t₀ t₁ i k)
    (fun k m => (-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k m)
    (fun k => Pentagon.Tri t₂ t₃ k ∧ Pentagon.Tri k t₀ t₁) l l'
    (fun k _ k' _ => sum_rot1Recoupling_mul_left t₂ t₃ t₀ t₁ k k')
    (fun k _ m hk => by
      have hk' : fourRecoupling t₀ t₁ t₂ t₃ k m ≠ 0 := fun h => hk (by rw [h, mul_zero])
      obtain ⟨a, b, -, -⟩ := fourRecoupling_support hk'
      unfold Pentagon.Tri at a b ⊢
      exact ⟨by omega, by omega⟩)]
  have hterm : ∀ k, ((-1 : ℝ) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) *
      ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l') =
      fourRecoupling t₀ t₁ t₂ t₃ k l * fourRecoupling t₀ t₁ t₂ t₃ k l' := fun k => by
    have := negOnePow_mul_self k
    calc _ = ((-1 : ℝ) ^ k * (-1) ^ k) * (fourRecoupling t₀ t₁ t₂ t₃ k l *
          fourRecoupling t₀ t₁ t₂ t₃ k l') := by ring
      _ = _ := by rw [this, one_mul]
  simp only [hterm]
  rw [sum_range_congr_supp (t₂ + t₃ + 1) (t₀ + t₁ + 1)]
  · exact sum_fourRecoupling_mul_left t₀ t₁ t₂ t₃ l l'
  · intro k hk
    have h1 : fourRecoupling t₀ t₁ t₂ t₃ k l ≠ 0 := left_ne_zero_of_mul hk
    obtain ⟨a, b, -, -⟩ := fourRecoupling_support h1
    unfold Pentagon.Tri at a b
    constructor <;> omega

end Lightlike.SpinFoam.EPRLStateSum
