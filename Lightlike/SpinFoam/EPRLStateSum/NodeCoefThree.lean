import Lightlike.SpinFoam.EPRLStateSum.NodeCoefSign

/-!
# Rotation `3` is rotation `1` up to a constant sign

A tetrahedron with sorted spins `t₀ t₁ t₂ t₃` sits at a node of rotation `1` with legs
`(t₁ t₂ t₃ t₀)` or of rotation `3` with legs `(t₃ t₀ t₁ t₂)`. These differ by the exchange of
the two pairs of legs, and the label `i` (coupling the first pair) is fixed mod `2`; so the two
bases of node intertwiners agree up to the constant sign `(-1)^(t₀+t₃)`:

* `fourRecoupling_flip`: `R(t₂ t₁ t₃ t₀; i, k) = R(t₀ t₃ t₁ t₂; i, k)`;
* `rot1Recoupling_three_one`: `rot1(t₂ t₃ t₀ t₁; i, k) (-1)^k = (-1)^(t₀+t₃) rot1(t₀ t₁ t₂ t₃; i, k)`;
* `nodeCoef_three_eq_sign`: `N₃(i,l) = (-1)^(t₀+t₃) N₁(i,l)`;
* `sum_nodeCoef_one_three_mul`, `sum_nodeCoef_one_three_mul_left`: mixed orthogonality of
  rotations `1` and `3`, with the constant sign.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

/-- Equal parity of exponents gives equal signs. -/
lemma negOnePow_congr {a b : ℕ} (h : a % 2 = b % 2) : ((-1 : ℝ) ^ a) = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two a, neg_one_pow_eq_pow_mod_two b, h]

/-- The recoupling coefficient of the two pairs `(t₂ t₁)(t₃ t₀)` is that of `(t₀ t₃)(t₁ t₂)`:
the `6j` symbols differ by the exchange of upper and lower spins in two columns. -/
theorem fourRecoupling_flip (t₀ t₁ t₂ t₃ i k : ℕ) :
    fourRecoupling t₂ t₁ t₃ t₀ i k = fourRecoupling t₀ t₃ t₁ t₂ i k := by
  unfold fourRecoupling
  rw [← sj_flip12 t₂ t₁ i t₀ t₃ k, add_comm t₁ t₃]

/-- **Rotation matrices of rotations `3` and `1`**: for the sorted spins `t₀ t₁ t₂ t₃`,
`rot1(t₂ t₃ t₀ t₁; i, k) (-1)^k = (-1)^(t₀+t₃) rot1(t₀ t₁ t₂ t₃; i, k)`. -/
theorem rot1Recoupling_three_one (t₀ t₁ t₂ t₃ i k : ℕ) :
    rot1Recoupling t₂ t₃ t₀ t₁ i k * (-1) ^ k =
      (-1) ^ (t₀ + t₃) * rot1Recoupling t₀ t₁ t₂ t₃ i k := by
  by_cases h : fourRecoupling t₀ t₃ t₁ t₂ i k = 0
  · unfold rot1Recoupling
    rw [fourRecoupling_flip t₀ t₁ t₂ t₃ i k, h]
    simp
  · obtain ⟨a, b, c, d⟩ := fourRecoupling_support h
    unfold Pentagon.Tri at a b c d
    unfold rot1Recoupling
    rw [fourRecoupling_flip t₀ t₁ t₂ t₃ i k]
    have key : (-1 : ℝ) ^ i * (-1) ^ ((t₂ + t₁ + i) / 2) * (-1) ^ ((k + t₀ + t₁) / 2) *
        (-1) ^ k = (-1) ^ (t₀ + t₃) * ((-1) ^ i * (-1) ^ ((t₀ + t₃ + i) / 2) *
          (-1) ^ ((k + t₂ + t₃) / 2)) := by
      simp only [← pow_add]
      exact negOnePow_congr (by omega)
    linear_combination (fourRecoupling t₀ t₃ t₁ t₂ i k) * key

/-- **Rotation `3` is rotation `1` up to a constant sign**: `N₃(i,l) = (-1)^(t₀+t₃) N₁(i,l)`. -/
theorem nodeCoef_three_eq_sign (t₀ t₁ t₂ t₃ i l : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ 3 i l = (-1) ^ (t₀ + t₃) * nodeCoef t₀ t₁ t₂ t₃ 1 i l := by
  have h3 : nodeCoef t₀ t₁ t₂ t₃ 3 i l = ∑ k ∈ range (t₂ + t₃ + 1),
      rot1Recoupling t₂ t₃ t₀ t₁ i k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) := rfl
  have h1 : nodeCoef t₀ t₁ t₂ t₃ 1 i l = ∑ k ∈ range (t₀ + t₁ + 1),
      rot1Recoupling t₀ t₁ t₂ t₃ i k * fourRecoupling t₀ t₁ t₂ t₃ k l := rfl
  have hterm : ∀ k, rot1Recoupling t₂ t₃ t₀ t₁ i k * ((-1) ^ k * fourRecoupling t₀ t₁ t₂ t₃ k l) =
      (-1) ^ (t₀ + t₃) * (rot1Recoupling t₀ t₁ t₂ t₃ i k * fourRecoupling t₀ t₁ t₂ t₃ k l) :=
    fun k => by
      have := rot1Recoupling_three_one t₀ t₁ t₂ t₃ i k
      linear_combination (fourRecoupling t₀ t₁ t₂ t₃ k l) * this
  rw [h3, h1, sum_congr rfl fun k _ => hterm k, ← mul_sum]
  congr 1
  refine sum_range_congr_supp _ _ _ fun k hk => ?_
  have hk' : fourRecoupling t₀ t₁ t₂ t₃ k l ≠ 0 := fun h => hk (by rw [h, mul_zero])
  obtain ⟨a, b, -, -⟩ := fourRecoupling_support hk'
  unfold Pentagon.Tri at a b
  omega

/-- **Mixed orthogonality of rotations `1` and `3`** (sum over the intrinsic label):
`Σ_l N₁(i,l) N₃(i',l) = (-1)^(t₀+t₃) δ_{ii'}` on the admissible labels. -/
theorem sum_nodeCoef_one_three_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 1 i l * nodeCoef t₀ t₁ t₂ t₃ 3 i' l =
      (-1) ^ (t₀ + t₃) *
        if i = i' ∧ Pentagon.Tri t₀ t₃ i ∧ Pentagon.Tri i t₁ t₂ then 1 else 0 := by
  rw [← sum_nodeCoef_one_mul t₀ t₁ t₂ t₃ i i', mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [nodeCoef_three_eq_sign]
  ring

/-- **Mixed transposed orthogonality of rotations `1` and `3`** (sum over the node label):
`Σ_i N₁(i,l) N₃(i,l') = (-1)^(t₀+t₃) δ_{ll'}` on the admissible intrinsic labels. -/
theorem sum_nodeCoef_one_three_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₃ + 1), nodeCoef t₀ t₁ t₂ t₃ 1 i l * nodeCoef t₀ t₁ t₂ t₃ 3 i l' =
      (-1) ^ (t₀ + t₃) *
        if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  rw [← sum_nodeCoef_one_mul_left t₀ t₁ t₂ t₃ l l', mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [nodeCoef_three_eq_sign]
  ring

end Lightlike.SpinFoam.EPRLStateSum
