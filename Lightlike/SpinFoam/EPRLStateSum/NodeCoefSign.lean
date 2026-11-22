import Lightlike.SpinFoam.EPRLStateSum.NodeCoefOrthT

/-!
# The sign `(-1)^i` of rotation `2` is constant on the admissible labels

A node intertwiner label `i` of a tetrahedron with spins `t₀ t₁ t₂ t₃` (doubled units) is admissible
only if `t₀ + t₁ + i` is even. So the factor `(-1)^i` in `nodeCoef … 2 i l` is the *constant*
`(-1)^(t₀+t₁)` on every nonzero coefficient. Hence two 4-simplices that glue along a tetrahedron
at positions of rotation `0` and `2` give, after the sum over the shared label, the Kronecker delta
times the sign `(-1)^(t₀+t₁)` (and not a non-diagonal matrix, as the factor `(-1)^i` suggested).

* `nodeCoef_two_eq_sign`: `N₂(i,l) = (-1)^(t₀+t₁) N₀(i,l)`;
* `sum_nodeCoef_zero_two_mul_left`, `sum_nodeCoef_two_zero_mul_left`: the mixed transposed
  orthogonality `Σ_i N₀(i,l) N₂(i,l') = (-1)^(t₀+t₁) δ_{ll'}`;
* `sum_nodeCoef_zero_two_mul`: the mixed orthogonality in the other index.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

/-- If `x + y + z` is even then `(-1)^z = (-1)^(x+y)`. -/
lemma negOnePow_eq_of_even {x y z : ℕ} (h : (x + y + z) % 2 = 0) :
    ((-1 : ℝ) ^ z) = (-1) ^ (x + y) := by
  have he : Even (x + y + z) := Nat.even_iff.mpr h
  have h1 : ((-1 : ℝ) ^ (x + y)) * (-1) ^ z = 1 := by
    rw [← pow_add]
    exact he.neg_one_pow
  have h2 : ((-1 : ℝ) ^ (x + y)) * (-1) ^ (x + y) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc ((-1 : ℝ) ^ z) = ((-1 : ℝ) ^ (x + y)) * (((-1 : ℝ) ^ (x + y)) * (-1) ^ z) := by
        rw [← mul_assoc, h2, one_mul]
    _ = _ := by rw [h1, mul_one]

/-- **The sign of rotation `2` is constant**: `N₂(i,l) = (-1)^(t₀+t₁) N₀(i,l)`. -/
theorem nodeCoef_two_eq_sign (t₀ t₁ t₂ t₃ i l : ℕ) :
    nodeCoef t₀ t₁ t₂ t₃ 2 i l = (-1) ^ (t₀ + t₁) * nodeCoef t₀ t₁ t₂ t₃ 0 i l := by
  rw [nodeCoef_two, nodeCoef_zero]
  by_cases h : fourRecoupling t₀ t₁ t₂ t₃ i l = 0
  · rw [h]; simp
  · obtain ⟨⟨h2, -⟩, -⟩ := fourRecoupling_support h
    rw [negOnePow_eq_of_even (x := t₀) (y := t₁) (z := i) (by omega)]

/-- **Mixed transposed orthogonality (rotations `0`, `2`)**:
`Σ_i N₀(i,l) N₂(i,l') = (-1)^(t₀+t₁) δ_{ll'}` on the admissible labels. -/
theorem sum_nodeCoef_zero_two_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 0 i l * nodeCoef t₀ t₁ t₂ t₃ 2 i l' =
      (-1) ^ (t₀ + t₁) *
        if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  rw [← sum_nodeCoef_zero_mul_left t₀ t₁ t₂ t₃ l l', mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [nodeCoef_two_eq_sign]
  ring

/-- **Mixed transposed orthogonality (rotations `2`, `0`)**. -/
theorem sum_nodeCoef_two_zero_mul_left (t₀ t₁ t₂ t₃ l l' : ℕ) :
    ∑ i ∈ range (t₀ + t₁ + 1), nodeCoef t₀ t₁ t₂ t₃ 2 i l * nodeCoef t₀ t₁ t₂ t₃ 0 i l' =
      (-1) ^ (t₀ + t₁) *
        if l = l' ∧ Pentagon.Tri t₀ t₂ l ∧ Pentagon.Tri l t₁ t₃ then 1 else 0 := by
  rw [← sum_nodeCoef_zero_mul_left t₀ t₁ t₂ t₃ l l', mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [nodeCoef_two_eq_sign]
  ring

/-- **Mixed orthogonality in the other index (rotations `0`, `2`)**:
`Σ_l N₀(i,l) N₂(i',l) = (-1)^(t₀+t₁) δ_{ii'}` on the admissible labels. -/
theorem sum_nodeCoef_zero_two_mul (t₀ t₁ t₂ t₃ i i' : ℕ) :
    ∑ l ∈ range (t₀ + t₂ + 1), nodeCoef t₀ t₁ t₂ t₃ 0 i l * nodeCoef t₀ t₁ t₂ t₃ 2 i' l =
      (-1) ^ (t₀ + t₁) *
        if i = i' ∧ Pentagon.Tri t₀ t₁ i ∧ Pentagon.Tri i t₂ t₃ then 1 else 0 := by
  rw [← sum_nodeCoef_zero_mul t₀ t₁ t₂ t₃ i i', mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [nodeCoef_two_eq_sign]
  ring

end Lightlike.SpinFoam.EPRLStateSum
