import Lightlike.Recoupling.Symmetry

/-!
# The change from the odd-node leg order to the sorted channel of a tetrahedron

`NodeBasis` shows that at an odd position `a` the EPRL label `i_a` of the tetrahedron couples the
sorted legs `(12)(30)` instead of `(01)(23)`. This file computes the orthogonal matrix
`rot1Recoupling` that turns the `(12)(30)` intertwiner into the sorted `(01)(23)` ones, so that a
corrected vertex can be written in the intrinsic basis.

* `fourJ_rot1`: `ι_{j₁ j₂ j₃ j₀}^{(k)} = Σ_l rot1Recoupling j₀ j₁ j₂ j₃ k l · ι_{j₀ j₁ j₂ j₃}^{(l)}`,
  componentwise, for all spins and projections.
* `sum_rot1Recoupling_mul`: `Σ_l rot1 k l · rot1 k' l = δ_{kk'}` on admissible `k`.
* The rotation by two legs is `Lightlike.Recoupling.fourJ_swapPairs` (a sign `(-1)^k`).
-/

open Finset Lightlike.Recoupling

namespace Lightlike.SpinFoam.EPRLStateSum

/-- Signs squared are one. -/
lemma negOnePow_mul_self (a : ℕ) : ((-1 : ℝ) ^ a) * (-1) ^ a = 1 := by
  rw [← mul_pow]; norm_num

/-- The recoupling matrix from the `(12)(30)` intertwiner `ι_{j₁ j₂ j₃ j₀}^{(k)}` (legs in the
rotated order) to the sorted `(01)(23)` intertwiners `ι_{j₀ j₁ j₂ j₃}^{(l)}`:
`(-1)^k (-1)^((j₀+j₃+k)/2) ⟨ι^{(03)k} | ι^{(01)l}⟩ (-1)^((l+j₂+j₃)/2)`, composed of the pair swap,
an exchange of the first two legs, `fourRecoupling` and an exchange of the last two legs. -/
noncomputable def rot1Recoupling (j₀ j₁ j₂ j₃ k l : ℕ) : ℝ :=
  (-1) ^ k * (-1) ^ ((j₀ + j₃ + k) / 2) * fourRecoupling j₀ j₃ j₁ j₂ k l *
    (-1) ^ ((l + j₂ + j₃) / 2)

/-- **Rotation by one leg**: the intertwiner with legs `(j₁ j₂)(j₃ j₀)` and label `k` is the
combination `Σ_l rot1Recoupling · ι_{j₀ j₁ j₂ j₃}^{(l)}` of the sorted-channel intertwiners. -/
theorem fourJ_rot1 (j₀ j₁ j₂ j₃ k : ℕ) (m₀ m₁ m₂ m₃ : ℤ) :
    fourJ j₁ j₂ j₃ j₀ k m₁ m₂ m₃ m₀ = ∑ l ∈ range (j₀ + j₁ + 1),
      rot1Recoupling j₀ j₁ j₂ j₃ k l * fourJ j₀ j₁ j₂ j₃ l m₀ m₁ m₂ m₃ := by
  have h1 := fourJ_swapPairs j₃ j₀ j₁ j₂ k m₃ m₀ m₁ m₂
  have h2 := fourJ_swap₁₂ j₃ j₀ j₁ j₂ k m₃ m₀ m₁ m₂
  have h3 := fourJ_eq_sum_fourRecoupling j₀ j₃ j₁ j₂ k m₀ m₃ m₁ m₂
  have h4 : ∀ l, fourJ j₀ j₁ j₃ j₂ l m₀ m₁ m₃ m₂ =
      (-1) ^ ((l + j₂ + j₃) / 2) * fourJ j₀ j₁ j₂ j₃ l m₀ m₁ m₂ m₃ := fun l =>
    fourJ_swap₃₄ j₀ j₁ j₂ j₃ l m₀ m₁ m₂ m₃
  set s : ℝ := (-1) ^ ((j₃ + j₀ + k) / 2) with hs
  have hss : s * s = 1 := negOnePow_mul_self _
  have h5 : fourJ j₃ j₀ j₁ j₂ k m₃ m₀ m₁ m₂ = s * fourJ j₀ j₃ j₁ j₂ k m₀ m₃ m₁ m₂ := by
    rw [h2, ← mul_assoc, hss, one_mul]
  rw [h1, h5, h3, mul_sum, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [h4 l]
  unfold rot1Recoupling
  rw [add_comm j₀ j₃]
  ring

/-- **Orthogonality of the rotation matrix**: `Σ_l rot1 k l · rot1 k' l = δ_{kk'}` for admissible
`k` (`(j₀ j₃ k)` and `(k j₁ j₂)` triads), `0` otherwise. -/
theorem sum_rot1Recoupling_mul (j₀ j₁ j₂ j₃ k k' : ℕ) :
    ∑ l ∈ range (j₀ + j₁ + 1), rot1Recoupling j₀ j₁ j₂ j₃ k l * rot1Recoupling j₀ j₁ j₂ j₃ k' l =
      if k = k' ∧ Pentagon.Tri j₀ j₃ k ∧ Pentagon.Tri k j₁ j₂ then 1 else 0 := by
  have key := sum_fourRecoupling_mul j₀ j₃ j₁ j₂ k k'
  set c : ℝ := (-1) ^ k * (-1) ^ ((j₀ + j₃ + k) / 2) * ((-1) ^ k' * (-1) ^ ((j₀ + j₃ + k') / 2))
    with hc
  have hterm : ∀ l ∈ range (j₀ + j₁ + 1),
      rot1Recoupling j₀ j₁ j₂ j₃ k l * rot1Recoupling j₀ j₁ j₂ j₃ k' l =
        c * (fourRecoupling j₀ j₃ j₁ j₂ k l * fourRecoupling j₀ j₃ j₁ j₂ k' l) *
          ((-1) ^ ((l + j₂ + j₃) / 2) * (-1) ^ ((l + j₂ + j₃) / 2)) := by
    intro l _
    unfold rot1Recoupling
    rw [hc]
    ring
  rw [sum_congr rfl hterm]
  simp only [negOnePow_mul_self, mul_one]
  rw [← mul_sum, key]
  by_cases hkk : k = k'
  · subst hkk
    have : c = 1 := by
      rw [hc]
      calc _ = ((-1 : ℝ) ^ k * (-1) ^ k) * ((-1) ^ ((j₀ + j₃ + k) / 2) * (-1) ^ ((j₀ + j₃ + k) / 2)) := by
            ring
        _ = 1 := by rw [negOnePow_mul_self, negOnePow_mul_self, one_mul]
    rw [this, one_mul]
  · simp [hkk]

end Lightlike.SpinFoam.EPRLStateSum
