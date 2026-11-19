import Mathlib

/-!
# Linear ODEs with continuous coefficients: the zero solution is unique (G1-024)
-/

open Set

namespace Lightlike

/-- **A solution of a linear system with continuous coefficients that vanishes at `0` vanishes on `[0, 1]`**:
if `F' (t) = A(t) F(t)` componentwise on `[0, 1]`, with each coefficient `A i j` continuous there, and `F 0 = 0`, then
`F t = 0` for `t ∈ [0, 1]` (Gronwall's inequality). -/
theorem linear_ode_eq_zero {ι : Type*} [Fintype ι] {F : ℝ → ι → ℝ} {A : ι → ι → ℝ → ℝ}
    (hA : ∀ i j, ContinuousOn (A i j) (Icc 0 1))
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (fun i => ∑ j, A i j t * F t j) t) (h0 : F 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, F t = 0 := by
  classical
  have hb : ∀ i j, ∃ M, ∀ t ∈ Icc (0 : ℝ) 1, ‖A i j t‖ ≤ M := fun i j =>
    isCompact_Icc.exists_bound_of_continuousOn (hA i j)
  choose M hM using hb
  set K : ℝ := ∑ i, ∑ j, |M i j| with hK
  have hMK : ∀ i, ∑ j, |M i j| ≤ K := fun i =>
    Finset.single_le_sum (f := fun i => ∑ j, |M i j|) (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K)
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hF t (Ico_subset_Icc_self ht)).hasDerivWithinAt) h0 ?_
  intro t ht
  have ht' := Ico_subset_Icc_self ht
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK0 (norm_nonneg _))).2 fun i => ?_
  calc ‖∑ j, A i j t * F t j‖ ≤ ∑ j, ‖A i j t * F t j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |M i j| * ‖F t‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul ((hM i j t ht').trans (le_abs_self _)) (norm_le_pi_norm (F t) j) (norm_nonneg _)
          (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖F t‖ := by rw [Finset.sum_mul]
    _ ≤ K * ‖F t‖ := mul_le_mul_of_nonneg_right (hMK i) (norm_nonneg _)

end Lightlike
