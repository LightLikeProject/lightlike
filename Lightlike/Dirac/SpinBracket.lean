import Mathlib
import Lightlike.Dirac.SpinConnection

/-!
# The spinor representation is a Lie algebra map (up to the row convention)

For a skew matrix `A` and any matrix `B`, `[spinForm A, spinForm B] = spinForm (B A - A B)`.
This is the algebraic input to the Ricci identity of the spinor covariant derivative: the curvature
`dω + ω ∧ ω` of the spinor connection `d + spinForm ω` is `spinForm` of the matrix curvature.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `spinForm` is additive in the matrix. -/
lemma spinForm_add (ρ : CliffordRep n V) (A B : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (A + B) = spinForm ρ A + spinForm ρ B := by
  simp only [spinForm, Matrix.add_apply, add_smul, Finset.sum_add_distrib, smul_add]

/-- `spinForm` commutes with real scalars. -/
lemma spinForm_smul (ρ : CliffordRep n V) (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (c • A) = c • spinForm ρ A := by
  simp only [spinForm, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, smul_comm c]

/-- `spinForm` is subtractive in the matrix. -/
lemma spinForm_sub (ρ : CliffordRep n V) (A B : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ (A - B) = spinForm ρ A - spinForm ρ B := by
  simp only [spinForm, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, smul_sub]

/-- `[spinForm A, γₖγₗ] = ∑ⱼ Aₖⱼ γⱼγₗ + ∑ⱼ Aₗⱼ γₖγⱼ` for skew `A`. -/
lemma spinForm_comm_gam_gam (ρ : CliffordRep n V) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, A i j = -A j i) (k l : Fin n) :
    spinForm ρ A * (gam ρ k * gam ρ l) - (gam ρ k * gam ρ l) * spinForm ρ A =
      ∑ j, A k j • (gam ρ j * gam ρ l) + ∑ j, A l j • (gam ρ k * gam ρ j) := by
  have h1 := spinForm_comm ρ hA k
  have h2 := spinForm_comm ρ hA l
  have e : spinForm ρ A * (gam ρ k * gam ρ l) - (gam ρ k * gam ρ l) * spinForm ρ A =
      (spinForm ρ A * gam ρ k - gam ρ k * spinForm ρ A) * gam ρ l +
        gam ρ k * (spinForm ρ A * gam ρ l - gam ρ l * spinForm ρ A) := by
    noncomm_ring
  rw [e, h1, h2, Finset.sum_mul, Finset.mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm]

/-- **Bracket of spinor connection forms.** For skew `A`,
`[spinForm A, spinForm B] = spinForm (B A - A B)`. -/
theorem spinForm_bracket (ρ : CliffordRep n V) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, A i j = -A j i) (B : Matrix (Fin n) (Fin n) ℝ) :
    spinForm ρ A * spinForm ρ B - spinForm ρ B * spinForm ρ A = spinForm ρ (B * A - A * B) := by
  have h : spinForm ρ A * spinForm ρ B - spinForm ρ B * spinForm ρ A =
      (1 / 4 : ℝ) • ∑ k, ∑ l, B k l • (spinForm ρ A * (gam ρ k * gam ρ l) -
        (gam ρ k * gam ρ l) * spinForm ρ A) := by
    have hB : spinForm ρ B = (1 / 4 : ℝ) • ∑ k, ∑ l, B k l • (gam ρ k * gam ρ l) := rfl
    rw [hB]
    simp only [smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
      ← smul_sub, ← Finset.sum_sub_distrib]
  rw [h]
  simp only [spinForm_comm_gam_gam ρ hA]
  have hR : spinForm ρ (B * A - A * B) =
      (1 / 4 : ℝ) • ∑ x, ∑ x_1, (∑ m, B x m * A m x_1 - ∑ m, A x m * B m x_1) •
        (gam ρ x * gam ρ x_1) := by
    simp only [spinForm, Matrix.sub_apply, Matrix.mul_apply]
  rw [hR]
  congr 1
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, sub_smul]
  set G : Fin n → Fin n → V →L[ℝ] V := fun a b => gam ρ a * gam ρ b with hG
  have e1 : ∑ x, ∑ x_1, ∑ x_2, (B x x_1 * A x x_2) • G x_2 x_1 =
      - ∑ x, ∑ x_1, (∑ m, A x m * B m x_1) • G x x_1 := by
    have s3 : ∀ F : Fin n → Fin n → Fin n → V →L[ℝ] V,
        ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
      intro F
      rw [Finset.sum_comm]
      refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
      exact Finset.sum_comm
    rw [s3, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_smul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hA a c, ← neg_smul]
    congr 1
    ring
  have e2 : ∑ x, ∑ x_1, ∑ x_2, (B x x_1 * A x_1 x_2) • G x x_2 =
      ∑ x, ∑ x_1, (∑ m, B x m * A m x_1) • G x x_1 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_smul]
  rw [e1, e2]
  simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

end Lightlike.Dirac
