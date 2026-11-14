module

public import Lightlike.Lorentz.LimitFormula
public import Lightlike.Lorentz.SphericalPlancherelTests

/-!
# Trust checks for the limit formula (milestone HA2)

1. **Non-vacuity.** The function `testLF X = testF(Σ |X_ij|²)` (the bump `testF` of the radial
   Plancherel checks, composed with the squared Hilbert–Schmidt norm) is smooth, compactly
   supported and invariant under `SU(2)` conjugation, with `testLF 1 = 1`. So `limit_formula`
   applies to it and gives the nonzero value `-8π` (`limit_formula_testLF`).
2. **Wrong input gives a different answer.** With `-4π` in place of `-8π` the formula fails, already
   for `testLF` (`limit_formula_wrong_constant`).

The numerical cross-check `scripts/lorentz/limit_formula_check.py` evaluates the orbital
integrals of `testLF` by quadrature and their Laplacian by finite differences. As a control, a
function that is not `SU(2)`-conjugation invariant violates the formula there.
-/

@[expose] public section

open MeasureTheory Complex
open scoped Matrix ContDiff

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-- The squared Hilbert–Schmidt norm `Σᵢⱼ |X_ij|²`. -/
noncomputable def hsNormSq (X : P2) : ℝ := ∑ i, ∑ j, ‖X i j‖ ^ 2

/-- The squared Hilbert–Schmidt norm is smooth. -/
lemma contDiff_hsNormSq : ContDiff ℝ ∞ hsNormSq :=
  ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_norm_sq ℝ).comp (contDiff_apply_apply ℝ i j)

/-- `Σᵢⱼ |Y_ij|² = tr(Y Y*)`. -/
lemma hsNormSq_eq_trace (Y : M2) : (hsNormSq Y : ℂ) = Matrix.trace (Y * star Y) := by
  simp only [hsNormSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply,
    Complex.star_def, Complex.mul_conj', ofReal_sum, ofReal_pow]

/-- The squared Hilbert–Schmidt norm is invariant under unitary conjugation. -/
lemma hsNormSq_conj {k : M2} (hk : k ∈ Matrix.unitaryGroup (Fin 2) ℂ) (X : M2) :
    hsNormSq (k * X * star k) = hsNormSq X := by
  have hk' : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have h : Matrix.trace (k * X * star k * star (k * X * star k)) = Matrix.trace (X * star X) := by
    rw [star_mul, star_mul, star_star, show k * X * star k * (k * (star X * star k)) =
      k * (X * star X) * star k by
        rw [show k * X * star k * (k * (star X * star k)) =
          k * X * (star k * k) * (star X * star k) by simp only [Matrix.mul_assoc], hk']
        simp only [Matrix.mul_one, Matrix.mul_assoc],
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk', Matrix.one_mul]
  exact_mod_cast (hsNormSq_eq_trace _).trans (h.trans (hsNormSq_eq_trace X).symm)

/-- An entry is bounded by the Hilbert–Schmidt norm: `|X_ij|² ≤ Σ |X_kl|²`. -/
lemma sq_norm_apply_le_hsNormSq (X : P2) (i j : Fin 2) : ‖X i j‖ ^ 2 ≤ hsNormSq X :=
  calc ‖X i j‖ ^ 2 ≤ ∑ j', ‖X i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖X i j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ hsNormSq X :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖X i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

/-- The test function `testLF X = testF(Σ |X_ij|²)`. -/
noncomputable def testLF (X : P2) : ℂ := testF (hsNormSq X)

/-- `testLF` is smooth. -/
lemma contDiff_testLF : ContDiff ℝ 2 testLF :=
  (contDiff_testF.comp contDiff_hsNormSq).of_le (WithTop.coe_le_coe.mpr le_top)

/-- `testLF` vanishes outside the ball of radius `2` (in the sup norm). -/
lemma hasCompactSupport_testLF : HasCompactSupport testLF := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : P2) 2) fun X hX => ?_
  by_contra h
  have hs : hsNormSq X ∈ Function.support testBump := by
    simpa [testLF, testF] using h
  rw [testBump.support_eq, Real.ball_eq_Ioo] at hs
  have h3 : hsNormSq X < 3 := by
    have : testBump.rOut = 1 := rfl
    linarith [hs.2]
  refine hX (mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun j => ?_))
  nlinarith [sq_norm_apply_le_hsNormSq X i j, norm_nonneg (X i j)]

/-- `testLF` is invariant under conjugation by `SU(2)`. -/
lemma isSU2ConjInvariant_testLF : IsSU2ConjInvariant testLF := fun k hk X => by
  simp only [testLF, hsNormSq_conj (Matrix.mem_specialUnitaryGroup_iff.mp hk).1 X]

/-- `testLF 1 = 1`. -/
lemma testLF_one : testLF (mat2 1 0 0 1) = 1 := by
  have h : hsNormSq (mat2 1 0 0 1) = 2 := by
    simp [hsNormSq, Fin.sum_univ_two]; norm_num
  rw [testLF, h, testF_two]

/-- **Non-vacuity**: for `testLF` the limit formula gives the nonzero value `-8π`. -/
theorem limit_formula_testLF :
    deriv (deriv fun t : ℝ => orbInt testLF (cexp t)) 0 +
      deriv (deriv fun t : ℝ => orbInt testLF (cexp (t * I))) 0 = -(8 * Real.pi) := by
  rw [limit_formula contDiff_testLF hasCompactSupport_testLF isSU2ConjInvariant_testLF, testLF_one,
    mul_one]

/-- **Wrong constant**: the limit formula with `-4π` in place of `-8π` is false. -/
theorem limit_formula_wrong_constant :
    ¬ ∀ F : P2 → ℂ, ContDiff ℝ 2 F → HasCompactSupport F → IsSU2ConjInvariant F →
      deriv (deriv fun t : ℝ => orbInt F (cexp t)) 0 +
        deriv (deriv fun t : ℝ => orbInt F (cexp (t * I))) 0 =
        -(4 * Real.pi) * F (mat2 1 0 0 1) := by
  intro h
  have h1 := h testLF contDiff_testLF hasCompactSupport_testLF isSU2ConjInvariant_testLF
  rw [limit_formula_testLF, testLF_one, mul_one] at h1
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  exact hπ (by linear_combination -h1 / 4)

end Lightlike.Lorentz
