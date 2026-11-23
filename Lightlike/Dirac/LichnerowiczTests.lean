import Mathlib
import Lightlike.Dirac.Lichnerowicz
import Lightlike.Dirac.Flat

/-!
# Trust checks for the curvature term of the Lichnerowicz formula

* The unit 2-sphere: the frame curvature array `Rᵢⱼₖₗ = δᵢₗδⱼₖ − δᵢₖδⱼₗ` on `Fin 2` has the
  Riemann symmetries and scalar curvature `s = ∑ Rᵢⱼⱼᵢ = 2` (`sphereR_scalar`).
* Non-vacuity: the Clifford generators `γᵢ = ι(eᵢ)` of `Cl(ℝ², -‖·‖²)` satisfy the hypothesis of
  `curvatureTerm_eq`, which therefore gives `curvatureTerm = (1/2) • 1` on the sphere
  (`curvatureTerm_sphere`).
* Wrong-constant control: with `½` in place of `¼` in the spinor curvature the term would be
  `s/2 = 1`, which is not `s/4 = 1/2` (`sphere_half_formula_fails`).
-/

open CliffordAlgebra

namespace Lightlike.Dirac

/-- Frame curvature of the unit 2-sphere, `Rᵢⱼₖₗ = δᵢₗδⱼₖ − δᵢₖδⱼₗ`. -/
def sphereR (i j k l : Fin 2) : ℝ :=
  (if i = l then 1 else 0) * (if j = k then 1 else 0)
    - (if i = k then 1 else 0) * (if j = l then 1 else 0)

lemma sphereR_antisymm (i j k l : Fin 2) : sphereR i j k l = - sphereR j i k l := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [sphereR]

lemma sphereR_pair (i j k l : Fin 2) : sphereR i j k l = sphereR k l i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [sphereR]

lemma sphereR_bianchi (i j k l : Fin 2) :
    sphereR i j k l + sphereR j k i l + sphereR k i j l = 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp [sphereR]

/-- The scalar curvature `∑ Rᵢⱼⱼᵢ` of the unit 2-sphere is `2`. -/
lemma sphereR_scalar : ∑ i, ∑ j, sphereR i j j i = 2 := by
  simp [sphereR]
  norm_num

/-- Clifford generators of `Cl(ℝ², -‖·‖²)`. -/
noncomputable def cliffGen (i : Fin 2) : CliffordAlgebra (Qneg 2) := ι (Qneg 2) (e i)

lemma polar_Qneg (a b : E 2) : QuadraticMap.polar (Qneg 2) a b = -2 * inner ℝ a b := by
  rw [QuadraticMap.polar, Qneg_apply, Qneg_apply, Qneg_apply, norm_add_sq_real]
  ring

lemma cliffGen_anticomm (j k : Fin 2) :
    cliffGen j * cliffGen k + cliffGen k * cliffGen j
      = (if j = k then (-2 : ℝ) else 0) • (1 : CliffordAlgebra (Qneg 2)) := by
  have h : -2 * inner ℝ (e j) (e k) = (if j = k then (-2 : ℝ) else 0) := by
    by_cases hjk : j = k <;> simp [e, hjk, EuclideanSpace.inner_single_left]
  unfold cliffGen
  rw [ι_mul_ι_add_swap, polar_Qneg, h, Algebra.algebraMap_eq_smul_one]

/-- Non-vacuity: on the unit 2-sphere the curvature term is `(1/2) • 1 = (s/4) • 1`. -/
lemma curvatureTerm_sphere :
    curvatureTerm cliffGen sphereR = (1 / 2 : ℝ) • (1 : CliffordAlgebra (Qneg 2)) := by
  rw [curvatureTerm_eq cliffGen sphereR cliffGen_anticomm sphereR_antisymm sphereR_pair
    sphereR_bianchi, sphereR_scalar]
  norm_num

/-- Wrong-constant control: `½` in place of `¼` in the spinor curvature would give `s/2 = 1`,
which differs from the true value `s/4 = 1/2`.  Stated on the scalars `s/2` and `s/4`. -/
lemma sphere_half_formula_fails :
    (1 / 2 : ℝ) * ∑ i, ∑ j, sphereR i j j i ≠ (1 / 4 : ℝ) * ∑ i, ∑ j, sphereR i j j i := by
  rw [sphereR_scalar]
  norm_num

end Lightlike.Dirac
