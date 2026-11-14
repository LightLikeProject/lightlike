module

public import Lightlike.Lorentz.SU2Average

/-!
# Checks of the `SU(2)` conjugation average

Two checks of `su2Avg` from `Lightlike.Lorentz.SU2Average`.

* **Wrong-model test.** The entry `F X = X₀₁` is continuous but not invariant under conjugation
  by `SU(2)`. Its average vanishes at `E = [[0, 1], [0, 0]]` although `F E = 1`
  (`su2Avg_entry01_eMat`). So `su2Avg` really changes a non-invariant function, while
  `su2Avg_eq_self` says that it fixes invariant ones. The reason is that `diag(i, -i)` conjugates
  `E` to `-E`, and the average of a linear function is linear.
* **Non-vacuity.** A smooth bump `b` on the arrays meets the hypotheses of
  `contDiff_su2Avg`, `hasCompactSupport_su2Avg` and `isSU2ConjInvariant_su2Avg`. Its average
  takes the value `1` at the identity (`bumpF_nonvacuous`), so the averaged function used in the
  Plancherel trace is not identically zero.
-/

@[expose] public section

open MeasureTheory Complex Metric
open scoped Matrix ComplexConjugate ContDiff

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-- `diag(i, -i)` lies in `SU(2)`. -/
lemma diagI_mem : !![I, 0; 0, -I] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  · simp [Matrix.det_fin_two]

/-- Conjugation by `diag(i, -i)` sends `E` to `-E`. -/
lemma diagI_conj_eMat :
    !![I, 0; 0, -I] * Matrix.of eMat * star !![I, 0; 0, -I] = -Matrix.of eMat := by
  have he : Matrix.of eMat = !![0, 1; 0, 0] := rfl
  rw [he]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]

/-- The `(0, 1)` entry of an array: continuous, linear, and not conjugation-invariant. -/
def entry01 (X : P2) : ℂ := X 0 1

/-- The average of the linear function `entry01` is odd. -/
lemma su2Avg_entry01_neg (X : P2) : su2Avg entry01 (-X) = -su2Avg entry01 X := by
  have hc : ∀ v, conjV v (-X) = -conjV v X := fun v => by
    ext i j
    simp [conjV, mm3_apply, Finset.sum_neg_distrib]
    ring
  have h : ∀ v, (avgWeight v : ℂ) * entry01 (conjV v (-X)) =
      -((avgWeight v : ℂ) * entry01 (conjV v X)) := fun v => by
    rw [hc, entry01, entry01, Pi.neg_apply, Pi.neg_apply, mul_neg]
  simp only [su2Avg, h, integral_neg, mul_neg]

/-- **Wrong-model test.** The entry `X₀₁` is not conjugation-invariant, and its average vanishes
at `E = [[0, 1], [0, 0]]` although its value there is `1`. -/
theorem su2Avg_entry01_eMat : su2Avg entry01 eMat = 0 ∧ entry01 eMat = 1 := by
  refine ⟨?_, rfl⟩
  have hF : Continuous entry01 := by unfold entry01; fun_prop
  have hinv := isSU2ConjInvariant_su2Avg hF _ diagI_mem (Matrix.of eMat)
  rw [diagI_conj_eMat] at hinv
  change su2Avg entry01 (-eMat) = su2Avg entry01 eMat at hinv
  rw [su2Avg_entry01_neg] at hinv
  linear_combination (-1 / 2 : ℂ) * hinv

/-- A smooth bump on the arrays: `1` on the closed ball of radius `2`, supported in the open
ball of radius `3`. -/
noncomputable def arrBump : ContDiffBump (0 : P2) := ⟨2, 3, by norm_num, by norm_num⟩

/-- The bump as a complex-valued function. -/
noncomputable def bumpF (X : P2) : ℂ := (arrBump X : ℂ)

/-- **Non-vacuity.** The bump satisfies every hypothesis of the main theorems of
`SU2Average`, and its average is `1` at the identity. -/
theorem bumpF_nonvacuous :
    ContDiff ℝ ∞ (su2Avg bumpF) ∧ HasCompactSupport (su2Avg bumpF) ∧
      IsSU2ConjInvariant (su2Avg bumpF) ∧ su2Avg bumpF (mat2 1 0 0 1) = 1 := by
  have hs : ContDiff ℝ ∞ bumpF := ofRealCLM.contDiff.comp arrBump.contDiff
  have hc : HasCompactSupport bumpF := arrBump.hasCompactSupport.comp_left ofReal_zero
  refine ⟨contDiff_su2Avg hs, hasCompactSupport_su2Avg hc,
    isSU2ConjInvariant_su2Avg hs.continuous, ?_⟩
  rw [su2Avg_one, bumpF, arrBump.one_of_mem_closedBall, ofReal_one]
  rw [mem_closedBall, dist_zero_right]
  have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have h0 : ‖(0 : ℂ)‖ ≤ 1 := by simp
  have hb : (arrBump.rIn : ℝ) = 2 := rfl
  rw [hb]
  exact (norm_mat2_le zero_le_one h1 h0 h0 h1).trans (by norm_num)

end Lightlike.Lorentz
