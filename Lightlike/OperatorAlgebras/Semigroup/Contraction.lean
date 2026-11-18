import Lightlike.OperatorAlgebras.Semigroup.Yosida
import Lightlike.OperatorAlgebras.Semigroup.ExpBound
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The approximating contractions `exp (t Yos l)`

For `A` satisfying `HYHyp` and `l > 0` the Yosida approximant `Yos l = l² R l - l` is a bounded
operator. The operators `exp (t Yos l)`, `t ≥ 0`, are contractions
(`HYHyp.norm_exp_yos_le`), since `exp (t (l² R - l)) = e^{-t l} exp (t l² R)` with `‖exp (t l² R)‖ ≤ e^{t l}`.
Two approximants commute (`HYHyp.commute_yos`).

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, proof of Theorem 1.9.
-/

open NormedSpace Filter Topology
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

/-- The algebra of bounded operators is a normed `ℚ`-algebra (needed for the exponential). -/
local instance instNormedAlgebraRatCLM {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} (h : HYHyp A)

/-- Two Yosida approximants commute. -/
lemma HYHyp.commute_yos {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ) : Commute (h.yos l) (h.yos μ) := by
  have hc : Commute (h.res l) (h.res μ) := h.res_comm hl hμ
  unfold HYHyp.yos
  refine Commute.sub_left (Commute.sub_right ?_ ?_) (Commute.sub_right ?_ ?_)
  · exact (hc.smul_left _).smul_right _
  · exact ((Commute.one_right _).smul_right _).smul_left _ |>.symm.symm
  · exact (Commute.one_left _).smul_left _ |>.smul_right _
  · exact ((Commute.one_left _).smul_left _).smul_right _

/-- `‖exp (t Yos l)‖ ≤ 1` for `t ≥ 0`: the approximating semigroups are contractions. -/
theorem HYHyp.norm_exp_yos_le {l : ℝ} (hl : 0 < l) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (((t : ℝ) : 𝕜) • h.yos l)‖ ≤ 1 := by
  set R := h.res l with hRdef
  have hR : ‖R‖ ≤ l⁻¹ := h.res_norm_le hl
  set a : X →L[𝕜] X := ((t * l ^ 2 : ℝ) : 𝕜) • R with ha
  set c : 𝕜 := ((-(t * l) : ℝ) : 𝕜) with hc
  set b : X →L[𝕜] X := c • (1 : X →L[𝕜] X) with hb
  have e : ((t : ℝ) : 𝕜) • h.yos l = a + b := by
    simp only [HYHyp.yos, ha, hb, hc]
    push_cast
    module
  have hab : Commute a b := (Commute.one_right a).smul_right c
  rw [e, exp_add_of_commute hab]
  have h1 : ‖(1 : X →L[𝕜] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hexpa : ‖exp a‖ ≤ Real.exp (t * l) := by
    refine (norm_exp_le_exp_norm (𝕜 := 𝕜) h1 a).trans (Real.exp_le_exp.2 ?_)
    calc ‖a‖ ≤ ‖((t * l ^ 2 : ℝ) : 𝕜)‖ * ‖R‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = (t * l ^ 2) * ‖R‖ := by
          rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
      _ ≤ (t * l ^ 2) * l⁻¹ := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = t * l := by field_simp
  have hexpb : ‖exp b‖ ≤ Real.exp (-(t * l)) := by
    have e1 : b = algebraMap 𝕜 (X →L[𝕜] X) c := by
      rw [Algebra.algebraMap_eq_smul_one]
    have e2 : exp b = algebraMap 𝕜 (X →L[𝕜] X) (exp c) := by
      rw [e1, algebraMap_exp_comm]
    have e3 : exp c = ((Real.exp (-(t * l)) : ℝ) : 𝕜) := by
      have := NormedSpace.map_exp (algebraMap ℝ 𝕜) (RCLike.continuous_ofReal) (-(t * l))
      rw [hc]
      simpa [Real.exp_eq_exp_ℝ] using this.symm
    rw [e2, e3, Algebra.algebraMap_eq_smul_one]
    calc ‖((Real.exp (-(t * l)) : ℝ) : 𝕜) • (1 : X →L[𝕜] X)‖
        ≤ ‖((Real.exp (-(t * l)) : ℝ) : 𝕜)‖ * ‖(1 : X →L[𝕜] X)‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ Real.exp (-(t * l)) * 1 := by
          rw [RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-(t * l)) := mul_one _
  calc ‖exp a * exp b‖ ≤ ‖exp a‖ * ‖exp b‖ := norm_mul_le _ _
    _ ≤ Real.exp (t * l) * Real.exp (-(t * l)) :=
        mul_le_mul hexpa hexpb (norm_nonneg _) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end Lightlike.OperatorAlgebras
