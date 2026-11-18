import Lightlike.OperatorAlgebras.Semigroup.Contraction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Cauchy estimate for the approximating contractions

For `l, μ > 0`, `t ≥ 0` and `x ∈ X`:
`‖exp (t Yos l) x - exp (t Yos μ) x‖ ≤ t ‖Yos l x - Yos μ x‖`.
The function `s ↦ exp (s Y_l) exp ((t - s) Y_μ) x` has derivative
`exp (s Y_l) exp ((t - s) Y_μ) (Y_l - Y_μ) x` (the approximants commute), of norm at most
`‖(Y_l - Y_μ) x‖`, and the mean value inequality bounds the difference of its endpoint values.

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, inequality (8) in
  the proof of Theorem 1.9.
-/

open NormedSpace Filter Topology Set
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

/-- The algebra of bounded operators is a normed `ℚ`-algebra (needed for the exponential). -/
local instance instNormedAlgebraRatCLM' {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- The derivative of `s ↦ exp (s B₁) * exp ((t - s) B₂)` for commuting `B₁ B₂`. -/
lemma hasDerivAt_exp_mul_exp (B₁ B₂ : X →L[𝕜] X) (hc : Commute B₁ B₂) (tc s : 𝕜) :
    HasDerivAt (fun u : 𝕜 => exp (u • B₁) * exp ((tc - u) • B₂))
      (exp (s • B₁) * exp ((tc - s) • B₂) * (B₁ - B₂)) s := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := 𝕜) B₁ s
  have h2 := (hasDerivAt_exp_smul_const (𝕂 := 𝕜) B₂ (tc - s)).scomp s
    ((hasDerivAt_id s).const_sub tc)
  have h3 := h1.mul h2
  refine h3.congr_deriv ?_
  have hB : Commute B₁ (exp ((tc - s) • B₂)) := (hc.smul_right _).exp_right
  have hB' : Commute (exp (s • B₁)) B₂ := (hc.smul_left _).exp_left
  simp only [neg_smul, one_smul, mul_neg]
  show exp (s • B₁) * B₁ * exp ((tc - s) • B₂) + -(exp (s • B₁) * (exp ((tc - s) • B₂) * B₂)) = _
  rw [mul_assoc (exp (s • B₁)) B₁, hB.eq]
  noncomm_ring

variable {A : X →ₗ.[𝕜] X} (h : HYHyp A)

/-- **The Cauchy estimate**: `‖exp (t Yos l) x - exp (t Yos μ) x‖ ≤ t ‖Yos l x - Yos μ x‖` for `t ≥ 0`. -/
theorem HYHyp.norm_exp_yos_sub_le {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ) {t : ℝ} (ht : 0 ≤ t)
    (x : X) :
    ‖exp (((t : ℝ) : 𝕜) • h.yos l) x - exp (((t : ℝ) : 𝕜) • h.yos μ) x‖ ≤
      t * ‖h.yos l x - h.yos μ x‖ := by
  set B₁ := h.yos l
  set B₂ := h.yos μ
  have hc : Commute B₁ B₂ := h.commute_yos hl hμ
  set tc : 𝕜 := ((t : ℝ) : 𝕜) with htc
  set P : 𝕜 → X →L[𝕜] X := fun u => exp (u • B₁) * exp ((tc - u) • B₂) with hP
  let f : 𝕜 → X := fun u => P u x
  let S : Set 𝕜 := segment ℝ (0 : 𝕜) tc
  have hSconv : Convex ℝ S := convex_segment _ _
  have hSreal : ∀ u ∈ S, ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ u = ((r : ℝ) : 𝕜) := by
    rintro u ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b * t, by positivity, ?_, ?_⟩
    · nlinarith
    · simp [htc, RCLike.real_smul_eq_coe_mul]
  have hder : ∀ u ∈ S, HasFDerivWithinAt f ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (P u ((B₁ - B₂) x))) S u := by
    intro u _
    have h1 := hasDerivAt_exp_mul_exp B₁ B₂ hc tc u
    have h2 := h1.clm_apply (hasDerivAt_const u x)
    exact ((h2.congr_deriv (by simp [hP, ContinuousLinearMap.mul_apply])).hasFDerivAt).hasFDerivWithinAt
  have hPle : ∀ u ∈ S, ‖P u‖ ≤ 1 := by
    intro u hu
    obtain ⟨r, hr0, hrt, rfl⟩ := hSreal u hu
    have e1 : (((t - r : ℝ)) : 𝕜) = tc - ((r : ℝ) : 𝕜) := by simp [htc]
    calc ‖P ((r : ℝ) : 𝕜)‖ ≤ ‖exp (((r : ℝ) : 𝕜) • B₁)‖ * ‖exp ((tc - ((r : ℝ) : 𝕜)) • B₂)‖ :=
          norm_mul_le _ _
      _ ≤ 1 * 1 := by
          rw [← e1]
          exact mul_le_mul (h.norm_exp_yos_le hl hr0) (h.norm_exp_yos_le hμ (by linarith))
            (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  have hbound : ∀ u ∈ S, ‖(1 : 𝕜 →L[𝕜] 𝕜).smulRight (P u ((B₁ - B₂) x))‖ ≤ ‖(B₁ - B₂) x‖ := by
    intro u hu
    have hd : ‖(1 : 𝕜 →L[𝕜] 𝕜).smulRight (P u ((B₁ - B₂) x))‖ ≤ ‖P u ((B₁ - B₂) x)‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
        simp [norm_smul, mul_comm]
    refine hd.trans ?_
    calc ‖P u ((B₁ - B₂) x)‖ ≤ ‖P u‖ * ‖(B₁ - B₂) x‖ := (P u).le_opNorm _
      _ ≤ 1 * ‖(B₁ - B₂) x‖ := mul_le_mul_of_nonneg_right (hPle u hu) (norm_nonneg _)
      _ = ‖(B₁ - B₂) x‖ := one_mul _
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := 𝕜) hder hbound hSconv
    (left_mem_segment ℝ (0 : 𝕜) tc) (right_mem_segment ℝ (0 : 𝕜) tc)
  have e0 : f 0 = exp (tc • B₂) x := by simp [f, hP]
  have e1 : f tc = exp (tc • B₁) x := by simp [f, hP]
  have hn : ‖tc - 0‖ = t := by simp [htc, abs_of_nonneg ht]
  rw [e0, e1, hn] at key
  simpa [ContinuousLinearMap.sub_apply, mul_comm] using key

end Lightlike.OperatorAlgebras
