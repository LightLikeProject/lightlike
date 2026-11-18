import Lightlike.OperatorAlgebras.Semigroup.Contraction
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Mean value estimate for `exp (t B) x`

For a bounded operator `B` on a Banach space and `x, w ∈ X`, the function
`s ↦ exp (s B) x - s w` has derivative `exp (s B) (B x) - w`, so if
`‖exp (r B) (B x) - w‖ ≤ C` for `0 ≤ r ≤ t` then `‖exp (t B) x - x - t w‖ ≤ C t`
(`norm_exp_sub_smul_le`). With `w = 0` this bounds `‖exp (t B) x - x‖` by `t ‖B x‖` for contractions;
with `w = B x` it bounds the difference quotient of the approximating semigroups.
-/

open NormedSpace Filter Topology Set

noncomputable section

namespace Lightlike.OperatorAlgebras

/-- The algebra of bounded operators is a normed `ℚ`-algebra (needed for the exponential). -/
local instance instNormedAlgebraRatCLM'' {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X]

/-- **Mean value estimate**: `‖exp (t B) x - x - t w‖ ≤ C t` if `‖exp (r B) (B x) - w‖ ≤ C` for
`0 ≤ r ≤ t`. -/
theorem norm_exp_sub_smul_le (B : X →L[𝕜] X) (x w : X) {t : ℝ} (ht : 0 ≤ t) {C : ℝ}
    (hC : ∀ r : ℝ, 0 ≤ r → r ≤ t → ‖exp (((r : ℝ) : 𝕜) • B) (B x) - w‖ ≤ C) :
    ‖(exp (((t : ℝ) : 𝕜) • B) x - x) - ((t : ℝ) : 𝕜) • w‖ ≤ C * t := by
  set tc : 𝕜 := ((t : ℝ) : 𝕜) with htc
  let f : 𝕜 → X := fun u => exp (u • B) x - u • w
  let S : Set 𝕜 := segment ℝ (0 : 𝕜) tc
  have hSconv : Convex ℝ S := convex_segment _ _
  have hSreal : ∀ u ∈ S, ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ u = ((r : ℝ) : 𝕜) := by
    rintro u ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨b * t, by positivity, ?_, ?_⟩
    · nlinarith
    · simp [htc, RCLike.real_smul_eq_coe_mul]
  have hder : ∀ u ∈ S, HasFDerivWithinAt f
      ((1 : 𝕜 →L[𝕜] 𝕜).smulRight (exp (u • B) (B x) - w)) S u := by
    intro u _
    have h1 := hasDerivAt_exp_smul_const (𝕂 := 𝕜) B u
    have h2 := h1.clm_apply (hasDerivAt_const u x)
    have h3 := h2.sub ((hasDerivAt_id u).smul_const w)
    refine ((h3.congr_deriv ?_).hasFDerivAt).hasFDerivWithinAt
    have hcomm : Commute B (exp (u • B)) := (Commute.refl B).smul_right u |>.exp_right
    simp [hcomm.eq, ContinuousLinearMap.mul_apply]
  have hbound : ∀ u ∈ S, ‖(1 : 𝕜 →L[𝕜] 𝕜).smulRight (exp (u • B) (B x) - w)‖ ≤ C := by
    intro u hu
    obtain ⟨r, hr0, hrt, rfl⟩ := hSreal u hu
    have hd : ‖(1 : 𝕜 →L[𝕜] 𝕜).smulRight (exp (((r : ℝ) : 𝕜) • B) (B x) - w)‖ ≤
        ‖exp (((r : ℝ) : 𝕜) • B) (B x) - w‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => by
        simp [norm_smul, mul_comm]
    exact hd.trans (hC r hr0 hrt)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := 𝕜) hder hbound hSconv
    (left_mem_segment ℝ (0 : 𝕜) tc) (right_mem_segment ℝ (0 : 𝕜) tc)
  have hn : ‖tc - 0‖ = t := by simp [htc, abs_of_nonneg ht]
  rw [hn] at key
  have key' : ‖(exp (tc • B) x - tc • w) - x‖ ≤ C * t := by simpa [f] using key
  rwa [sub_right_comm] at key'

end Lightlike.OperatorAlgebras
