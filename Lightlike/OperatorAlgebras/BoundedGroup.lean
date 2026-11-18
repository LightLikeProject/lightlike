import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Lightlike.OperatorAlgebras.UnitaryGroup

/-!
# The unitary group of a bounded self-adjoint operator

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). For a bounded operator `B` on a complex
Hilbert space, `bdU B s = exp (s • (i B))` (Mathlib's exponential of a bounded operator). If `B` is
self-adjoint, `bdU B s` is unitary, `bdU B (s + t) = bdU B s * bdU B t`, and for two commuting bounded
self-adjoint operators `B, B'` the strong Cauchy estimate
`‖bdU B t y - bdU B' t y‖ ≤ |t| ‖(B - B') y‖` holds: it is the mean value inequality for
`s ↦ bdU B s (bdU B' (t - s) y)`.
-/

open scoped InnerProductSpace
open NormedSpace

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `exp (i s B)` for a bounded operator `B`. -/
noncomputable def bdU (B : H →L[ℂ] H) (s : ℝ) : H →L[ℂ] H := exp (s • (Complex.I • B))

lemma bdU_zero (B : H →L[ℂ] H) : bdU B 0 = 1 := by simp [bdU]

lemma bdU_add (B : H →L[ℂ] H) (s t : ℝ) : bdU B (s + t) = bdU B s * bdU B t := by
  unfold bdU
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℂ) (𝔸 := H →L[ℂ] H)
    ((Commute.refl _).smul_left s |>.smul_right t)
    ((expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)

lemma bdU_star {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (s : ℝ) : star (bdU B s) = bdU B (-s) := by
  unfold bdU
  rw [star_exp]
  congr 1
  rw [star_smul, star_smul, hB.star_eq]
  simp [neg_smul, smul_neg]

lemma bdU_neg_mul {B : H →L[ℂ] H} (s : ℝ) : bdU B (-s) * bdU B s = 1 := by
  rw [← bdU_add]; simp [bdU_zero]

lemma bdU_mul_neg {B : H →L[ℂ] H} (s : ℝ) : bdU B s * bdU B (-s) = 1 := by
  rw [← bdU_add]; simp [bdU_zero]

/-- `exp (i s B)` is an isometry for a self-adjoint `B`. -/
lemma bdU_norm {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (s : ℝ) (y : H) : ‖bdU B s y‖ = ‖y‖ := by
  have h1 : (ContinuousLinearMap.adjoint (bdU B s)) (bdU B s y) = y := by
    have : ContinuousLinearMap.adjoint (bdU B s) = bdU B (-s) := by
      rw [← bdU_star hB]; rfl
    rw [this]
    have := congrArg (fun T : H →L[ℂ] H => T y) (bdU_neg_mul (B := B) s)
    simpa using this
  have h2 : ⟪bdU B s y, bdU B s y⟫_ℂ = ⟪y, y⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left (bdU B s) y (bdU B s y)
    rw [h1] at this
    exact this.symm
  have h3 : ‖bdU B s y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

end Lightlike.OperatorAlgebras
