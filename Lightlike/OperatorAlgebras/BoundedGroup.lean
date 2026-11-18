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

/-- Evaluation at a vector, as a real-linear continuous map. -/
noncomputable def evalAt (y : H) : (H →L[ℂ] H) →L[ℝ] H :=
  ((ContinuousLinearMap.apply ℂ H y).restrictScalars ℝ)

lemma evalAt_apply (y : H) (T : H →L[ℂ] H) : evalAt y T = T y := rfl

/-- The derivative of `r ↦ bdU B r y`. -/
lemma hasDerivAt_bdU_apply (B : H →L[ℂ] H) (y : H) (s : ℝ) :
    HasDerivAt (fun r : ℝ => bdU B r y) (bdU B s (Complex.I • B y)) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (Complex.I • B) s
  have h2 := (evalAt y).hasFDerivAt.comp_hasDerivAt s h
  convert h2 using 1
  simp [evalAt_apply, bdU, Function.comp_def]
  rfl

/-- **The strong Cauchy estimate** for two commuting bounded self-adjoint operators:
`‖exp (i t B) y - exp (i t B') y‖ ≤ |t| ‖(B - B') y‖`. -/
theorem bdU_cauchy {B B' : H →L[ℂ] H} (hB : IsSelfAdjoint B) (hB' : IsSelfAdjoint B')
    (hc : Commute B B') (t : ℝ) (y : H) :
    ‖bdU B t y - bdU B' t y‖ ≤ |t| * ‖(B - B') y‖ := by
  set X : H →L[ℂ] H := Complex.I • B with hX
  set Y : H →L[ℂ] H := Complex.I • B' with hY
  have hXY : Commute X Y := (hc.smul_left Complex.I).smul_right Complex.I
  -- the derivative in the algebra
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => bdU B r * bdU B' (t - r))
      (bdU B s * X * bdU B' (t - s) - bdU B s * (bdU B' (t - s) * Y)) s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => bdU B r) (bdU B s * X) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
    have h2 : HasDerivAt (fun r : ℝ => bdU B' (t - r)) ((-1 : ℝ) • (bdU B' (t - s) * Y)) s := by
      have := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
      exact this
    have := h1.mul h2
    convert this using 1
    simp [sub_eq_add_neg]
  have hf : ∀ s : ℝ, HasDerivAt (fun r : ℝ => bdU B r (bdU B' (t - r) y))
      (evalAt y (bdU B s * X * bdU B' (t - s) - bdU B s * (bdU B' (t - s) * Y))) s := fun s =>
    (evalAt y).hasFDerivAt.comp_hasDerivAt s (hd s)
  have hbound : ∀ s : ℝ, ‖evalAt y (bdU B s * X * bdU B' (t - s) - bdU B s * (bdU B' (t - s) * Y))‖ ≤
      ‖(B - B') y‖ := by
    intro s
    have hcomm : Commute X (bdU B' (t - s)) := (hXY.smul_right (t - s)).exp_right
    have e : bdU B s * X * bdU B' (t - s) - bdU B s * (bdU B' (t - s) * Y) =
        bdU B s * (bdU B' (t - s) * (X - Y)) := by
      rw [mul_assoc, hcomm.eq, mul_sub, mul_sub]
    rw [evalAt_apply, e]
    simp only [ContinuousLinearMap.mul_apply]
    rw [bdU_norm hB, bdU_norm hB']
    have : (X - Y) y = Complex.I • ((B - B') y) := by
      simp [hX, hY, smul_sub]
    rw [this, norm_smul, Complex.norm_I, one_mul]
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun r : ℝ => bdU B r (bdU B' (t - r) y)) (s := Set.univ) (x := 0) (y := t)
    (fun s _ => (hf s).hasDerivWithinAt) (fun s _ => hbound s) convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simp only [bdU_zero, sub_self, sub_zero, ContinuousLinearMap.one_apply, ContinuousLinearMap.sub_apply,
    Real.norm_eq_abs, mul_comm] at this ⊢
  exact this

end Lightlike.OperatorAlgebras
