import Mathlib

/-!
# Continuity of partial derivatives of a `C¹` function of two real variables

Row G1-065 support file. If `F : ℝ × ℝ → ℝ` is `C¹` at `(r₀, θ₀)`, the partial derivatives
`r ↦ ∂_r F(r, θ₀)` and `r ↦ ∂_θ F(r, θ₀)` are continuous at `r₀`, and each is a genuine
`HasDerivAt` for `r` near `r₀`.
-/

open Filter Topology

namespace Lightlike

variable {F : ℝ × ℝ → ℝ} {r₀ θ₀ : ℝ}

/-- Near `r₀`, `F` is differentiable at `(r, θ₀)`. -/
lemma eventually_differentiableAt_slice (hF : ContDiffAt ℝ 1 F (r₀, θ₀)) :
    ∀ᶠ r in 𝓝 r₀, DifferentiableAt ℝ F (r, θ₀) := by
  have h1 : ∀ᶠ y in 𝓝 (r₀, θ₀), ContDiffAt ℝ 1 F y := hF.eventually (by simp)
  have ht : Tendsto (fun s : ℝ => (s, θ₀)) (𝓝 r₀) (𝓝 (r₀, θ₀)) :=
    (continuous_id.prodMk continuous_const).tendsto' _ _ rfl
  exact (ht.eventually h1).mono fun r hr => hr.differentiableAt (by simp)

/-- The `r`-partial derivative is `fderiv F (r, θ₀) (1, 0)` where `F` is differentiable. -/
lemma deriv_slice_fst {r : ℝ} (h : DifferentiableAt ℝ F (r, θ₀)) :
    deriv (fun s => F (s, θ₀)) r = fderiv ℝ F (r, θ₀) (1, 0) := by
  have := h.hasFDerivAt.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r θ₀))
  exact this.deriv

/-- The `θ`-partial derivative is `fderiv F (r, θ) (0, 1)` where `F` is differentiable. -/
lemma deriv_slice_snd {r θ : ℝ} (h : DifferentiableAt ℝ F (r, θ)) :
    deriv (fun t => F (r, t)) θ = fderiv ℝ F (r, θ) (0, 1) := by
  have := h.hasFDerivAt.comp_hasDerivAt θ ((hasDerivAt_const θ r).prodMk (hasDerivAt_id θ))
  exact this.deriv

/-- `r ↦ ∂_r F(r, θ₀)` is continuous at `r₀`. -/
lemma continuousAt_deriv_fst (hF : ContDiffAt ℝ 1 F (r₀, θ₀)) :
    ContinuousAt (fun r => deriv (fun s => F (s, θ₀)) r) r₀ := by
  have hc : ContinuousAt (fun r : ℝ => fderiv ℝ F (r, θ₀) (1, 0)) r₀ := by
    have h1 : ContinuousAt (fderiv ℝ F) (r₀, θ₀) := hF.continuousAt_fderiv (by simp)
    have h2 : ContinuousAt (fun r : ℝ => (r, θ₀)) r₀ := by fun_prop
    exact (ContinuousAt.comp (x := r₀) h1 h2).clm_apply continuousAt_const
  refine hc.congr ?_
  filter_upwards [eventually_differentiableAt_slice hF] with r hr
  exact (deriv_slice_fst hr).symm

/-- `r ↦ ∂_θ F(r, θ₀)` is continuous at `r₀`. -/
lemma continuousAt_deriv_snd (hF : ContDiffAt ℝ 1 F (r₀, θ₀)) :
    ContinuousAt (fun r => deriv (fun t => F (r, t)) θ₀) r₀ := by
  have hc : ContinuousAt (fun r : ℝ => fderiv ℝ F (r, θ₀) (0, 1)) r₀ := by
    have h1 : ContinuousAt (fderiv ℝ F) (r₀, θ₀) := hF.continuousAt_fderiv (by simp)
    have h2 : ContinuousAt (fun r : ℝ => (r, θ₀)) r₀ := by fun_prop
    exact (ContinuousAt.comp (x := r₀) h1 h2).clm_apply continuousAt_const
  refine hc.congr ?_
  filter_upwards [eventually_differentiableAt_slice hF] with r hr
  exact (deriv_slice_snd hr).symm

end Lightlike
