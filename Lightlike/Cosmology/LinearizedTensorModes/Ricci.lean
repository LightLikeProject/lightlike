import Lightlike.Cosmology.LinearizedTensorModes.Variation

/-!
# The first variation of the Ricci tensor for tensor modes about conformal FLRW (row G1-031)

For a global smooth `a ≠ 0` and a smooth `f` depending only on `(η, z)` (`∂_x f = ∂_y f = 0`), the
variation of the Ricci tensor of `a² diag(-1, 1 + εf, 1 - εf, 1)` at `ε = 0` is
`δR_{σν} = δ_{σν} c_σ [ ½ (f'' + 2𝓗 f' - ∂_z² f) + (𝓗' + 2𝓗²) f ]`, `c = (0, 1, -1, 0)`
(`dRicci_tPert`).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Cosmology.LinearizedTensorModes

open Lightlike Lightlike.Cosmology

variable {a : ℝ → ℝ} {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}

/-- Partial derivatives of a smooth function commute. -/
theorem pd_comm' (hf : ContDiff ℝ ∞ f) (i j : Fin 4) : pd i (pd j f) = pd j (pd i f) := by
  funext x
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have e : ∀ u v : Fin 4, pd u (pd v f) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single u 1) (Pi.single v 1) := fun u v => by
    unfold pd
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  rw [e, e, (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq]

/-- **The variation of the Ricci tensor for the tensor perturbation** of the conformal FLRW metric. -/
theorem dRicci_tPert (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (hf : ContDiff ℝ ∞ f)
    (h1 : pd 1 f = fun _ => 0) (h2 : pd 2 f = fun _ => 0) (σ ν : Fin 4) :
    dRicci (confMetric a) (tPert a f) x σ ν = dl σ ν * cp σ *
      ((1 / 2) * (pd 0 (pd 0 f) x + 2 * Hf a x * pd 0 f x - pd 3 (pd 3 f) x) +
        (dH a 0 x + 2 * Hf a x ^ 2) * f x) := by
  have hdiff : ∀ t, DifferentiableAt ℝ a t := fun t => (hfa.differentiable (by simp)) t
  have c1 : ∀ j, pd 1 (pd j f) = fun _ => 0 := fun j => by
    rw [pd_comm' hf, h1]; funext y; exact pd_const _ _ _
  have c2 : ∀ j, pd 2 (pd j f) = fun _ => 0 := fun j => by
    rw [pd_comm' hf, h2]; funext y; exact pd_const _ _ _
  unfold dRicci
  simp only [pd_dChristoffel_tPert hfa hne hf,
    dChristoffel_tPert (hdiff _) (hne _) (hf.differentiable (by simp) x),
    christoffel_conf (hdiff _) (hne _), Fin.sum_univ_four]
  fin_cases σ <;> fin_cases ν <;>
    simp [cc, K1, dGd, dG, dl, cp, sgn, h1, h2, c1, c2, pd_const] <;> ring

end Lightlike.Cosmology.LinearizedTensorModes

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.dRicci_tPert := _root_.Lightlike.Cosmology.LinearizedTensorModes.dRicci_tPert
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.pd_comm' := _root_.Lightlike.Cosmology.LinearizedTensorModes.pd_comm'
