import Lightlike.Rows.G1_031.Ricci

/-!
# Ricci and scalar curvature of the conformal FLRW background (row G1-031)

For a global smooth `a ≠ 0`, the metric `a(η)² diag(-1, 1, 1, 1)` has
`R_{00} = -3 𝓗'`, `R_{ii} = 𝓗' + 2𝓗²` (`ricci_conf`) and `R = 6 (𝓗' + 𝓗²) / a²` (`scalar_conf`),
where `𝓗 = a'/a` is `Hf a` and `𝓗' = dH a 0 x`.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Rows.G1_031

open Lightlike Lightlike.Cosmology

variable {a : ℝ → ℝ} {x : Fin 4 → ℝ}

/-- `∂_μ Γ^i_{jk}` of the conformal FLRW metric: `cc i j k · ∂_μ 𝓗`. -/
theorem pd_christoffel_conf (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (μ i j k : Fin 4) :
    pd μ (christoffel (confMetric a) i j k) x = cc i j k * dH a μ x := by
  have hdiff : ∀ t, DifferentiableAt ℝ a t := fun t => (hfa.differentiable (by simp)) t
  have hdiff' : ∀ t, DifferentiableAt ℝ (deriv a) t :=
    fun t => (((contDiff_infty_iff_deriv.mp hfa).2).differentiable (by simp)) t
  have : christoffel (confMetric a) i j k = fun y => cc i j k * Hf a y :=
    funext fun y => christoffel_conf (hdiff _) (hne _) i j k
  rw [this]
  have h := ((HasPd.const (j := μ) (x := x) (cc i j k)).mul
    (hasPd_Hf (j := μ) (hdiff (x 0)) (hdiff' (x 0)) (hne (x 0)))).2
  rw [h]; ring

/-- **The Ricci tensor of the conformal FLRW background**: `R_{00} = -3𝓗'`, `R_{ii} = 𝓗' + 2𝓗²`. -/
theorem ricci_conf (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (σ ν : Fin 4) :
    ricci (confMetric a) σ ν x =
      dl σ ν * (if σ = 0 then -3 * dH a 0 x else dH a 0 x + 2 * Hf a x ^ 2) := by
  have hdiff : ∀ t, DifferentiableAt ℝ a t := fun t => (hfa.differentiable (by simp)) t
  unfold ricci riemann
  simp only [pd_christoffel_conf hfa hne, christoffel_conf (hdiff _) (hne _), Fin.sum_univ_four]
  fin_cases σ <;> fin_cases ν <;> simp [cc, dl, sgn, dH] <;> ring

/-- **The scalar curvature of the conformal FLRW background**: `R = 6 (𝓗' + 𝓗²) / a²`. -/
theorem scalar_conf (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) :
    scalarCurvature (confMetric a) x = 6 * (dH a 0 x + Hf a x ^ 2) / a (x 0) ^ 2 := by
  have hpos := hne (x 0)
  have hd : ∀ μ, sgn μ * a (x 0) ^ 2 ≠ 0 := by
    intro μ; unfold sgn; split_ifs <;> simp [hpos]
  have hinv : (confMetric a x)⁻¹ = Matrix.diagonal (fun μ => (sgn μ * a (x 0) ^ 2)⁻¹) :=
    inv_diag' _ hd
  unfold scalarCurvature
  rw [hinv]
  simp only [ricci_conf hfa hne, Fin.sum_univ_four, Matrix.diagonal_apply]
  simp [dl, sgn]
  field_simp
  ring

end Lightlike.Rows.G1_031
