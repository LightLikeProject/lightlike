import Lightlike.Cosmology.LinearizedTensorModes.Curvature

/-!
# The linearized Einstein tensor for tensor modes about conformal FLRW (row G1-031)

`dScalar_tPert` : the first variation of the scalar curvature vanishes for a tensor (traceless,
`R_{11} = R_{22}`) perturbation.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Rows.G1_031

open Lightlike Lightlike.Cosmology

variable {a : ℝ → ℝ} {f : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ}

/-- **The first variation of the scalar curvature vanishes for the tensor perturbation**:
`∑ (-(g⁻¹ h g⁻¹)^{σν} R_{σν} + g^{σν} δR_{σν}) = 0`. -/
theorem dScalar_tPert (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (hf : ContDiff ℝ ∞ f)
    (h1 : pd 1 f = fun _ => 0) (h2 : pd 2 f = fun _ => 0) :
    ∑ σ, ∑ ν, (-((confMetric a x)⁻¹ * tPert a f x * (confMetric a x)⁻¹) σ ν *
        ricci (confMetric a) σ ν x + (confMetric a x)⁻¹ σ ν * dRicci (confMetric a) (tPert a f) x σ ν)
      = 0 := by
  have hpos := hne (x 0)
  have hd : ∀ μ, sgn μ * a (x 0) ^ 2 ≠ 0 := by
    intro μ; unfold sgn; split_ifs <;> simp [hpos]
  have hinv : (confMetric a x)⁻¹ = Matrix.diagonal (fun μ => (sgn μ * a (x 0) ^ 2)⁻¹) :=
    inv_diag' _ hd
  have hh : tPert a f x = Matrix.diagonal fun μ => a (x 0) ^ 2 * (cp μ * f x) := rfl
  simp only [ricci_conf hfa hne, dRicci_tPert hfa hne hf h1 h2, hinv, hh,
    Matrix.diagonal_mul_diagonal, Fin.sum_univ_four, Matrix.diagonal_apply]
  simp [dl, sgn, cp]
  field_simp
  ring

end Lightlike.Rows.G1_031
