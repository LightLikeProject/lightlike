module

public import Lightlike.Cosmology.FLRW

/-!
# The scalar field in FLRW: the stress tensor of a homogeneous field (row G1-027, milestone CO29)

For a scalar field `Φ` with potential `V` on a coordinate metric `g`, the stress-energy tensor is
`T_{μν} = ∂_μ Φ ∂_ν Φ − (½ g^{αβ} ∂_α Φ ∂_β Φ + V(Φ)) g_{μν}`. For a homogeneous field `Φ = φ(t)` on
the FLRW metric of `Lightlike.Cosmology.flrwMetric` it is the perfect fluid at rest with
`ρ = φ̇²/2 + V(φ)` and `p = φ̇²/2 − V(φ)`.

Main results
* `Lightlike.Cosmology.scalarStress`: the stress tensor of a scalar field in a chart.
* `Lightlike.Cosmology.scalarStress_flrw`: for a homogeneous field it is `perfectFluid ρ p`.

Source: Baumann, *TASI lectures on inflation* (`baumann-2009`), eq. (A.140) for the equations of
motion; the tensor is Carroll, gr-qc/9712019, eq. (1.112).
-/

@[expose] public section

open Matrix

noncomputable section

namespace Lightlike

namespace Cosmology

/-- The stress-energy tensor of a scalar field `Φ` with potential `V` in a chart with metric `g`:
`T_{μν} = ∂_μ Φ ∂_ν Φ − (½ g^{αβ} ∂_α Φ ∂_β Φ + V(Φ)) g_{μν}`. -/
def scalarStress (Φ : (Fin 4 → ℝ) → ℝ) (V : ℝ → ℝ)
    (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  pd μ Φ x * pd ν Φ x -
    (1 / 2 * ∑ α : Fin 4, ∑ β : Fin 4, (g x)⁻¹ α β * pd α Φ x * pd β Φ x + V (Φ x)) * g x μ ν

/-- The energy density `φ̇²/2 + V(φ)` of a homogeneous scalar field. -/
def scalarRho (φ V : ℝ → ℝ) (t : ℝ) : ℝ := deriv φ t ^ 2 / 2 + V (φ t)

/-- The pressure `φ̇²/2 − V(φ)` of a homogeneous scalar field. -/
def scalarP (φ V : ℝ → ℝ) (t : ℝ) : ℝ := deriv φ t ^ 2 / 2 - V (φ t)

/-- **A homogeneous scalar field on the FLRW metric is a perfect fluid at rest**, with density
`φ̇²/2 + V(φ)` and pressure `φ̇²/2 − V(φ)`, at every point where `φ` is differentiable in time. -/
theorem scalarStress_flrw {φ V : ℝ → ℝ} {a : ℝ → ℝ} {k : ℝ} {x : Fin 4 → ℝ}
    (hφ : DifferentiableAt ℝ φ (x 0)) (ha : a (x 0) ≠ 0)
    (hD : 0 < 1 + k * spatialNormSq x / 4) (μ ν : Fin 4) :
    scalarStress (fun y => φ (y 0)) V (flrwMetric a k) μ ν x =
      perfectFluid (scalarRho φ V) (scalarP φ V) (flrwMetric a k) μ ν x := by
  have hp : ∀ j : Fin 4, pd j (fun y : Fin 4 → ℝ => φ (y 0)) x
      = if j = 0 then deriv φ (x 0) else 0 := fun j => (hasPd_comp0 (j := j) hφ).2
  have hinv : (flrwMetric a k x)⁻¹ = Matrix.diagonal (fun i : Fin 4 =>
      (if i = 0 then (-1 : ℝ) else (a (x 0) / (1 + k * spatialNormSq x / 4)) ^ 2)⁻¹) :=
    inv_diag' _ (fun i => by
      split_ifs
      · norm_num
      · exact pow_ne_zero 2 (div_ne_zero ha hD.ne'))
  unfold scalarStress perfectFluid scalarRho scalarP
  rw [hinv]
  simp only [hp, flrwMetric, Fin.sum_univ_four, Matrix.diagonal_apply]
  fin_cases μ <;> fin_cases ν <;> simp <;> ring

end Cosmology

end Lightlike
