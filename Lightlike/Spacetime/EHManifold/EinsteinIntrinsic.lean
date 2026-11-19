import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.EHManifold.ManifoldStationary

/-!
# Stationary points of the Einstein–Hilbert action: `G + Λ g = 0`

`isEHStationary_iff_einstein`: a metric `g` (of any signature) on a manifold is a stationary point of the
Einstein–Hilbert action with cosmological constant `Λ` if and only if `G(u, v) + Λ g(u, v) = 0` for all
tangent vectors `u`, `v` at every point, where `G` is the Einstein tensor of the Levi-Civita connection of
`g`.

It is `isEHStationary_iff` with the chart condition rewritten intrinsically; the step uses the symmetry of
the Ricci tensor (`ricciAt_symm_proved`).

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.66) and
  (4.67), p. 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

/-- `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` is the matrix `g⁻¹ (G + Λ g) g⁻¹`, with `G` the Einstein tensor. -/
lemma einsteinUp_eq_mul {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Λ : ℝ) (y : Fin n → ℝ)
    (hG : IsUnit (g y).det) (α β : Fin n) :
    einsteinUp g Λ y α β =
      ((g y)⁻¹ * ((Matrix.of fun σ ν => einsteinTensor g σ ν y) + Λ • g y) * (g y)⁻¹) α β := by
  have hE : (Matrix.of fun σ ν => einsteinTensor g σ ν y) =
      (Matrix.of fun σ ν => ricci g σ ν y) - (scalarCurvature g y / 2) • g y := by
    ext σ ν
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, einsteinTensor]
    ring
  have h1 : (g y)⁻¹ * ((Matrix.of fun σ ν => ricci g σ ν y) - (scalarCurvature g y / 2) • g y +
        Λ • g y) * (g y)⁻¹ =
      (g y)⁻¹ * (Matrix.of fun σ ν => ricci g σ ν y) * (g y)⁻¹ -
        (scalarCurvature g y / 2) • (g y)⁻¹ + Λ • (g y)⁻¹ := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  rw [hE, h1]
  unfold einsteinUp ricciUp
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

/-- For symmetric `G` (invertible) and `X`: the symmetric part of `G⁻¹ X G⁻¹` vanishes iff `X = 0`. -/
lemma inv_mul_mul_inv_symm_part {n : ℕ} (G X : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det)
    (hGs : Gᵀ = G) (hXs : Xᵀ = X) :
    (∀ α β, (G⁻¹ * X * G⁻¹) α β + (G⁻¹ * X * G⁻¹) β α = 0) ↔ X = 0 := by
  have hUs : (G⁻¹ * X * G⁻¹)ᵀ = G⁻¹ * X * G⁻¹ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hGs, hXs,
      Matrix.mul_assoc]
  constructor
  · intro h
    have hU : G⁻¹ * X * G⁻¹ = 0 := by
      ext α β
      have h1 := h α β
      have h2 : (G⁻¹ * X * G⁻¹) β α = (G⁻¹ * X * G⁻¹) α β := by
        conv_lhs => rw [← hUs]
        rfl
      rw [h2] at h1
      show (G⁻¹ * X * G⁻¹) α β = 0
      linarith
    have hX : X = G * (G⁻¹ * X * G⁻¹) * G := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.mul_one]
    rw [hX, hU, Matrix.mul_zero, Matrix.zero_mul]
  · intro h α β
    rw [h, Matrix.mul_zero, Matrix.zero_mul]
    simp

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- **Einstein's equation at a point, in a chart and intrinsically.** At the point `p` with coordinates `y`
in the chart at `x₁`: the symmetric part of `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` vanishes if and only if
`G(u, v) + Λ g(u, v) = 0` for all tangent vectors `u`, `v` at `p`. -/
theorem einsteinUp_symm_eq_zero_iff (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (x₁ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    (∀ α β, einsteinUp (g.coordMetric x₁) Λ y α β + einsteinUp (g.coordMetric x₁) Λ y β α = 0) ↔
      ∀ u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y),
        (leviCivita g).einsteinField g _ u v + Λ * g.g _ u v = 0 := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hLC := isLeviCivita_leviCivita g
  have hp := symm_mem_chartTriv_baseSet x₁ hy
  have hGu := g.coordMetric_isUnit_det x₁ hy
  have hGs := g.coordMetric_transpose x₁ y
  -- the matrices of the forms in the coordinate basis
  have hGm : LinearMap.BilinForm.toMatrix (coordBasis x₁ hp)
      (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm = g.coordMetric x₁ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eq x₁ hy]
    rfl
  have hEm : LinearMap.BilinForm.toMatrix (coordBasis x₁ hp)
      (einsteinBilin g (leviCivita g) hLC ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)) =
      Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y := by
    rw [toMatrix_einsteinBilin g (leviCivita g) hLC x₁ hp,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv hy]
  have hXm : LinearMap.BilinForm.toMatrix (coordBasis x₁ hp)
      (einsteinBilin g (leviCivita g) hLC ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) +
        Λ • (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm) =
      (Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y) + Λ • g.coordMetric x₁ y := by
    rw [map_add, map_smul, hGm, hEm]
  -- symmetry of the Einstein form
  have hEsymm : ∀ u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y),
      (leviCivita g).einsteinField g _ u v = (leviCivita g).einsteinField g _ v u := by
    intro u v
    unfold Connection.einsteinField
    rw [ricciAt_symm_proved (leviCivita g) g hLC.1 hLC.2 _ u v, g.symm _ u v]
  have hXs : ((Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y) +
      Λ • g.coordMetric x₁ y)ᵀ =
      (Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y) + Λ • g.coordMetric x₁ y := by
    rw [← hXm]
    ext i j
    rw [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
    show (leviCivita g).einsteinField g _ _ _ + Λ * g.g _ _ _ =
      (leviCivita g).einsteinField g _ _ _ + Λ * g.g _ _ _
    rw [hEsymm, g.symm]
  have hstep : (∀ α β, einsteinUp (g.coordMetric x₁) Λ y α β +
        einsteinUp (g.coordMetric x₁) Λ y β α = 0) ↔
      (Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y) + Λ • g.coordMetric x₁ y = 0 := by
    rw [← inv_mul_mul_inv_symm_part (g.coordMetric x₁ y) _ hGu hGs hXs]
    simp only [einsteinUp_eq_mul (g.coordMetric x₁) Λ y hGu]
  rw [hstep, ← hXm]
  constructor
  · intro h0 u v
    have hform : einsteinBilin g (leviCivita g) hLC ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) +
        Λ • (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm = 0 :=
      (LinearMap.BilinForm.toMatrix (coordBasis x₁ hp)).injective (by rw [h0, map_zero])
    have := congrArg (fun B : LinearMap.BilinForm ℝ _ => B u v) hform
    exact this
  · intro h0
    have hform : einsteinBilin g (leviCivita g) hLC ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) +
        Λ • (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm = 0 :=
      LinearMap.ext₂ fun u v => h0 u v
    rw [hform, map_zero]

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- **Stationary points of the Einstein–Hilbert action are the solutions of Einstein's equation
`G + Λ g = 0`.** -/
theorem isEHStationary_iff_einstein (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) :
    IsEHStationary g Λ ↔ ∀ (p : M) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p),
      (leviCivita g).einsteinField g p u v + Λ * g.g p u v = 0 := by
  rw [isEHStationary_iff]
  constructor
  · intro h p
    have h1 := (einsteinUp_symm_eq_zero_iff g Λ p (mem_extChartAt_target p)).1
      (h p _ (mem_extChartAt_target p))
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (mem_extChartAt_source p)] at h1
    exact h1
  · intro h x₁ y hy
    exact (einsteinUp_symm_eq_zero_iff g Λ x₁ hy).2 fun u v => h _ u v

end Lightlike
