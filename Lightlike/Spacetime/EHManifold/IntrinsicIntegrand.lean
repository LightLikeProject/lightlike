import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.EHManifold.Contraction
import Lightlike.Spacetime.EHManifold.EinsteinForm
import Lightlike.Spacetime.EHManifold.Perturbation

/-!
# The intrinsic integrand of the first variation of the Einstein–Hilbert action

`ehIntegrand g h Λ p = ⟨G + Λ g, h⟩_g (p)`: the full contraction, with the inverse metric, of the Einstein
tensor of `g` plus `Λ g` with a symmetric bilinear field `h`, at the point `p`. It is defined with the
coordinate basis of the chart at `p`, and `ehIntegrand_chart` gives it in the components of any chart:
`h_{αβ} (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ})`.

Supporting definitions for the intrinsic form of the Einstein–Hilbert first variation; no catalogue entry.
-/

open Bundle Manifold Set Matrix
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

/-- The trace of `X H` for a symmetric `H`, as a double sum. -/
lemma trace_mul_of_symm {n : ℕ} (X H : Matrix (Fin n) (Fin n) ℝ) (hH : ∀ i j, H i j = H j i) :
    (X * H).trace = ∑ α, ∑ β, H α β * X α β := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [hH β α, mul_comm]

/-- The contraction `tr(G⁻¹ (Ric - ½ R G + Λ G) G⁻¹ H)` written with raised indices. -/
lemma trace_einstein_contract {n : ℕ} (G Ric H : Matrix (Fin n) (Fin n) ℝ) (R Λ : ℝ)
    (hG : IsUnit G.det) (hH : ∀ i j, H i j = H j i) :
    (G⁻¹ * (Ric - (R / 2) • G + Λ • G) * G⁻¹ * H).trace =
      ∑ α, ∑ β, H α β * ((∑ a, ∑ b, G⁻¹ α a * Ric a b * G⁻¹ b β) -
        (1 / 2) * R * G⁻¹ α β + Λ * G⁻¹ α β) := by
  have h1 : G⁻¹ * (Ric - (R / 2) • G + Λ • G) * G⁻¹ =
      G⁻¹ * Ric * G⁻¹ - (R / 2) • G⁻¹ + Λ • G⁻¹ := by
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  rw [h1, trace_mul_of_symm _ H hH]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  congr 1
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The Levi-Civita connection of `g` is a Levi-Civita connection. -/
lemma isLeviCivita_leviCivita (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) :
    (leviCivita g).IsLeviCivita g := ⟨leviCivita_torsion g, leviCivita_compat g⟩

/-- **The integrand of the first variation**, `⟨G + Λ g, h⟩_g` at the point `p`: the contraction of the
Einstein tensor of `g` plus `Λ g` with `h`, with the inverse metric. -/
def ehIntegrand (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ)
    (p : M) : ℝ :=
  haveI := contMDiffCovariantDerivative_leviCivita g
  formContract (coordBasis p (FiberBundle.mem_baseSet_trivializationAt' p)) (g.g p).toBilinForm
    (einsteinBilin g (leviCivita g) (isLeviCivita_leviCivita g) p + Λ • (g.g p).toBilinForm)
    (h.h p).toBilinForm

/-- **The integrand in the components of a chart**: `h_{αβ} (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ})`. -/
theorem ehIntegrand_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (Λ : ℝ) (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ehIntegrand g h Λ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      ∑ α, ∑ β, h.coordComp x₀ y α β *
        (ricciUp (g.coordMetric x₀) y α β -
          (1 / 2) * scalarCurvature (g.coordMetric x₀) y * (g.coordMetric x₀ y)⁻¹ α β +
          Λ * (g.coordMetric x₀ y)⁻¹ α β) := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hG : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp)
      (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)).toBilinForm = g.coordMetric x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eq x₀ hy]
    rfl
  have hH : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp)
      (h.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)).toBilinForm = h.coordComp x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, h.coordComp_eq x₀ hy]
    rfl
  have hE : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp)
      (einsteinBilin g (leviCivita g) (isLeviCivita_leviCivita g)
        ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)) =
      (Matrix.of fun σ ν => ricci (g.coordMetric x₀) σ ν y) -
        (scalarCurvature (g.coordMetric x₀) y / 2) • g.coordMetric x₀ y := by
    rw [toMatrix_einsteinBilin g (leviCivita g) (isLeviCivita_leviCivita g) x₀ hp,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).right_inv hy]
    ext σ ν
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, einsteinTensor]
    ring
  unfold ehIntegrand
  rw [formContract_basis_indep _ (coordBasis x₀ hp)]
  unfold formContract
  rw [map_add, map_smul, hG, hH, hE,
    trace_einstein_contract _ _ _ _ _ (g.coordMetric_isUnit_det x₀ hy) (h.coordComp_symm x₀ y)]
  rfl

end Lightlike
