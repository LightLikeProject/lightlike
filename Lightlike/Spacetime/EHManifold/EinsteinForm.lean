import Lightlike.Spacetime.ChartTensor
import Lightlike.Spacetime.Coordinates

/-!
# The Einstein tensor of a metric as a bilinear form on each tangent space

For a Levi-Civita connection `cov` of `g`, the Einstein field `cov.einsteinField g p` is bilinear
(`einsteinBilin`), and its matrix in the coordinate basis of any chart at `x₀` containing `p` is the Einstein
tensor of the components of `g` in that chart (`toMatrix_einsteinBilin`).

Both follow from the component formula `einsteinField_eq_bilOf`.

Supporting lemmas for the intrinsic form of the Einstein–Hilbert first variation; no catalogue entry.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
  (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- The coordinate basis vector is the value of the coordinate vector field. -/
lemma coordBasis_eq_coordField (x₀ : M) {p : M} (hp : p ∈ (chartTriv n x₀).baseSet) (k : Fin n) :
    coordBasis x₀ hp k = coordField x₀ k p := by
  unfold coordField
  rw [Trivialization.localFrame_apply_of_mem_baseSet (e := chartTriv n x₀)
    (b := Pi.basisFun ℝ (Fin n)) (i := k) hp]
  rfl

/-- **The components of the Einstein field in a chart** are the Einstein tensor of the components of the
metric. -/
theorem einsteinField_coordBasis (hLC : cov.IsLeviCivita g) (x₀ : M) {p : M}
    (hp : p ∈ (chartTriv n x₀).baseSet) (σ ν : Fin n) :
    cov.einsteinField g p (coordBasis x₀ hp σ) (coordBasis x₀ hp ν) =
      einsteinTensor (g.coordMetric x₀) σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  rw [coordBasis_eq_coordField, coordBasis_eq_coordField,
    einsteinField_eq_bilOf (g := g) (cov := cov) x₀ hLC hp]
  show BE g x₀ p (hv x₀ p (coordField x₀ σ p)) (hv x₀ p (coordField x₀ ν p)) = _
  rw [hv_coordField x₀ hp, hv_coordField x₀ hp]
  show einsteinComp g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) (Pi.single σ 1) (Pi.single ν 1) = _
  rw [einsteinComp_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- The Einstein field at a point, in the components of the chart at that point. -/
lemma einsteinField_eq_BE (hLC : cov.IsLeviCivita g) (p : M)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    cov.einsteinField g p u v = BE g p p (hv p p u) (hv p p v) :=
  einsteinField_eq_bilOf (g := g) (cov := cov) p hLC
    (FiberBundle.mem_baseSet_trivializationAt' p) u v

/-- **The Einstein tensor at a point as a bilinear form** on the tangent space. -/
def einsteinBilin (hLC : cov.IsLeviCivita g) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :=
  LinearMap.mk₂ ℝ (cov.einsteinField g p)
    (fun u u' v => by
      rw [einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC,
        hv_add p (FiberBundle.mem_baseSet_trivializationAt' p), map_add,
        ContinuousLinearMap.add_apply])
    (fun r u v => by
      rw [einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC,
        hv_smul' p (FiberBundle.mem_baseSet_trivializationAt' p), map_smul,
        ContinuousLinearMap.smul_apply])
    (fun u v v' => by
      rw [einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC,
        hv_add p (FiberBundle.mem_baseSet_trivializationAt' p), map_add])
    (fun r u v => by
      rw [einsteinField_eq_BE g cov hLC, einsteinField_eq_BE g cov hLC,
        hv_smul' p (FiberBundle.mem_baseSet_trivializationAt' p), map_smul])

lemma einsteinBilin_apply (hLC : cov.IsLeviCivita g) (p : M)
    (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    einsteinBilin g cov hLC p u v = cov.einsteinField g p u v := rfl

/-- **The matrix of the Einstein form in the coordinate basis of a chart** is the Einstein tensor of the
components of the metric in that chart. -/
theorem toMatrix_einsteinBilin (hLC : cov.IsLeviCivita g) (x₀ : M) {p : M}
    (hp : p ∈ (chartTriv n x₀).baseSet) :
    LinearMap.BilinForm.toMatrix (coordBasis x₀ hp) (einsteinBilin g cov hLC p) =
      Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₀) σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  ext σ ν
  rw [LinearMap.BilinForm.toMatrix_apply, einsteinBilin_apply, Matrix.of_apply]
  exact einsteinField_coordBasis g cov hLC x₀ hp σ ν

end Lightlike
