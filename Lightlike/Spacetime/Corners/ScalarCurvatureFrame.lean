import Mathlib
import Lightlike.Spacetime.Corners.RicciTransport
import Lightlike.Spacetime.Corners.CurvatureSymmetries
import Lightlike.Spacetime.HypersurfaceConstraints

/-!
# The Ricci and scalar curvature in an orthonormal basis, for a model with corners on `Fin n → ℝ`

The model-`𝓘(ℝ, E)` results `ricciAt_frame` and `scalarCurvatureAt_frame` of
`Lightlike/Spacetime/HypersurfaceConstraints.lean`, for a manifold modelled by any
`I : ModelWithCorners ℝ (Fin n → ℝ) H` (for instance the transported model of the 2-sphere): for a
torsion-free metric connection and a basis `fᵢ` of `T_x M` with `g(fᵢ, fⱼ) = sᵢ δᵢⱼ`, `sᵢ² = 1`,

* `ricciAt_frameW`: `Ric(Y, Z) = Σᵢ sᵢ g(R(fᵢ, Y) Z, fᵢ)`;
* `scalarCurvatureAt_frameW`: `S = Σᵢ sᵢ Ric(fᵢ, fᵢ)`.

The proofs are those of the model-`𝓘` versions, with the slot linearity `curvatureAt_linearW` and the symmetry
`ricciAt_symm_provedW` of the Ricci tensor for models with corners.
-/

open Bundle Manifold Set VectorField Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 2 M]
  (cov : Connection I M) [LocallySmoothConnectionW cov] (g : NondegMetric I M)

/-- The curvature `v ↦ R(v, Y) Z` as a linear map. -/
def curvLW (x : M) (Y Z : TangentSpace I x) : TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun v := cov.curvatureAt x v Y Z
  map_add' a a' := (curvatureAt_linearW cov x).1 a a' Y Z
  map_smul' r a := (curvatureAt_linearW cov x).2.1 r a Y Z

/-- The Ricci tensor is the trace of `v ↦ R(v, Y) Z`. -/
theorem ricciAt_eq_trace_curvLW (x : M) (Y Z : TangentSpace I x) :
    cov.ricciAt x Y Z = LinearMap.trace ℝ _ (curvLW cov x Y Z) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (tbW (I := I) x)]
  unfold Connection.ricciAt
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, curvLW, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- Coordinates in an orthonormal basis: `f.coord i w = sᵢ g(w, fᵢ)`. -/
theorem coord_orthonormalW {ι : Type*} [Fintype ι] [DecidableEq ι] (x : M)
    (f : Module.Basis ι ℝ (TangentSpace I x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) (w : TangentSpace I x) (i : ι) :
    f.coord i w = s i * g.g x w (f i) := by
  have hw : g.g x w (f i) = f.coord i w * s i := by
    conv_lhs => rw [← f.sum_repr w]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hf]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [hw, mul_comm (f.coord i w), ← mul_assoc, hs, one_mul]

/-- **The Ricci tensor in an orthonormal basis**: `Ric(Y, Z) = Σᵢ sᵢ g(R(fᵢ, Y) Z, fᵢ)`. -/
theorem ricciAt_frameW {ι : Type*} [Fintype ι] [DecidableEq ι] (x : M)
    (f : Module.Basis ι ℝ (TangentSpace I x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) (Y Z : TangentSpace I x) :
    cov.ricciAt x Y Z = ∑ i, s i * g.g x (cov.curvatureAt x (f i) Y Z) (f i) := by
  rw [ricciAt_eq_trace_curvLW, LinearMap.trace_eq_matrix_trace ℝ f]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := coord_orthonormalW g x f s hs hf (curvLW cov x Y Z (f i)) i
  simpa [Module.Basis.coord_apply, curvLW] using this

theorem ricciAt_bilinearW (x : M) :
    (∀ Y Y' Z : TangentSpace I x, cov.ricciAt x (Y + Y') Z = cov.ricciAt x Y Z + cov.ricciAt x Y' Z) ∧
    (∀ (r : ℝ) (Y Z : TangentSpace I x), cov.ricciAt x (r • Y) Z = r * cov.ricciAt x Y Z) ∧
    (∀ Y Z Z' : TangentSpace I x, cov.ricciAt x Y (Z + Z') = cov.ricciAt x Y Z + cov.ricciAt x Y Z') ∧
    (∀ (r : ℝ) (Y Z : TangentSpace I x), cov.ricciAt x Y (r • Z) = r * cov.ricciAt x Y Z) := by
  have hl := curvatureAt_linearW cov x
  refine ⟨fun Y Y' Z => ?_, fun r Y Z => ?_, fun Y Z Z' => ?_, fun r Y Z => ?_⟩ <;>
    simp only [ricciAt_eq_trace_curvLW]
  · rw [← map_add]; congr 1; ext v; exact hl.2.2.1 v Y Y' Z
  · rw [← smul_eq_mul, ← map_smul]; congr 1; ext v; exact hl.2.2.2.1 r v Y Z
  · rw [← map_add]; congr 1; ext v; exact hl.2.2.2.2.1 v Y Z Z'
  · rw [← smul_eq_mul, ← map_smul]; congr 1; ext v; exact hl.2.2.2.2.2 r v Y Z

/-- The Ricci tensor at `x` as a continuous bilinear form. -/
def ricciCLMW (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
    LinearMap.mk₂ ℝ (cov.ricciAt x) (ricciAt_bilinearW cov x).1 (ricciAt_bilinearW cov x).2.1
      (ricciAt_bilinearW cov x).2.2.1 (ricciAt_bilinearW cov x).2.2.2)

theorem ricciCLMW_apply (x : M) (Y Z : TangentSpace I x) : ricciCLMW cov x Y Z = cov.ricciAt x Y Z := rfl

theorem nondegMetric_bilin_nondegenerateW (x : M) : (g.g x).toBilinForm.Nondegenerate :=
  ⟨fun v hv => g.nondegenerate x v hv, fun w hw => g.nondegenerate x w fun v => (g.symm x w v).trans (hw v)⟩

/-- The scalar curvature is the `g`-trace of the Ricci tensor. -/
theorem scalarCurvatureAt_eq_traceGW (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) (x : M) :
    cov.scalarCurvatureAt g x = traceG (g.g x) (ricciCLMW cov x) (nondegMetric_bilin_nondegenerateW g x) := by
  rw [traceG_eq_gram _ _ _ (tbW (I := I) x)]
  unfold Connection.scalarCurvatureAt
  simp only [ricciCLMW_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ricciAt_symm_provedW cov g hT hC]
  rfl

/-- **The scalar curvature in an orthonormal basis**: `S = Σᵢ sᵢ Ric(fᵢ, fᵢ)`. -/
theorem scalarCurvatureAt_frameW (hT : cov.torsion = 0) (hC : cov.IsMetricCompatible g) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x : M) (f : Module.Basis ι ℝ (TangentSpace I x)) (s : ι → ℝ) (hs : ∀ i, s i * s i = 1)
    (hf : ∀ i j, g.g x (f i) (f j) = if i = j then s i else 0) :
    cov.scalarCurvatureAt g x = ∑ i, s i * cov.ricciAt x (f i) (f i) := by
  rw [scalarCurvatureAt_eq_traceGW cov g hT hC, traceG_eq_gram _ _ _ f]
  have hG : (Matrix.of fun i j => g.g x (f i) (f j)) = Matrix.diagonal s := by
    ext i j; simp [hf, Matrix.diagonal_apply]
  have hinv : (Matrix.diagonal s)⁻¹ = Matrix.diagonal s := by
    rw [Matrix.inv_eq_left_inv]
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; exact hs i
  rw [hG, hinv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp [ricciCLMW_apply]

end Lightlike
