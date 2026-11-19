import Lightlike.Spacetime.ContractedBianchiWithin
import Lightlike.Spacetime.DivergenceFree
import Lightlike.Spacetime.Corners.ChartTensor
/-!
# The Einstein tensor of a Levi-Civita connection is divergence free, for any model with corners

`einstein_divergence_free_provedW`: for the Levi-Civita connection `cov` of a nondegenerate metric `g` (any signature) on a
manifold modelled with corners on `Fin n → ℝ`, the divergence `g^{ij} (∇_i G)(e_j, w)` of the Einstein tensor
`G = Ric - (S/2) g` (`Connection.divBilinAt`, `Connection.einsteinField`) vanishes.

Proof. (1) In a chart the covariant derivative of a bilinear field is given by the components formula
(`covDerivBilinAt_einsteinW`, `Lightlike/Spacetime/Corners/ChartTensor.lean`); hence `(∇G)(X, v, w)` is trilinear and the divergence in the
basis of the `finBasis` is the divergence in the coordinate basis (`divBilinAt_einstein_coordW`, with `trace_raiseW`),
whose terms are `DG` of the coordinate metric within `range I` (`covDerivBilinAt_einstein_valueW`, using
`gamHat_coordW`). (2) The coordinate identity `g^{στ} DG_{στν} = 0` within `range I` is `einstein_div_coordW`
(`ContractedBianchiWithin.lean`), proved from the coordinate second Bianchi identity.

**Differences from the task `T-GE1-P8`** (which stays open): the task is for any model space `E` and any
`ModelWithCorners` `I`; this theorem is for a manifold with corners modelled on `Fin n → ℝ` (any
`ModelWithCorners ℝ (Fin n → ℝ) H`, boundary and corners allowed; the coordinate formulas have derivatives within
`range I`), with `[IsManifold I 2 M]` added, and a locally smooth connection (no Hausdorff hypothesis). The comparison of
the statement with Carroll, *Lecture Notes on General Relativity* (1997), ch. 3, is pending: the source was not read at
the cited location.

This is the Corners layer: the version for any model with corners of `Lightlike/Spacetime/DivergenceFree.lean`, with a
`W` suffix where the boundaryless file owns the name (`hasFDerivAt_sum_smul`, which does not involve the model, is the
boundaryless file's).
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M]
  (g : NondegMetric I M)
  (cov : Connection I M) [LocallySmoothConnectionW cov]

section Lin
variable (x₀ : M) (h : cov.IsLeviCivita g) {x : M} (hx : x ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet)
include h hx

/-- `∇ G` is additive in the derivative slot. -/
theorem covDerivBilinAt_einstein_add_leftW (X X' v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (X + X') v w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X' v w := by
  rw [covDerivBilinAt_einsteinW g cov x₀ h hx, covDerivBilinAt_einsteinW g cov x₀ h hx,
    covDerivBilinAt_einsteinW g cov x₀ h hx, hv_addW x₀ hx]
  simp only [map_add, add_apply]
  ring

/-- `∇ G` is homogeneous in the derivative slot. -/
theorem covDerivBilinAt_einstein_smul_leftW (r : ℝ) (X v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (r • X) v w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  rw [covDerivBilinAt_einsteinW g cov x₀ h hx, covDerivBilinAt_einsteinW g cov x₀ h hx, hv_smul'W x₀ hx]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- `∇ G` is additive in the first form slot. -/
theorem covDerivBilinAt_einstein_add_midW (X v v' w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (v + v') w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X v' w := by
  rw [covDerivBilinAt_einsteinW g cov x₀ h hx, covDerivBilinAt_einsteinW g cov x₀ h hx,
    covDerivBilinAt_einsteinW g cov x₀ h hx, hv_addW x₀ hx]
  simp only [map_add, add_apply]
  ring

/-- `∇ G` is homogeneous in the first form slot. -/
theorem covDerivBilinAt_einstein_smul_midW (r : ℝ) (X v w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (r • v) w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  rw [covDerivBilinAt_einsteinW g cov x₀ h hx, covDerivBilinAt_einsteinW g cov x₀ h hx, hv_smul'W x₀ hx]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- The bilinear form `(X, v) ↦ (∇_X G)(v, w)` at a point of the chart domain. -/
def divFormW (w : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X v => cov.covDerivBilinAt (cov.einsteinField g) x X v w)
    (fun X X' v => covDerivBilinAt_einstein_add_leftW g cov x₀ h hx X X' v w)
    (fun r X v => covDerivBilinAt_einstein_smul_leftW g cov x₀ h hx r X v w)
    (fun X v v' => covDerivBilinAt_einstein_add_midW g cov x₀ h hx X v v' w)
    (fun r X v => covDerivBilinAt_einstein_smul_midW g cov x₀ h hx r X v w)


end Lin

section Div
variable (x : M) (h : cov.IsLeviCivita g)
include h

/-- **The divergence of the Einstein tensor is the coordinate sum** `g^{στ} (∇_σ G)(∂_τ, w)`. -/
theorem divBilinAt_einstein_coordW (w : TangentSpace I x) :
    cov.divBilinAt g (cov.einsteinField g) x w =
      ∑ σ, ∑ τ, (g.coordMetricW x (extChartAt I x x))⁻¹ σ τ *
        cov.covDerivBilinAt (cov.einsteinField g) x (coordFieldW (I := I) x σ x) (coordFieldW (I := I) x τ x) w := by
  have hzs : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hy : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hzs
  have hp : x ∈ (tTrivW (I := I) (E := Fin n → ℝ) x).baseSet := by
    simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) x)
  set B := divFormW g cov x h hp w with hB
  have h1 : cov.divBilinAt g (cov.einsteinField g) x w =
      ∑ i, ∑ j, (gramBW g x (tbW x))⁻¹ i j * B (tbW x i) (tbW x j) := rfl
  rw [h1, ← trace_raiseW g x B (tbW x), trace_raiseW g x B (coordBasisW x hp)]
  have e1 : ∀ k, coordBasisW x hp k = coordFieldW (I := I) x k x := fun k =>
    (coordBasis_applyW x hp k).trans (symmL_eq_coordFieldW x hp k)
  have hG : gramBW g x (coordBasisW x hp) = g.coordMetricW x (extChartAt I x x) := by
    ext i j
    show g.g x (coordBasisW x hp i) (coordBasisW x hp j) = _
    rw [e1 i, e1 j]
    have := g_coordFieldW g x i j hy
    rw [(extChartAt I x).left_inv hzs] at this
    exact this
  rw [hG]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [e1 σ, e1 τ]
  rfl
end Div

/-- The derivative within a set of a finite sum of scalar functions times constant vectors. -/
theorem hasFDerivWithinAt_sum_smul {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type*} [Fintype ι] [Fintype κ] {s : Set F}
    (c : ι → κ → F → ℝ) (K : ι → κ → V) {y : F} (hc : ∀ i j, DifferentiableWithinAt ℝ (c i j) s y) :
    HasFDerivWithinAt (fun y' => ∑ i, ∑ j, c i j y' • K i j)
      (∑ i, ∑ j, (fderivWithin ℝ (c i j) s y).smulRight (K i j)) s y :=
  HasFDerivWithinAt.fun_sum fun i _ => HasFDerivWithinAt.fun_sum fun j _ => (hc i j).hasFDerivWithinAt.smul_const _

section Val
variable (x : M) (h : cov.IsLeviCivita g)

/-- The derivative within `range I` of the component form of the Einstein tensor along `eσ`. -/
theorem fderiv_einsteinCompW {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x).target) (σ : Fin n) :
    fderivWithin ℝ (einsteinCompW g x) (range I) y (Pi.single σ 1) =
      ∑ i, ∑ j, pdW (range I) σ (einsteinTensorW (range I) (g.coordMetricW x) i j) y •
        ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) := by
  have hgc := g.isCoordMetricW_coordMetric x
  have hc : ∀ σ ν : Fin n, DifferentiableWithinAt ℝ
      (fun y' => einsteinTensorW (range I) (g.coordMetricW x) σ ν y') (range I) y := fun σ ν =>
    differentiableWithinAt_of_contDiffOn hgc (hgc.contDiffOn_einsteinTensorW σ ν) hy
  have := (hasFDerivWithinAt_sum_smul (fun σ ν y' => einsteinTensorW (range I) (g.coordMetricW x) σ ν y')
    (fun σ ν => (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)) hc).fderivWithin
      (I.uniqueDiffOn y (extChartAt_target_subset_range x hy))
  unfold einsteinCompW
  rw [this]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [pdW]

set_option synthInstance.maxHeartbeats 200000 in
/-- The derivative of the Einstein component field along `∂_σ` at the base point of the chart. -/
theorem mvfderiv_BE_coordFieldW (σ : Fin n) :
    mvfderiv I (BEW g x) x (coordFieldW (I := I) x σ x) =
      fderivWithin ℝ (einsteinCompW g x) (range I) (extChartAt I x x) (Pi.single σ 1) := by
  have hzs : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hy : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hzs
  rw [mvfderiv_eq_chartW (BEW g x) x (mdiffAt_BEW g hzs) (coordFieldW (I := I) x σ x)]
  have hm := mfderiv_chart_coordFieldW (I := I) x σ hy
  rw [(extChartAt I x).left_inv hzs] at hm
  rw [hm]
  have hev : (BEW g x ∘ (extChartAt I x).symm) =ᶠ[nhdsWithin (extChartAt I x x) (range I)]
      einsteinCompW g x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with y' hy'
    simp only [Function.comp_apply, BEW, (extChartAt I x).right_inv hy']
  rw [hev.fderivWithin_eq (hev.eq_of_nhdsWithin (extChartAt_target_subset_range x hy))]

include h in
/-- **`(∇_σ G)(∂_τ, w)` in coordinates**: `Σ_ν w^ν DG_{στν}`. -/
theorem covDerivBilinAt_einstein_valueW (σ τ : Fin n) (w : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (coordFieldW (I := I) x σ x) (coordFieldW (I := I) x τ x) w =
      ∑ ν, hvW x x w ν * DGW (range I) (g.coordMetricW x) σ τ ν (extChartAt I x x) := by
  have hzs : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hy : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hzs
  have hp : x ∈ (tTrivW (I := I) (E := Fin n → ℝ) x).baseSet := by
    simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) x)
  rw [covDerivBilinAt_einsteinW g cov x h hp, hv_coordFieldW x hp σ, hv_coordFieldW x hp τ,
    mvfderiv_BE_coordFieldW g x σ, fderiv_einsteinCompW g x hy σ]
  set a := hvW x x w with ha
  have hsa : a = ∑ ν, a ν • (Pi.single ν 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have hBE : ∀ u b : Fin n → ℝ, BEW g x x u b = ∑ i, ∑ j, u i * b j *
      einsteinTensorW (range I) (g.coordMetricW x) i j (extChartAt I x x) := fun u b =>
    einsteinComp_applyW g x _ u b
  have hg1 := gamHat_coordW cov x g h hp
  have hgam1 : ∀ i, gamHatW cov x x (Pi.single τ 1) (Pi.single σ 1) i =
      christoffelW (range I) (g.coordMetricW x) i σ τ (extChartAt I x x) := fun i => by
    rw [hg1 σ τ]; simp [Finset.sum_apply, Pi.single_apply]
  have hgam2 : ∀ k, gamHatW cov x x a (Pi.single σ 1) k =
      ∑ ν, a ν * christoffelW (range I) (g.coordMetricW x) k σ ν (extChartAt I x x) := fun k => by
    conv_lhs => rw [hsa]
    simp only [map_sum, map_smul, sum_apply, smul_apply, hg1 σ,
      Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp
  unfold DGW
  simp only [hBE, Finset.sum_apply, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  simp only [hgam1, hgam2]
  set y := extChartAt I x x
  have e1 : ∑ x_1, ∑ x_2, pdW (range I) σ (einsteinTensorW (range I) (g.coordMetricW x) x_1 x_2) y * ((if x_1 = τ then (1 : ℝ) else 0) * a x_2) =
      ∑ ν, a ν * pdW (range I) σ (einsteinTensorW (range I) (g.coordMetricW x) τ ν) y := by
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have e2 : ∑ x_1, ∑ x_2, christoffelW (range I) (g.coordMetricW x) x_1 σ τ y * a x_2 * einsteinTensorW (range I) (g.coordMetricW x) x_1 x_2 y =
      ∑ ν, a ν * ∑ k, christoffelW (range I) (g.coordMetricW x) k σ τ y * einsteinTensorW (range I) (g.coordMetricW x) k ν y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x_1, ∑ x_2, ((if x_1 = τ then (1 : ℝ) else 0) *
      ∑ ν, a ν * christoffelW (range I) (g.coordMetricW x) x_2 σ ν y) * einsteinTensorW (range I) (g.coordMetricW x) x_1 x_2 y =
      ∑ ν, a ν * ∑ k, christoffelW (range I) (g.coordMetricW x) k σ ν y * einsteinTensorW (range I) (g.coordMetricW x) τ k y := by
    rw [Finset.sum_comm]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_eq]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3]
  simp only [mul_sub, Finset.sum_sub_distrib]
end Val

section Main
variable (x : M) (h : cov.IsLeviCivita g)
include h

/-- **The Einstein tensor of a Levi-Civita connection is divergence free**, on a manifold modelled with corners on
`ℝⁿ` (boundary and corners allowed), of class `C²`, for a locally smooth connection; no Hausdorff hypothesis. -/
theorem einstein_divergence_free_provedW (w : TangentSpace I x) :
    cov.divBilinAt g (cov.einsteinField g) x w = 0 := by
  have hzs : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hy : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hzs
  rw [divBilinAt_einstein_coordW g cov x h w]
  simp only [covDerivBilinAt_einstein_valueW g cov x h, Finset.mul_sum]
  have key := einstein_div_coordW (g.isCoordMetricW_coordMetric x) hy
  have : ∀ ν, ∑ σ, ∑ τ, (g.coordMetricW x (extChartAt I x x))⁻¹ σ τ *
      (hvW x x w ν * DGW (range I) (g.coordMetricW x) σ τ ν (extChartAt I x x)) = 0 := fun ν => by
    have := key ν
    calc _ = hvW x x w ν * ∑ σ, ∑ τ, (g.coordMetricW x (extChartAt I x x))⁻¹ σ τ *
          DGW (range I) (g.coordMetricW x) σ τ ν (extChartAt I x x) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [this, mul_zero]
  calc _ = ∑ ν, ∑ σ, ∑ τ, (g.coordMetricW x (extChartAt I x x))⁻¹ σ τ *
        (hvW x x w ν * DGW (range I) (g.coordMetricW x) σ τ ν (extChartAt I x x)) := by
        exact (Finset.sum_congr rfl fun σ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun ν _ => this ν
end Main
end Lightlike
