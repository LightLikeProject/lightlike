import Lightlike.Spacetime.ContractedBianchi
import Lightlike.Spacetime.ChartAgreement
/-!
# The Einstein tensor of a Levi-Civita connection is divergence free (task `T-GE1-P8`)

`einstein_divergence_free_proved`: for the Levi-Civita connection `cov` of a Lorentzian metric `g`, the divergence
`g^{ij} (∇_i G)(e_j, w)` of the Einstein tensor `G = Ric - (S/2) g` (`Connection.divBilinAt`,
`Connection.einsteinField`) vanishes.

Proof. (1) In a chart the covariant derivative of a bilinear field is given by the components formula
(`covDerivBilinAt_einstein`, `ChartTensor.lean`); hence `(∇G)(X, v, w)` is trilinear and the divergence in the basis of the
`finBasis` is the divergence in the coordinate basis (`divBilinAt_einstein_coord`, with `trace_raise`), whose terms are
`DG` of the coordinate metric (`covDerivBilinAt_einstein_value`, using `gamHat_coord`). (2) The coordinate identity
`g^{στ} DG_{στν} = 0` is `einstein_div_coord` (`ContractedBianchi.lean`), proved from the coordinate second Bianchi
identity, not from `T-GE1-P7`.

**Former task `T-GE1-P8`, closed by `einstein_divergence_free_proved`.** Differences from the task statement (approved on 18 November 2026,
updated for the metrics of any signature of GE11): (1) the model is `Fin n → ℝ` with no boundary instead of any model space and `ModelWithCorners` (this
matches the source, where manifolds are charts onto open subsets of `ℝⁿ`), with a locally smooth connection and no Hausdorff hypothesis; the task also
assumes `[IsManifold I 2 M]`, so that is not a difference; (2) representation: Carroll, *Lecture Notes on General Relativity* (1997), ch. 3, eqs. (3.94)
and (3.96) (read at those locations), derives `∇^μ G_{μν} = 0` by contracting the Bianchi identity (3.87) twice, the proof here is a coordinate computation.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
  (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [LocallySmoothConnection cov]

section Lin
variable (x₀ : M) (h : cov.IsLeviCivita g) {x : M} (hx : x ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet)
include h hx

/-- `∇ G` is additive in the derivative slot. -/
theorem covDerivBilinAt_einstein_add_left (X X' v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (X + X') v w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X' v w := by
  rw [covDerivBilinAt_einstein g cov x₀ h hx, covDerivBilinAt_einstein g cov x₀ h hx,
    covDerivBilinAt_einstein g cov x₀ h hx, hv_add x₀ hx]
  simp only [map_add, add_apply]
  ring

/-- `∇ G` is homogeneous in the derivative slot. -/
theorem covDerivBilinAt_einstein_smul_left (r : ℝ) (X v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (r • X) v w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  rw [covDerivBilinAt_einstein g cov x₀ h hx, covDerivBilinAt_einstein g cov x₀ h hx, hv_smul' x₀ hx]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- `∇ G` is additive in the first form slot. -/
theorem covDerivBilinAt_einstein_add_mid (X v v' w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (v + v') w =
      cov.covDerivBilinAt (cov.einsteinField g) x X v w + cov.covDerivBilinAt (cov.einsteinField g) x X v' w := by
  rw [covDerivBilinAt_einstein g cov x₀ h hx, covDerivBilinAt_einstein g cov x₀ h hx,
    covDerivBilinAt_einstein g cov x₀ h hx, hv_add x₀ hx]
  simp only [map_add, add_apply]
  ring

/-- `∇ G` is homogeneous in the first form slot. -/
theorem covDerivBilinAt_einstein_smul_mid (r : ℝ) (X v w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X (r • v) w =
      r * cov.covDerivBilinAt (cov.einsteinField g) x X v w := by
  rw [covDerivBilinAt_einstein g cov x₀ h hx, covDerivBilinAt_einstein g cov x₀ h hx, hv_smul' x₀ hx]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- The bilinear form `(X, v) ↦ (∇_X G)(v, w)` at a point of the chart domain. -/
def divForm (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun X v => cov.covDerivBilinAt (cov.einsteinField g) x X v w)
    (fun X X' v => covDerivBilinAt_einstein_add_left g cov x₀ h hx X X' v w)
    (fun r X v => covDerivBilinAt_einstein_smul_left g cov x₀ h hx r X v w)
    (fun X v v' => covDerivBilinAt_einstein_add_mid g cov x₀ h hx X v v' w)
    (fun r X v => covDerivBilinAt_einstein_smul_mid g cov x₀ h hx r X v w)


end Lin

section Div
variable (x : M) (h : cov.IsLeviCivita g)
include h

/-- **The divergence of the Einstein tensor is the coordinate sum** `g^{στ} (∇_σ G)(∂_τ, w)`. -/
theorem divBilinAt_einstein_coord (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.divBilinAt g (cov.einsteinField g) x w =
      ∑ σ, ∑ τ, (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ σ τ *
        cov.covDerivBilinAt (cov.einsteinField g) x (coordField x σ x) (coordField x τ x) w := by
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hzs
  have hp : x ∈ (tTriv (E := Fin n → ℝ) x).baseSet := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) x)
  set B := divForm g cov x h hp w with hB
  have h1 : cov.divBilinAt g (cov.einsteinField g) x w =
      ∑ i, ∑ j, (gramB g x (tb x))⁻¹ i j * B (tb x i) (tb x j) := rfl
  rw [h1, ← trace_raise g x B (tb x), trace_raise g x B (coordBasis x hp)]
  have e1 : ∀ k, coordBasis x hp k = coordField x k x := fun k =>
    (coordBasis_apply x hp k).trans (symmL_eq_coordField x hp k)
  have hG : gramB g x (coordBasis x hp) = g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
    ext i j
    show g.g x (coordBasis x hp i) (coordBasis x hp j) = _
    rw [e1 i, e1 j]
    have := g_coordField g x i j hy
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hzs] at this
    exact this
  rw [hG]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [e1 σ, e1 τ]
  rfl
end Div

/-- The derivative of a finite sum of scalar functions times constant vectors. -/
theorem hasFDerivAt_sum_smul {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → F → ℝ) (K : ι → κ → V) {y : F} (hc : ∀ i j, DifferentiableAt ℝ (c i j) y) :
    HasFDerivAt (fun y' => ∑ i, ∑ j, c i j y' • K i j)
      (∑ i, ∑ j, (fderiv ℝ (c i j) y).smulRight (K i j)) y :=
  HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => (hc i j).hasFDerivAt.smul_const _

section Val
variable (x : M) (h : cov.IsLeviCivita g)

/-- The derivative of the component form of the Einstein tensor along `eσ`. -/
theorem fderiv_einsteinComp {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target) (σ : Fin n) :
    fderiv ℝ (einsteinComp g x) y (Pi.single σ 1) =
      ∑ i, ∑ j, pd σ (einsteinTensor (g.coordMetric x) i j) y •
        ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) := by
  have hgc := g.isCoordMetric_coordMetric x
  have hc : ∀ σ ν : Fin n, DifferentiableAt ℝ (fun y' => einsteinTensor (g.coordMetric x) σ ν y') y := fun σ ν =>
    differentiableAt_of_contDiffOn (hgc.contDiffOn_einsteinTensor σ ν) hgc.isOpen hy
  have := (hasFDerivAt_sum_smul (fun σ ν y' => einsteinTensor (g.coordMetric x) σ ν y')
    (fun σ ν => (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)) hc).fderiv
  unfold einsteinComp
  rw [this]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [pd]

/-- The derivative of the Einstein component field along `∂_σ` at the base point of the chart. -/
theorem mvfderiv_BE_coordField (σ : Fin n) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (BE g x) x (coordField x σ x) =
      fderiv ℝ (einsteinComp g x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) (Pi.single σ 1) := by
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hzs
  rw [mvfderiv_eq_chart (BE g x) x (mdiffAt_BE g hzs) (coordField x σ x)]
  have hm := mfderiv_chart_coordField x σ hy
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hzs] at hm
  rw [hm]
  have hev : (BE g x ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) =ᶠ[nhds (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)]
      einsteinComp g x := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hy] with y' hy'
    simp only [Function.comp_apply, BE, (extChartAt 𝓘(ℝ, Fin n → ℝ) x).right_inv hy']
  rw [hev.fderiv_eq]

include h in
/-- **`(∇_σ G)(∂_τ, w)` in coordinates**: `Σ_ν w^ν DG_{στν}`. -/
theorem covDerivBilinAt_einstein_value (σ τ : Fin n) (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x (coordField x σ x) (coordField x τ x) w =
      ∑ ν, hv x x w ν * DG (g.coordMetric x) σ τ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hzs
  have hp : x ∈ (tTriv (E := Fin n → ℝ) x).baseSet := by
    simpa [tTriv, TangentBundle.trivializationAt_baseSet] using (mem_chart_source (Fin n → ℝ) x)
  rw [covDerivBilinAt_einstein g cov x h hp, hv_coordField x hp σ, hv_coordField x hp τ,
    mvfderiv_BE_coordField g x σ, fderiv_einsteinComp g x hy σ]
  set a := hv x x w with ha
  have hsa : a = ∑ ν, a ν • (Pi.single ν 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have hBE : ∀ u b : Fin n → ℝ, BE g x x u b = ∑ i, ∑ j, u i * b j *
      einsteinTensor (g.coordMetric x) i j (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := fun u b =>
    einsteinComp_apply g x _ u b
  have hg1 := gamHat_coord cov x g h hp
  have hgam1 : ∀ i, gamHat cov x x (Pi.single τ 1) (Pi.single σ 1) i =
      christoffel (g.coordMetric x) i σ τ (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := fun i => by
    rw [hg1 σ τ]; simp [Finset.sum_apply, Pi.single_apply]
  have hgam2 : ∀ k, gamHat cov x x a (Pi.single σ 1) k =
      ∑ ν, a ν * christoffel (g.coordMetric x) k σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := fun k => by
    conv_lhs => rw [hsa]
    simp only [map_sum, map_smul, sum_apply, smul_apply, hg1 σ,
      Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    simp
  unfold DG
  simp only [hBE, Finset.sum_apply, sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply]
  simp only [hgam1, hgam2]
  set y := extChartAt 𝓘(ℝ, Fin n → ℝ) x x
  have e1 : ∑ x_1, ∑ x_2, pd σ (einsteinTensor (g.coordMetric x) x_1 x_2) y * ((if x_1 = τ then (1 : ℝ) else 0) * a x_2) =
      ∑ ν, a ν * pd σ (einsteinTensor (g.coordMetric x) τ ν) y := by
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun ν _ => by ring
  have e2 : ∑ x_1, ∑ x_2, christoffel (g.coordMetric x) x_1 σ τ y * a x_2 * einsteinTensor (g.coordMetric x) x_1 x_2 y =
      ∑ ν, a ν * ∑ k, christoffel (g.coordMetric x) k σ τ y * einsteinTensor (g.coordMetric x) k ν y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ x_1, ∑ x_2, ((if x_1 = τ then (1 : ℝ) else 0) *
      ∑ ν, a ν * christoffel (g.coordMetric x) x_2 σ ν y) * einsteinTensor (g.coordMetric x) x_1 x_2 y =
      ∑ ν, a ν * ∑ k, christoffel (g.coordMetric x) k σ ν y * einsteinTensor (g.coordMetric x) τ k y := by
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

/-- **The Einstein tensor of a Levi-Civita connection is divergence free** (the statement of the task
`T-GE1-P8`, for a manifold modelled on `ℝⁿ` that is Hausdorff and of class `C²`, a `C^∞` connection). -/
theorem einstein_divergence_free_proved (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.divBilinAt g (cov.einsteinField g) x w = 0 := by
  have hzs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source := mem_extChartAt_source x
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hzs
  rw [divBilinAt_einstein_coord g cov x h w]
  simp only [covDerivBilinAt_einstein_value g cov x h, Finset.mul_sum]
  have key := einstein_div_coord (g.isCoordMetric_coordMetric x) hy
  have : ∀ ν, ∑ σ, ∑ τ, (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ σ τ *
      (hv x x w ν * DG (g.coordMetric x) σ τ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)) = 0 := fun ν => by
    have := key ν
    calc _ = hv x x w ν * ∑ σ, ∑ τ, (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ σ τ *
          DG (g.coordMetric x) σ τ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [this, mul_zero]
  calc _ = ∑ ν, ∑ σ, ∑ τ, (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ σ τ *
        (hv x x w ν * DG (g.coordMetric x) σ τ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)) := by
        exact (Finset.sum_congr rfl fun σ _ => Finset.sum_comm).trans Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun ν _ => this ν
end Main
end Lightlike
