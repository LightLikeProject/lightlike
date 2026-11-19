import Lightlike.Spacetime.EHManifold.EinsteinIntrinsic
import Lightlike.Spacetime.EHManifold.MatterCoupling
import Lightlike.Spacetime.EHManifold.TestField

/-!
# Einstein's equation with matter from the stationarity of the total action

`total_action_stationary_iff`: let the matter action `SM` have the energy-momentum tensor `T` at `g`
(`HasMatterVariation`, for every compact set), and let `κ ≠ 0`. Then the total action
`S_H / κ + S_M` is stationary at `g` for every perturbation of compact support if and only if

`G(u, v) + Λ g(u, v) = κ T(u, v)` for all tangent vectors `u`, `v` at every point.

With `κ = 8πG` this is Carroll's (4.69) with the definition (4.70) of the energy-momentum tensor.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 4, eqs. (4.68) to
  (4.70), p. 116.
-/

open MeasureTheory Set Manifold TopologicalSpace Matrix Filter Metric
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Lightlike

/-- The contraction is homogeneous in its middle argument. -/
lemma formContract_smul_middle {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin n) ℝ V) (g A B : LinearMap.BilinForm ℝ V) (r : ℝ) :
    formContract b g (r • A) B = r * formContract b g A B := by
  unfold formContract
  rw [map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

set_option synthInstance.maxHeartbeats 400000

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]

/-- The matrix of a symmetric tensor field in the coordinate basis of a chart is its matrix of components. -/
lemma toMatrix_symBilinField (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    LinearMap.BilinForm.toMatrix (coordBasis x₁ (symm_mem_chartTriv_baseSet x₁ hy))
      (h.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm = h.coordComp x₁ y := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, h.coordComp_eq x₁ hy]
  rfl

/-- The matrix of the metric in the coordinate basis of a chart is its matrix of components. -/
lemma toMatrix_metric (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    LinearMap.BilinForm.toMatrix (coordBasis x₁ (symm_mem_chartTriv_baseSet x₁ hy))
      (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm = g.coordMetric x₁ y := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eq x₁ hy]
  rfl

/-- **The contraction `⟨T, h⟩_g` in the components of a chart.** -/
theorem contractWith_chart (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (T h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    contractWith g T h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) =
      ∑ α, ∑ β, h.coordComp x₁ y α β *
        ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) α β := by
  unfold contractWith
  rw [formContract_basis_indep _ (coordBasis x₁ (symm_mem_chartTriv_baseSet x₁ hy))]
  unfold formContract
  rw [toMatrix_metric g x₁ hy, toMatrix_symBilinField T x₁ hy, toMatrix_symBilinField h x₁ hy,
    trace_mul_of_symm _ _ (h.coordComp_symm x₁ y)]

/-- The raised components of a symmetric tensor field are continuous on the chart target. -/
lemma continuousOn_raised (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (T : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M) (α β : Fin n) :
    ContinuousOn (fun y => ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) α β)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
  have hc := g.isCoordMetric_coordMetric x₁
  simp only [Matrix.mul_apply]
  exact continuousOn_finsetSum _ fun j _ => (continuousOn_finsetSum _ fun i _ =>
    (hc.contDiffOn_inv α i).continuousOn.mul (T.coordComp_smooth x₁ i j).continuousOn).mul
      (hc.contDiffOn_inv j β).continuousOn

/-- `R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}` of the components of a metric is continuous on the chart target. -/
lemma continuousOn_einsteinUp (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (Λ : ℝ) (x₁ : M) (α β : Fin n) :
    ContinuousOn (fun y => einsteinUp (g.coordMetric x₁) Λ y α β)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := by
  have hc := g.isCoordMetric_coordMetric x₁
  have hinv : ∀ i j, ContinuousOn (fun y => (g.coordMetric x₁ y)⁻¹ i j)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target := fun i j => (hc.contDiffOn_inv i j).continuousOn
  unfold einsteinUp ricciUp
  exact ((continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    ((hinv α i).mul (hc.contDiffOn_ricci i j).continuousOn).mul (hinv j β)).sub
      ((continuousOn_const.mul hc.contDiffOn_scalarCurvature.continuousOn).mul (hinv α β))).add
        (continuousOn_const.mul (hinv α β))

/-- The contraction `⟨T, h⟩_g` is continuous on every chart domain. -/
lemma continuousOn_contractWith (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (T h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₁ : M) :
    ContinuousOn (contractWith g T h) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source := by
  have hF : ContinuousOn (fun y => ∑ α, ∑ β, h.coordComp x₁ y α β *
      ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) α β)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target :=
    continuousOn_finsetSum _ fun α _ => continuousOn_finsetSum _ fun β _ =>
      (h.coordComp_smooth x₁ α β).continuousOn.mul (continuousOn_raised g T x₁ α β)
  refine (hF.comp (continuousOn_extChartAt x₁) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).mapsTo).congr
    fun p hp => ?_
  have h1 := contractWith_chart g T h x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_source hp)
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).left_inv hp] at h1
  exact h1

/-- **Einstein's equation with a source, in a chart and intrinsically**: at the point with coordinates `y`,
the symmetric part of `-(1/κ) (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) + T^{αβ}` vanishes if and only if
`G(u, v) + Λ g(u, v) = κ T(u, v)` for all tangent vectors. -/
theorem sourced_einstein_chart_iff (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (T : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ κ : ℝ) (hκ : κ ≠ 0) (x₁ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target) :
    (∀ α β, (-(1 / κ) * einsteinUp (g.coordMetric x₁) Λ y α β +
          ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) α β) +
        (-(1 / κ) * einsteinUp (g.coordMetric x₁) Λ y β α +
          ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) β α) = 0) ↔
      ∀ u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y),
        (leviCivita g).einsteinField g _ u v + Λ * g.g _ u v = κ * T.h _ u v := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  have hLC := isLeviCivita_leviCivita g
  have hp := symm_mem_chartTriv_baseSet x₁ hy
  have hGu := g.coordMetric_isUnit_det x₁ hy
  have hGs := g.coordMetric_transpose x₁ y
  obtain ⟨X, hX⟩ : ∃ X : LinearMap.BilinForm ℝ
      (TangentSpace 𝓘(ℝ, Fin n → ℝ) ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)),
      X = -(1 / κ) • (einsteinBilin g (leviCivita g) hLC ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y) +
        Λ • (g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm) +
        (T.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).symm y)).toBilinForm := ⟨_, rfl⟩
  have hXapp : ∀ u v, X u v = -(1 / κ) * ((leviCivita g).einsteinField g _ u v + Λ * g.g _ u v) +
      T.h _ u v := by
    intro u v
    rw [hX]
    rfl
  have hXm : LinearMap.BilinForm.toMatrix (coordBasis x₁ hp) X =
      -(1 / κ) • ((Matrix.of fun σ ν => einsteinTensor (g.coordMetric x₁) σ ν y) +
        Λ • g.coordMetric x₁ y) + T.coordComp x₁ y := by
    rw [hX, map_add, map_smul, map_add, map_smul, toMatrix_metric g x₁ hy,
      toMatrix_symBilinField T x₁ hy, toMatrix_einsteinBilin g (leviCivita g) hLC x₁ hp,
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).right_inv hy]
  have hXsymm : ∀ u v, X u v = X v u := by
    intro u v
    rw [hXapp, hXapp, g.symm _ u v, T.symm _ u v]
    unfold Connection.einsteinField
    rw [ricciAt_symm_proved (leviCivita g) g hLC.1 hLC.2 _ u v, g.symm _ u v]
  have hXs : (LinearMap.BilinForm.toMatrix (coordBasis x₁ hp) X)ᵀ =
      LinearMap.BilinForm.toMatrix (coordBasis x₁ hp) X := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply]
    exact hXsymm _ _
  have hentry : ∀ α β, -(1 / κ) * einsteinUp (g.coordMetric x₁) Λ y α β +
        ((g.coordMetric x₁ y)⁻¹ * T.coordComp x₁ y * (g.coordMetric x₁ y)⁻¹) α β =
      ((g.coordMetric x₁ y)⁻¹ * LinearMap.BilinForm.toMatrix (coordBasis x₁ hp) X *
        (g.coordMetric x₁ y)⁻¹) α β := by
    intro α β
    rw [hXm, einsteinUp_eq_mul (g.coordMetric x₁) Λ y hGu]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
  simp only [hentry]
  rw [inv_mul_mul_inv_symm_part (g.coordMetric x₁ y) _ hGu hGs hXs]
  constructor
  · intro h0 u v
    have hform : X = 0 :=
      (LinearMap.BilinForm.toMatrix (coordBasis x₁ hp)).injective (by rw [h0, map_zero])
    have h1 : X u v = 0 := by rw [hform]; rfl
    rw [hXapp] at h1
    have h2 : (leviCivita g).einsteinField g _ u v + Λ * g.g _ u v = κ * T.h _ u v := by
      field_simp at h1
      linarith
    exact h2
  · intro h0
    have hform : X = 0 := LinearMap.ext₂ fun u v => by
      rw [hXapp, h0 u v]
      show -(1 / κ) * (κ * T.h _ u v) + T.h _ u v = 0
      field_simp
      ring
    rw [hform, map_zero]

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- **Einstein's equation with matter**: the total action `S_H / κ + S_M` is stationary at `g` if and only if
`G + Λ g = κ T`. -/
theorem total_action_stationary_iff (SM : NondegMetric 𝓘(ℝ, Fin n → ℝ) M → ℝ)
    (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (T : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (Λ κ : ℝ)
    (hκ : κ ≠ 0) (hM : ∀ K : Set M, IsCompact K → HasMatterVariation SM g T K) :
    (∀ (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (K : Set M), IsCompact K → (∀ p, p ∉ K → h.h p = 0) →
        HasDerivAt (fun t : ℝ => ehAction (g.perturb h t) Λ K / κ + SM (g.perturb h t)) 0 0) ↔
      ∀ (p : M) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p),
        (leviCivita g).einsteinField g p u v + Λ * g.g p u v = κ * T.h p u v := by
  haveI := contMDiffCovariantDerivative_leviCivita g
  constructor
  · intro hst p
    -- the chart statement at every point of the chart at `p`
    have hchart : ∀ y₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target, ∀ a b,
        (-(1 / κ) * einsteinUp (g.coordMetric p) Λ y₀ a b +
            ((g.coordMetric p y₀)⁻¹ * T.coordComp p y₀ * (g.coordMetric p y₀)⁻¹) a b) +
          (-(1 / κ) * einsteinUp (g.coordMetric p) Λ y₀ b a +
            ((g.coordMetric p y₀)⁻¹ * T.coordComp p y₀ * (g.coordMetric p y₀)⁻¹) b a) = 0 := by
      intro y₀ hy₀ a b
      refine symm_part_eq_zero_of_forall_test g p a b
        (fun y α β => -(1 / κ) * einsteinUp (g.coordMetric p) Λ y α β +
          ((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) α β)
        (fun α β => (continuousOn_const.mul (continuousOn_einsteinUp g Λ p α β)).add
          (continuousOn_raised g T p α β)) ?_ hy₀
      intro η hη hηc hηs
      have hKc := isCompact_symm_image_tsupport p hηc hηs
      have hsupp : ∀ q, q ∉ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm '' tsupport η →
          (testField p hη hηc hηs a b).h q = 0 := fun q hq => testField_eq_zero p hη hηc hηs a b hq
      have hder := hst (testField p hη hηc hηs a b) _ hKc hsupp
      have hv := hasDerivAt_total_action SM g T (testField p hη hηc hηs a b) hKc hsupp Λ κ
        (hM _ hKc)
      have h0 := hv.unique hder
      rw [setIntegral_testField p hη hηc hηs g a b (fun h => ehIntegrand g h Λ)
          (fun y α β => einsteinUp (g.coordMetric p) Λ y α β)
          (fun h => continuousOn_ehIntegrand g h Λ p) (fun h y hy => ehIntegrand_chart g h Λ p hy),
        setIntegral_testField p hη hηc hηs g a b (fun h => contractWith g T h)
          (fun y α β => ((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) α β)
          (fun h => continuousOn_contractWith g T h p)
          (fun h y hy => contractWith_chart g T h p hy)] at h0
      have hcK : IsCompact (tsupport η) := hηc.isCompact
      have i1 : IntegrableOn (fun y => NondegMetric.volDensity g p y * (η y *
          (einsteinUp (g.coordMetric p) Λ y a b + einsteinUp (g.coordMetric p) Λ y b a)))
          (tsupport η) volume :=
        ContinuousOn.integrableOn_compact hcK
          (((NondegMetric.continuousOn_volDensity g p).mono hηs).mul
            (hη.continuous.continuousOn.mul
              (((continuousOn_einsteinUp g Λ p a b).add (continuousOn_einsteinUp g Λ p b a)).mono hηs)))
      have i2 : IntegrableOn (fun y => NondegMetric.volDensity g p y * (η y *
          (((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) a b +
            ((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) b a)))
          (tsupport η) volume :=
        ContinuousOn.integrableOn_compact hcK
          (((NondegMetric.continuousOn_volDensity g p).mono hηs).mul
            (hη.continuous.continuousOn.mul
              (((continuousOn_raised g T p a b).add (continuousOn_raised g T p b a)).mono hηs)))
      have hneg : IntegrableOn (fun y => -(NondegMetric.volDensity g p y * (η y *
          (einsteinUp (g.coordMetric p) Λ y a b + einsteinUp (g.coordMetric p) Λ y b a)) / κ))
          (tsupport η) volume := (i1.div_const κ).neg
      have e1 : ∫ y in tsupport η, (-(NondegMetric.volDensity g p y * (η y *
            (einsteinUp (g.coordMetric p) Λ y a b + einsteinUp (g.coordMetric p) Λ y b a)) / κ) +
          NondegMetric.volDensity g p y * (η y *
            (((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) a b +
              ((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) b a))) =
          -(∫ y in tsupport η, NondegMetric.volDensity g p y * (η y *
            (einsteinUp (g.coordMetric p) Λ y a b + einsteinUp (g.coordMetric p) Λ y b a))) / κ +
          ∫ y in tsupport η, NondegMetric.volDensity g p y * (η y *
            (((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) a b +
              ((g.coordMetric p y)⁻¹ * T.coordComp p y * (g.coordMetric p y)⁻¹) b a)) := by
        rw [integral_add hneg i2, integral_neg, integral_div, neg_div]
      rw [← h0, ← e1]
      refine setIntegral_congr_fun (isClosed_tsupport η).measurableSet fun y _ => ?_
      show NondegMetric.volDensity g p y * (η y * (_ + _)) = _
      field_simp
      ring
    have h1 := (sourced_einstein_chart_iff g T Λ κ hκ p (mem_extChartAt_target p)).1
      (fun α β => hchart _ (mem_extChartAt_target p) α β)
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p).left_inv (mem_extChartAt_source p)] at h1
    exact h1
  · intro hE h K hK hsupp
    have hv := hasDerivAt_total_action SM g T h hK hsupp Λ κ (hM K hK)
    have hpt : ∀ p, ehIntegrand g h Λ p = κ * contractWith g T h p := by
      intro p
      have hform : einsteinBilin g (leviCivita g) (isLeviCivita_leviCivita g) p +
          Λ • (g.g p).toBilinForm = κ • (T.h p).toBilinForm :=
        LinearMap.ext₂ fun u v => hE p u v
      unfold ehIntegrand contractWith
      rw [hform, formContract_smul_middle]
    have hz : -(∫ p in K, ehIntegrand g h Λ p ∂(NondegMetric.volumeMeasure g)) / κ +
        ∫ p in K, contractWith g T h p ∂(NondegMetric.volumeMeasure g) = 0 := by
      simp only [hpt]
      rw [integral_const_mul]
      field_simp
      ring
    rw [hz] at hv
    exact hv

end Lightlike
