import Mathlib
import Lightlike.Spacetime.VolumeMeasure

/-!
# The pairing of two differentials by the inverse metric

For a smooth nondegenerate metric `g` on a manifold modelled on `ℝⁿ` and two functions `f, h`, the pairing
`g⁻¹(df, dh) = g^{ij} ∂ᵢf ∂ⱼh` of their differentials, computed in the chart at the point
(`NondegMetric.dualPair`), is the same in every chart containing the point (`NondegMetric.dualPair_eq_coord`): under a
change of chart with Jacobian `C` the components of the differentials transform by `Cᵀ` and the metric by
`Cᵀ g C` (`NondegMetric.coordMetric_chart_change`). This is the first-order part of the Laplace–Beltrami operator: its
weak form is `∫ φ Δf = ∫ g⁻¹(dφ, df)`.

## Main definitions

* `coordPartial x₀ f y i`: the partial derivative `∂ᵢ (f ∘ φ₀⁻¹)` at `y` in the chart at `x₀`.
* `NondegMetric.dualPairCoord g x₀ f h y`: `Σᵢⱼ g^{ij}(y) ∂ᵢ(f ∘ φ₀⁻¹)(y) ∂ⱼ(h ∘ φ₀⁻¹)(y)`.
* `NondegMetric.dualPair g f h x`: the same in the chart at `x`, at `x`.

## Main results

* `coordPartial_chart_change`: the chain rule `∂ᵢ(f∘φ₀⁻¹) = Σ_μ ∂_μ(f∘φ₁⁻¹) C_{μi}`.
* `NondegMetric.dualPairCoord_chart_change`, `NondegMetric.dualPair_eq_coord`: chart independence.
-/

open Set Manifold Matrix
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]

/-- The partial derivative `∂ᵢ (f ∘ φ₀⁻¹)` at `y`, in the chart at `x₀`. -/
def coordPartial (x₀ : M) (f : M → ℝ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) y (Pi.single i 1)

/-- A smooth function is smooth in every chart, on the chart target. The same statement, with the arguments in the other
order, is `Lightlike.contDiffOn_comp_extChartAt_symm` in `Lightlike/Spacetime/NullHypersurface.lean`; this file does not import
it because that file pulls in the Raychaudhuri layer. -/
theorem contDiffOn_chart_comp {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M) :
    ContDiffOn ℝ ∞ (f ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have := (contMDiff_iff.1 hf).2 x₀ (0 : ℝ)
  simpa [extChartAt_model_space_eq_id] using this

/-- The coordinate change between two charts is differentiable at every point of the overlap. -/
theorem differentiableAt_chartChange (x₀ x₁ p : M) (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source)
    (hp1 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    DifferentiableAt ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) := by
  set φ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀
  set φ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁
  have hcd := contDiffOn_ext_coord_change (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x₁ x₀
  have hmem : φ₀ p ∈ (φ₀.symm ≫ φ₁).source := by
    simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage]
    exact ⟨φ₀.map_source hp0, by rwa [φ₀.left_inv hp0]⟩
  have hopen : IsOpen (φ₀.symm ≫ φ₁).source := by
    simp only [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
      (isOpen_extChartAt_source x₁)
  exact (hcd.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)

/-- **The chain rule between two charts**: `∂ᵢ(f∘φ₀⁻¹)(φ₀ p) = Σ_μ ∂_μ(f∘φ₁⁻¹)(φ₁ p) · C_{μi}` with `C` the chart-change
map at `p`. -/
theorem coordPartial_chart_change {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ x₁ p : M)
    (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hp1 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source)
    (i : Fin n) :
    coordPartial x₀ f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) i =
      ∑ μ, coordPartial x₁ f (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) μ * chgL x₀ x₁ p (Pi.single i 1) μ := by
  have hc0 : p ∈ (chartAt (Fin n → ℝ) x₀).source := by rwa [extChartAt_source] at hp0
  have hc1 : p ∈ (chartAt (Fin n → ℝ) x₁).source := by rwa [extChartAt_source] at hp1
  set φ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hφ₀
  set φ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hφ₁
  have hcomp : f ∘ φ₀.symm =ᶠ[𝓝 (φ₀ p)] (f ∘ φ₁.symm) ∘ (φ₁ ∘ φ₀.symm) := by
    have hopen : IsOpen (φ₀.target ∩ φ₀.symm ⁻¹' φ₁.source) :=
      (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
        (isOpen_extChartAt_source x₁)
    filter_upwards [hopen.mem_nhds ⟨φ₀.map_source hp0, by
      simp only [mem_preimage]; rwa [φ₀.left_inv hp0]⟩] with y hy
    simp only [Function.comp_apply]
    rw [φ₁.left_inv hy.2]
  have hd1 : DifferentiableAt ℝ (f ∘ φ₁.symm) (φ₁ p) :=
    ((contDiffOn_chart_comp hf x₁).contDiffAt
      ((isOpen_extChartAt_target x₁).mem_nhds (φ₁.map_source hp1))).differentiableAt (by simp)
  have hd2 := differentiableAt_chartChange x₀ x₁ p hp0 hp1
  have hτ : (φ₁ ∘ φ₀.symm) (φ₀ p) = φ₁ p := by simp only [Function.comp_apply]; rw [φ₀.left_inv hp0]
  unfold coordPartial
  rw [← hφ₀, ← hφ₁, hcomp.fderiv_eq, fderiv_comp _ (hτ ▸ hd1) hd2, ContinuousLinearMap.comp_apply, hτ,
    ← chgL_eq x₀ x₁ p hc0 hc1]
  conv_lhs => rw [show chgL x₀ x₁ p (Pi.single i 1) = ∑ μ, chgL x₀ x₁ p (Pi.single i 1) μ • (Pi.single μ 1 : Fin n → ℝ) by
    ext k; simp [Finset.sum_apply, Pi.single_apply]]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun μ _ => mul_comm _ _

variable (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- `g⁻¹(df, dh)` in the chart at `x₀`, at `y`: `Σᵢⱼ g^{ij}(y) ∂ᵢ(f∘φ₀⁻¹)(y) ∂ⱼ(h∘φ₀⁻¹)(y)`. -/
def NondegMetric.dualPairCoord (x₀ : M) (f h : M → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (g.coordMetric x₀ y)⁻¹ i j * coordPartial x₀ f y i * coordPartial x₀ h y j

/-- **The pairing `g⁻¹(df, dh)` of two differentials at `x`**, computed in the chart at `x`. -/
def NondegMetric.dualPair (f h : M → ℝ) (x : M) : ℝ :=
  g.dualPairCoord x f h (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)

theorem NondegMetric.dualPairCoord_eq_dotProduct (x₀ : M) (f h : M → ℝ) (y : Fin n → ℝ) :
    g.dualPairCoord x₀ f h y = (fun i => coordPartial x₀ f y i) ⬝ᵥ
      ((g.coordMetric x₀ y)⁻¹ *ᵥ fun j => coordPartial x₀ h y j) := by
  unfold NondegMetric.dualPairCoord
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The pairing `g⁻¹(df, dh)` is the same in any two charts** at a point of their overlap. -/
theorem NondegMetric.dualPairCoord_chart_change {f h : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hh : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ h) (x₀ x₁ p : M)
    (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) (hp1 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source) :
    g.dualPairCoord x₀ f h (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) =
      g.dualPairCoord x₁ f h (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ p) := by
  have hc1 : p ∈ (chartAt (Fin n → ℝ) x₁).source := by rwa [extChartAt_source] at hp1
  set φ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hφ₀
  set φ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hφ₁
  set C : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun μ a => chgL x₀ x₁ p (Pi.single a 1) μ with hC
  have hy0 : φ₀ p ∈ φ₀.target := φ₀.map_source hp0
  have hy1 : φ₁ p ∈ φ₁.target := φ₁.map_source hp1
  have hG : g.coordMetric x₀ (φ₀ p) = Cᵀ * g.coordMetric x₁ (φ₁ p) * C := by
    ext a b
    have h := g.coordMetric_chart_change x₀ x₁ hy0 (by rw [φ₀.left_inv hp0]; exact hc1) a b
    rw [φ₀.left_inv hp0] at h
    rw [h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hC, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet0 : IsUnit (g.coordMetric x₀ (φ₀ p)).det := g.coordMetric_isUnit_det x₀ hy0
  have hdetC : IsUnit C.det := by
    rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet0
    exact isUnit_of_mul_isUnit_right hdet0
  have hvec : ∀ {u : M → ℝ}, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ u →
      (fun i => coordPartial x₀ u (φ₀ p) i) = Cᵀ *ᵥ fun μ => coordPartial x₁ u (φ₁ p) μ := by
    intro u hu
    funext i
    rw [coordPartial_chart_change hu x₀ x₁ p hp0 hp1 i]
    simp only [mulVec, dotProduct, Matrix.transpose_apply, hC, Matrix.of_apply]
    exact Finset.sum_congr rfl fun μ _ => mul_comm _ _
  rw [g.dualPairCoord_eq_dotProduct, g.dualPairCoord_eq_dotProduct, hvec hf, hvec hh]
  set a := fun μ => coordPartial x₁ f (φ₁ p) μ
  set b := fun μ => coordPartial x₁ h (φ₁ p) μ
  have hCt : IsUnit Cᵀ.det := by rwa [Matrix.det_transpose]
  have hinv : (g.coordMetric x₀ (φ₀ p))⁻¹ = C⁻¹ * (g.coordMetric x₁ (φ₁ p))⁻¹ * (Cᵀ)⁻¹ := by
    rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  have h1 : (g.coordMetric x₀ (φ₀ p))⁻¹ *ᵥ (Cᵀ *ᵥ b) = C⁻¹ *ᵥ ((g.coordMetric x₁ (φ₁ p))⁻¹ *ᵥ b) := by
    rw [hinv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hCt,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have h2 : ∀ w : Fin n → ℝ, (Cᵀ *ᵥ a) ⬝ᵥ (C⁻¹ *ᵥ w) = a ⬝ᵥ w := fun w => by
    rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdetC,
      Matrix.vecMul_one]
  rw [h1, h2]

/-- **`g⁻¹(df, dh)` at `p` in any chart containing `p`.** -/
theorem NondegMetric.dualPair_eq_coord {f h : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hh : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ h) (x₀ p : M)
    (hp0 : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    g.dualPair f h p = g.dualPairCoord x₀ f h (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ p) :=
  (g.dualPairCoord_chart_change hf hh x₀ p p hp0 (mem_extChartAt_source p)).symm

end Lightlike
