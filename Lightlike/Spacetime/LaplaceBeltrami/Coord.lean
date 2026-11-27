import Mathlib
import Lightlike.Spacetime.VolumeMeasureFinite
import Lightlike.Spacetime.LaplaceBeltrami.Pairing
import Lightlike.Spacetime.LaplaceBeltrami.Smooth

/-!
# The Laplace–Beltrami operator in a chart and its weak form

For a smooth nondegenerate metric `g` on a manifold modelled on `ℝⁿ`, in the chart `φ₀` at `x₀`, with `ρ = √|det g|`
and `F = f ∘ φ₀⁻¹`:

* `NondegMetric.lapFlux g x₀ f i = ρ g^{ij} ∂ⱼF` (the flux of the gradient),
* `NondegMetric.laplaceCoord g x₀ f = -ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼF)` (the Laplace–Beltrami operator in divergence form, with the
  sign that makes it nonnegative for a Riemannian metric),
* `NondegMetric.laplaceBeltrami g f x`: the same in the chart at `x`, at `x`.

## Main results

* `NondegMetric.contDiffOn_lapFlux`, `NondegMetric.continuousOn_laplaceCoord`: regularity on the chart target.
* `NondegMetric.integral_mul_laplaceCoord` (**the weak form in a chart**): for `Ψ` smooth with compact support in the chart
  target, `∫ Ψ ρ (Δ₀ F) dy = ∫ ρ g^{ij} ∂ᵢΨ ∂ⱼF dy` (integration by parts, `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`).
* `NondegMetric.integral_mul_laplaceCoord_eq_dualPair` (**the weak form on the manifold**): for `ψ` smooth with compact
  support in the chart domain, `∫_M ψ · Δ₀f dvol_g = ∫_M g⁻¹(dψ, df) dvol_g`.

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §1.2, the coordinate formula of the
  Laplacian `Δ = -|g|^{-1/2} ∂ᵢ(|g|^{1/2} g^{ij} ∂ⱼ)` (sign convention of the source: nonnegative Laplacian). Comparison
  pending (not read at that location).
-/

open MeasureTheory Set Manifold Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The flux `ρ g^{ij} ∂ⱼ(f ∘ φ₀⁻¹)` (component `i`) in the chart at `x₀`. -/
def NondegMetric.lapFlux (x₀ : M) (f : M → ℝ) (i : Fin n) (y : Fin n → ℝ) : ℝ :=
  g.volDensity x₀ y * ∑ j, (g.coordMetric x₀ y)⁻¹ i j * coordPartial x₀ f y j

/-- **The Laplace–Beltrami operator in the chart at `x₀`**: `-ρ⁻¹ ∂ᵢ(ρ g^{ij} ∂ⱼ(f ∘ φ₀⁻¹))` at `y`. -/
def NondegMetric.laplaceCoord (x₀ : M) (f : M → ℝ) (y : Fin n → ℝ) : ℝ :=
  -(g.volDensity x₀ y)⁻¹ * ∑ i, fderiv ℝ (g.lapFlux x₀ f i) y (Pi.single i 1)

/-- **The Laplace–Beltrami operator** `Δ_g f (x)`, computed in the chart at `x`. -/
def NondegMetric.laplaceBeltrami (f : M → ℝ) (x : M) : ℝ :=
  g.laplaceCoord x f (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)

theorem top_add_one_le_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  exact le_of_eq (by rfl)

/-- The partial derivatives of a smooth function in a chart are smooth on the chart target. -/
theorem contDiffOn_coordPartial {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M) (j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => coordPartial x₀ f y j) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have h := ((contDiffOn_chart_comp hf x₀).fderiv_of_isOpen (isOpen_extChartAt_target x₀)
    top_add_one_le_top)
  exact h.clm_apply contDiffOn_const

/-- The flux is smooth on the chart target. -/
theorem NondegMetric.contDiffOn_lapFlux {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M)
    (i : Fin n) :
    ContDiffOn ℝ ∞ (g.lapFlux x₀ f i) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  (g.contDiffOn_volDensity x₀).mul
    (ContDiffOn.sum fun j _ => (g.contDiffOn_coordMetric_inv x₀ i j).mul (contDiffOn_coordPartial hf x₀ j))

/-- The coordinate Laplacian is continuous (indeed smooth) on the chart target. -/
theorem NondegMetric.contDiffOn_laplaceCoord {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M) :
    ContDiffOn ℝ ∞ (g.laplaceCoord x₀ f) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  have hρ : ContDiffOn ℝ ∞ (fun y => (g.volDensity x₀ y)⁻¹) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (g.contDiffOn_volDensity x₀).inv fun y hy => (g.volDensity_pos x₀ hy).ne'
  refine hρ.neg.mul (ContDiffOn.sum fun i _ => ?_)
  exact ((g.contDiffOn_lapFlux hf x₀ i).fderiv_of_isOpen (isOpen_extChartAt_target x₀)
    top_add_one_le_top).clm_apply contDiffOn_const

/-- A continuous function times a function continuous on an open set containing its topological support is
continuous. -/
theorem continuous_mul_of_tsupport_subset {E : Type*} [TopologicalSpace E] {U : Set E} (hU : IsOpen U)
    {Ψ H : E → ℝ} (hΨ : Continuous Ψ) (hH : ContinuousOn H U) (hs : tsupport Ψ ⊆ U) :
    Continuous fun y => Ψ y * H y := by
  refine continuous_of_tsupport fun y hy => ?_
  have hyU : y ∈ U := hs ((tsupport_mul_subset_left) hy)
  exact (hΨ.continuousAt.mul (hH.continuousAt (hU.mem_nhds hyU)))

/-- **The weak form of the Laplacian in a chart**: for `Ψ` smooth with compact support in the chart target,
`∫ Ψ ρ Δ₀F dy = ∫ ρ Σᵢⱼ g^{ij} ∂ᵢΨ ∂ⱼF dy`. -/
theorem NondegMetric.integral_mul_laplaceCoord {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) (x₀ : M)
    {Ψ : (Fin n → ℝ) → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨc : HasCompactSupport Ψ)
    (hΨs : tsupport Ψ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ∫ y, Ψ y * (g.volDensity x₀ y * g.laplaceCoord x₀ f y) =
      ∫ y, g.volDensity x₀ y *
        ∑ i, ∑ j, (g.coordMetric x₀ y)⁻¹ i j * fderiv ℝ Ψ y (Pi.single i 1) * coordPartial x₀ f y j := by
  set U := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target with hU
  have hUo : IsOpen U := isOpen_extChartAt_target x₀
  set V := fun i => g.lapFlux x₀ f i with hV
  have hVc : ∀ i, ContDiffOn ℝ ∞ (V i) U := fun i => g.contDiffOn_lapFlux hf x₀ i
  have hdΨ : ∀ i, Continuous fun y => fderiv ℝ Ψ y (Pi.single i 1) := fun i =>
    (hΨ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdV : ∀ i, ContinuousOn (fun y => fderiv ℝ (V i) y (Pi.single i 1)) U := fun i =>
    ((hVc i).continuousOn_fderiv_of_isOpen hUo (by simp)).clm_apply continuousOn_const
  -- the integrand of the left side is `-Σᵢ Ψ ∂ᵢVᵢ`
  have hL : ∀ y, Ψ y * (g.volDensity x₀ y * g.laplaceCoord x₀ f y) =
      -∑ i, Ψ y * fderiv ℝ (V i) y (Pi.single i 1) := by
    intro y
    by_cases hy : y ∈ U
    · have hρ := (g.volDensity_pos x₀ hy).ne'
      unfold NondegMetric.laplaceCoord
      rw [← Finset.mul_sum]
      field_simp
      rfl
    · have : Ψ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hΨs h)
      simp [this]
  have hint1 : ∀ i, Integrable fun y => Ψ y * fderiv ℝ (V i) y (Pi.single i 1) := fun i =>
    (continuous_mul_of_tsupport_subset hUo hΨ.continuous (hdV i) hΨs).integrable_of_hasCompactSupport
      (hΨc.mul_right)
  have hint2 : ∀ i, Integrable fun y => fderiv ℝ Ψ y (Pi.single i 1) * V i y := fun i =>
    (continuous_mul_of_tsupport_subset hUo (hdΨ i) (hVc i).continuousOn
      ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)).trans hΨs)).integrable_of_hasCompactSupport
      ((hΨc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).mul_right)
  have hint3 : ∀ i, Integrable fun y => Ψ y * V i y := fun i =>
    (continuous_mul_of_tsupport_subset hUo hΨ.continuous (hVc i).continuousOn hΨs).integrable_of_hasCompactSupport
      (hΨc.mul_right)
  have hibp : ∀ i, ∫ y, Ψ y * fderiv ℝ (V i) y (Pi.single i 1) =
      -∫ y, fderiv ℝ Ψ y (Pi.single i 1) * V i y := fun i =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint2 i) (hint1 i) (hint3 i)
      (fun y _ => (hΨ.differentiable (by simp)) y)
      (fun y hy => ((hVc i).contDiffAt (hUo.mem_nhds (hΨs hy))).differentiableAt (by simp))
  simp_rw [hL]
  rw [integral_neg, integral_finsetSum _ fun i _ => hint1 i]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, neg_neg, ← integral_finsetSum _ fun i _ => hint2 i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hV, NondegMetric.lapFlux, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Lightlike
