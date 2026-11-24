import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.ChartChange

/-!
# The transition map between two charts is a chart change of the coordinate metrics (G1-006 manifold lift)

For two points `x₀, x₁` of a Lorentzian manifold the transition `φ = ψ₁ ∘ ψ₀.symm` between the preferred charts
`ψᵢ = extChartAt x_i` is a smooth map with Jacobian `chgL x₀ x₁` and it pulls the coordinate metric at `x₁` back to the
coordinate metric at `x₀` (`NondegMetric.coordMetric_chart_change`); in particular it is a `IsChartChange`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The derivative of the transition map between the charts at `x₀` and `x₁` is the chart-change map `chgL`. -/
theorem fderiv_transition (x₀ x₁ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target)
    (hp₁ : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₁).source) :
    fderiv ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) y =
      chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  set ψ₀ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ with hψ₀
  set ψ₁ := extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ with hψ₁
  set p := ψ₀.symm y with hp
  have hs₀ : p ∈ (chartAt (Fin n → ℝ) x₀).source := by
    have := ψ₀.map_target hy
    rwa [hψ₀, extChartAt_source] at this
  have hd₀ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₀.symm y :=
    ((mdifferentiableOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀)) y hy).mdifferentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hy)
  have hd₁ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₁ (ψ₀.symm y) :=
    mdifferentiableAt_extChartAt hp₁
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, Fin n → ℝ)) (I' := 𝓘(ℝ, Fin n → ℝ)) (I'' := 𝓘(ℝ, Fin n → ℝ)) y hd₁ hd₀
  have h1 : (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _) x₁).continuousLinearMapAt ℝ p =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₁ p :=
    TangentBundle.continuousLinearMapAt_trivializationAt hp₁
  have h2 : (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _) x₀).symmL ℝ p =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₀.symm (ψ₀ p) :=
    by
      have := TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ, Fin n → ℝ)) hs₀
      simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at this
      exact this
  have e : ψ₀ p = y := ψ₀.right_inv hy
  rw [e] at h2
  have key : fderiv ℝ (ψ₁ ∘ ψ₀.symm) y =
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₁ p).comp
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ₀.symm y) := by
    exact (mfderiv_eq_fderiv (f := ψ₁ ∘ ψ₀.symm) (x := y)).symm.trans hcomp
  rw [key]
  unfold chgL
  rw [h1, h2]
  rfl

/-- The domain of the transition map: the part of the target of the chart at `x₀` that lands in the source of the chart at
`x₁`. -/
def transitionDom (x₀ x₁ : M) : Set (Fin n → ℝ) :=
  (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target ∩
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm ⁻¹' (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).source

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
theorem isOpen_transitionDom (x₀ x₁ : M) : IsOpen (transitionDom (n := n) x₀ x₁) :=
  (continuousOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) x₀).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀) (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x₁)

/-- The Jacobian of the transition map is `chgL`. -/
theorem jac_transition (x₀ x₁ : M) {y : Fin n → ℝ} (hy : y ∈ transitionDom (n := n) x₀ x₁) (μ a : Fin n) :
    jac (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) y μ a =
      chgL x₀ x₁ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) (Pi.single a 1) μ := by
  have hp₁ : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₁).source := by
    simpa [extChartAt_source] using hy.2
  have hd₀ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y :=
    ((mdifferentiableOn_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x₀)) y hy.1).mdifferentiableAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) x₀).mem_nhds hy.1)
  have hd₁ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁)
      ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := mdifferentiableAt_extChartAt hp₁
  have hφ : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) y :=
    (hd₁.comp y hd₀).differentiableAt
  rw [← fderiv_transition x₀ x₁ hy.1 hp₁]
  unfold jac pd
  have := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) μ).hasFDerivAt.comp y
    hφ.hasFDerivAt).fderiv
  exact congrArg (fun L => L (Pi.single a 1)) this

/-- **The transition map pulls the coordinate metric at `x₁` back to the coordinate metric at `x₀`.** -/
theorem pullback_transition [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M] (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ x₁ : M) {y : Fin n → ℝ}
    (hy : y ∈ transitionDom (n := n) x₀ x₁) :
    pullback (g.coordMetric x₁) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm) y =
      g.coordMetric x₀ y := by
  have hp₁ : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₁).source := by
    simpa [extChartAt_source] using hy.2
  ext a b
  simp only [pullback, jac_transition x₀ x₁ hy]
  rw [g.coordMetric_chart_change x₀ x₁ hy.1 hp₁ a b]
  rfl

/-- The transition map between two preferred charts is smooth on its domain. -/
theorem contDiffOn_transition (x₀ x₁ : M) :
    ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)
      (transitionDom (n := n) x₀ x₁) := by
  have h := (𝓘(ℝ, Fin n → ℝ)).contDiffOn_extendCoordChange (n := ∞) (M := M)
    (IsManifold.subset_maximalAtlas (chart_mem_atlas (Fin n → ℝ) x₀))
    (IsManifold.subset_maximalAtlas (chart_mem_atlas (Fin n → ℝ) x₁))
  have h' : ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)
      ((𝓘(ℝ, Fin n → ℝ)).extendCoordChange (chartAt (Fin n → ℝ) x₀) (chartAt (Fin n → ℝ) x₁)).source := h
  refine h'.mono ?_
  intro y hy
  simpa [ModelWithCorners.extendCoordChange, transitionDom, PartialEquiv.trans_source] using hy

/-- **The transition map between the preferred charts is a chart change** of the coordinate metrics of any
nondegenerate metric. -/
theorem isChartChange_transition [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
    [MeasurableSpace M] [BorelSpace M] (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ x₁ : M) :
    IsChartChange (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm)
      (transitionDom (n := n) x₀ x₁) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).target where
  isOpen := isOpen_transitionDom x₀ x₁
  mapsTo := fun y hy => by
    have := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₁).map_source hy.2
    exact this
  smooth := fun μ => (contDiffOn_pi.1 (contDiffOn_transition x₀ x₁)) μ
  isUnit_det := fun y hy => by
    have h1 : IsUnit (g.coordMetric x₀ y).det := g.coordMetric_isUnit_det x₀ hy.1
    rw [← pullback_transition g x₀ x₁ hy, pullback_eq_mul, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose] at h1
    exact isUnit_of_mul_isUnit_right h1

end Lightlike
