module

public import Lightlike.Spacetime.Curvature
public import Lightlike.Spacetime.Corners.Curvature
public import Lightlike.Spacetime.NondegMetricBase
public import Lightlike.Spacetime.CurvatureWithin
public import Lightlike.Spacetime.Coordinates

/-!
# Connecting manifold-level Lorentzian metrics to coordinate metrics

`NondegMetric.coordMetricW g x₀ y = (g(∂ᵢ, ∂ⱼ))ᵢⱼ` is the matrix of components of a smooth
metric `g` on a manifold `M` modelled with corners on `ℝⁿ` in the chart at `x₀`, evaluated at the chart point `y`.

Main results: `NondegMetric.isCoordMetricW_coordMetric` - on the chart's target (relatively open in `range I`, containing
the image of `x₀`) these components form an `IsCoordMetricW`, for any model with corners; for a boundaryless model,
`NondegMetric.isCoordMetric_coordMetricW` - on the open chart target they form an `IsCoordMetric`: symmetric,
invertible, with `C^∞` entries. Signature: `LorentzianMetric.coordMetric_congr_etaW` (for a Lorentzian metric the
coordinate matrix is congruent to `η` on the chart target, any model with corners) and
`LorentzianMetric.isLorentzianCoordMetric_coordMetricW` (an `IsLorentzianCoordMetric`, boundaryless model). Hence every coordinate curvature statement in `Curvature.lean` /
`Lightlike/GR/Einstein.lean` applies to the coordinate expression of any smooth Lorentzian metric.

Proof ingredients (all from Mathlib):
* `TangentBundle.symmL_trivializationAt`: the derivative of the inverse chart is the inverse
  tangent-bundle trivialization, so `∂ᵢ` is the `i`-th vector of Mathlib's `localFrame` of that
  trivialization;
* symmetry and nondegeneracy of `g` (`IsLorentzianForm.symm`, `.bilinForm_nondegenerate`) and
  `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` (Gram matrix in a basis);
* `ContMDiffOn.clm_bundle_apply₂` (a smooth bilinear-form section applied to smooth sections is
  smooth), `contMDiffOn_localFrame_baseSet`, `contMDiffOn_extChartAt_symm`.

The open-set forms `IsCoordMetric` and `IsLorentzianCoordMetric` need a boundaryless model (`[I.Boundaryless]`); with
boundary or corners the relatively open form `IsCoordMetricW` is the one available.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 3 (curvature); S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 3 (curvature). The coordinate formulas for the Christoffel symbols and the Riemann, Ricci and scalar curvatures follow these texts' conventions.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/Coordinates.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

@[expose] public section

open Bundle Manifold Set
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The tangent-bundle trivialization in the chart at `x₀`. -/
abbrev chartTrivW (n : ℕ) {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] (x₀ : M) :=
  trivializationAt (Fin n → ℝ) (TangentSpace I : M → Type _) x₀

lemma symm_mem_chartTriv_baseSetW (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈ (chartTrivW (I := I) n x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  exact (extChartAt _ x₀).map_target hy

/-- The derivative of the inverse chart is the inverse tangent-bundle trivialization. -/
lemma mfderiv_extChartAt_symm_eqW (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt I x₀).target) :
    mfderivWithin 𝓘(ℝ, Fin n → ℝ) I (extChartAt I x₀).symm (range I) y =
      (chartTrivW (I := I) n x₀).symmL ℝ ((extChartAt I x₀).symm y) := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source I]; exact (extChartAt _ x₀).map_target hy
  rw [TangentBundle.symmL_trivializationAt hp, PartialEquiv.right_inv _ hy]

/-- The coordinate basis `(∂₀, …, ∂_{n-1})` of `T_p M` (chart at `x₀`), as a Mathlib `Basis`. -/
def coordBasisW (x₀ : M) {p : M} (hp : p ∈ (chartTrivW (I := I) n x₀).baseSet) :
    Module.Basis (Fin n) ℝ (TangentSpace I p) :=
  (Pi.basisFun ℝ (Fin n)).map ((chartTrivW (I := I) n x₀).linearEquivAt ℝ p hp).symm

lemma coordBasis_applyW (x₀ : M) {p : M} (hp : p ∈ (chartTrivW (I := I) n x₀).baseSet) (i : Fin n) :
    coordBasisW x₀ hp i = (chartTrivW (I := I) n x₀).symmL ℝ p (Pi.single i 1) := by
  simp [coordBasisW, Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hp]

/-- On the chart target, the coordinate components are `g(∂ᵢ, ∂ⱼ)` in the coordinate basis. -/
lemma NondegMetric.coordMetric_eqW (g : NondegMetric I M) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) (i j : Fin n) :
    g.coordMetricW x₀ y i j =
      g.g _ (coordBasisW x₀ (symm_mem_chartTriv_baseSetW x₀ hy) i)
        (coordBasisW x₀ (symm_mem_chartTriv_baseSetW x₀ hy) j) := by
  rw [coordBasis_applyW, coordBasis_applyW]
  simp only [NondegMetric.coordMetricW]
  rw [mfderiv_extChartAt_symm_eqW x₀ hy]
  rfl

/-- The coordinate matrix is symmetric (everywhere). -/
theorem NondegMetric.coordMetric_transposeW (g : NondegMetric I M)
    (x₀ : M) (y : Fin n → ℝ) : (g.coordMetricW x₀ y)ᵀ = g.coordMetricW x₀ y := by
  ext i j
  simp only [Matrix.transpose_apply, NondegMetric.coordMetricW]
  exact g.symm _ _ _

/-- The coordinate matrix is invertible on the chart target: it is the Gram matrix of the
nondegenerate form `g_p` in the coordinate basis of `T_p M`. -/
theorem NondegMetric.coordMetric_isUnit_detW (g : NondegMetric I M)
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) :
    IsUnit (g.coordMetricW x₀ y).det := by
  set p := (extChartAt I x₀).symm y
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (coordBasisW x₀ hp)).mp
    (g.bilinForm_nondegenerate p)
  have hmat : LinearMap.BilinForm.toMatrix (coordBasisW x₀ hp) (g.g p).toBilinForm =
      g.coordMetricW x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eqW x₀ hy]
    rfl
  rw [← hmat]
  exact hdet.isUnit

/-- The coordinate components are `C^∞` on the chart target. -/
theorem NondegMetric.coordMetric_smoothW (g : NondegMetric I M)
    (x₀ : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => g.coordMetricW x₀ y i j) (extChartAt I x₀).target := by
  set e := chartTrivW (I := I) n x₀
  set b := Pi.basisFun ℝ (Fin n)
  -- `p ↦ g_p(sᵢ(p), sⱼ(p))` is smooth on the chart domain, for the local frame `s` of `e`.
  have hF : ContMDiffOn I 𝓘(ℝ) ∞
      (fun p => g.g p (e.localFrame b i p) (e.localFrame b j p)) e.baseSet := by
    have h := ContMDiffOn.clm_bundle_apply₂ (F₁ := Fin n → ℝ) (F₂ := Fin n → ℝ)
      (E₃ := Bundle.Trivial M ℝ) (b := id) (s := e.baseSet)
      g.contMDiff.contMDiffOn (e.contMDiffOn_localFrame_baseSet _ b i)
      (e.contMDiffOn_localFrame_baseSet _ b j)
    intro p hp
    have := h p hp
    simp only [contMDiffWithinAt_totalSpace] at this
    exact this.2
  -- compose with the (smooth) inverse chart
  have hcomp := hF.comp (contMDiffOn_extChartAt_symm x₀) fun y hy =>
    symm_mem_chartTriv_baseSetW x₀ hy
  refine (contMDiffOn_iff_contDiffOn.mp hcomp).congr fun y hy => ?_
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  have hfr : ∀ k, e.localFrame b k ((extChartAt I x₀).symm y) =
      coordBasisW x₀ hp k := fun k => by
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) (i := k) hp]
    rfl
  simp only [Function.comp, g.coordMetric_eqW x₀ hy, hfr]

/-- **The link for any model with corners.** The coordinate components form an `IsCoordMetricW` on the chart target, relatively open in
`range I`: derivatives within `range I`, with no boundary hypothesis. -/
theorem NondegMetric.isCoordMetricW_coordMetric (g : NondegMetric I M) (x₀ : M) :
    IsCoordMetricW (range I) (g.coordMetricW x₀) (extChartAt I x₀).target where
  uniqueDiff := I.uniqueDiffOn
  closure x hx := by rw [← I.range_eq_closure_interior]; exact hx
  isRelOpen := ⟨I.symm ⁻¹' (chartAt H x₀).target,
    (chartAt H x₀).open_target.preimage I.continuous_symm, by rw [extChartAt_target, Set.inter_comm]⟩
  symm y _ := g.coordMetric_transposeW x₀ y
  isUnit_det _ hy := g.coordMetric_isUnit_detW x₀ hy
  smooth i j := g.coordMetric_smoothW x₀ i j

/-- **The link.** For any smooth Lorentzian metric `g` on `M` and any `x₀ : M`, the coordinate
components `g.coordMetricW x₀` form an `IsCoordMetric` (symmetric, invertible, `C^∞`) on the open
chart target, which contains the chart image of `x₀`. So the coordinate curvature predicates
(`IsFlatOn`, `IsVacuumSolution`) are meaningful for every manifold-level Lorentzian metric. -/
theorem NondegMetric.isCoordMetric_coordMetricW [I.Boundaryless] (g : NondegMetric I M)
    (x₀ : M) : IsCoordMetric (g.coordMetricW x₀) (extChartAt I x₀).target where
  isOpen := isOpen_extChartAt_target x₀
  symm y _ := g.coordMetric_transposeW x₀ y
  isUnit_det _ hy := g.coordMetric_isUnit_detW x₀ hy
  smooth i j := g.coordMetric_smoothW x₀ i j

/-- **Signature.** On the chart target the coordinate matrix is congruent to `η`:
`g(∂ᵢ,∂ⱼ) = (Pᵀ η P)ᵢⱼ`, where `P` is the change of basis from a Lorentz frame to the coordinate
basis. -/
theorem LorentzianMetric.coordMetric_congr_etaW (g : LorentzianMetric I M n)
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt I x₀).target) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧ g.coordMetricW x₀ y = Pᵀ * eta n * P := by
  set p := (extChartAt I x₀).symm y
  have hp := symm_mem_chartTriv_baseSetW x₀ hy
  obtain ⟨e, he⟩ := g.lorentzian p
  set f := coordBasisW x₀ hp
  refine ⟨e.toMatrix f, Matrix.isUnit_det_of_right_inverse (e.toMatrix_mul_toMatrix_flip f), ?_⟩
  ext i j
  rw [g.coordMetric_eqW x₀ hy, IsLorentzianForm.apply_eq_sum e he]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eta, Matrix.diagonal_apply,
    Module.Basis.toMatrix_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The coordinate components of a smooth Lorentzian metric have Lorentzian signature on the chart
target. -/
theorem LorentzianMetric.isLorentzianCoordMetric_coordMetricW [I.Boundaryless]
    (g : LorentzianMetric I M n) (x₀ : M) :
    IsLorentzianCoordMetric (g.coordMetricW x₀) (extChartAt I x₀).target :=
  ⟨g.isCoordMetric_coordMetricW x₀, fun _ hy => g.coordMetric_congr_etaW x₀ hy⟩

/-- For a Lorentzian metric the general coordinate matrix is the Lorentzian one (the same expression: `ofLorentzian` is the
underlying metric). Kept under this name for the files that cite it. -/
theorem NondegMetric.ofLorentzian_coordMetricW (g : LorentzianMetric I M n) (x₀ : M) :
    (NondegMetric.ofLorentzian g).coordMetricW x₀ = g.coordMetricW x₀ := rfl

end Lightlike
