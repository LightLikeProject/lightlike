module

public import Lightlike.Spacetime.Curvature

/-!
# Connecting manifold-level Lorentzian metrics to coordinate metrics

`LorentzianMetric.coordMetric g x₀ y = (g(∂ᵢ, ∂ⱼ))ᵢⱼ` is the matrix of components of a smooth
Lorentzian metric `g` on a manifold `M` (modelled on `ℝⁿ`, no boundary) in the chart at `x₀`,
evaluated at the chart point `y`.

Main result: `LorentzianMetric.isCoordMetric_coordMetric` - on the chart's target (an open set
containing the image of `x₀`), these components form an `IsCoordMetric`: symmetric, invertible,
with `C^∞` entries. Hence every coordinate curvature statement in `Curvature.lean` /
`Einstein.lean` applies to the coordinate expression of any smooth Lorentzian metric.

Proof ingredients (all from Mathlib):
* `TangentBundle.symmL_trivializationAt`: the derivative of the inverse chart is the inverse
  tangent-bundle trivialization, so `∂ᵢ` is the `i`-th vector of Mathlib's `localFrame` of that
  trivialization;
* symmetry and nondegeneracy of `g` (`IsLorentzianForm.symm`, `.bilinForm_nondegenerate`) and
  `LinearMap.BilinForm.nondegenerate_iff_det_ne_zero` (Gram matrix in a basis);
* `ContMDiffOn.clm_bundle_apply₂` (a smooth bilinear-form section applied to smooth sections is
  smooth), `contMDiffOn_localFrame_baseSet`, `contMDiffOn_extChartAt_symm`.

Not covered: Lorentzian *signature* of the coordinate matrix (true by Sylvester's law, not needed
for `IsCoordMetric`), and manifolds with boundary.

**References.** R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 3 (curvature); S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 3 (curvature). The coordinate formulas for the Christoffel symbols and the Riemann, Ricci and scalar curvatures follow these texts' conventions.
-/

@[expose] public section

open Bundle Manifold Set
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The tangent-bundle trivialization in the chart at `x₀`. -/
abbrev chartTriv (n : ℕ) {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (x₀ : M) :=
  trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _) x₀

lemma symm_mem_chartTriv_baseSet (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartTriv n x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, ← extChartAt_source 𝓘(ℝ, Fin n → ℝ)]
  exact (extChartAt _ x₀).map_target hy

/-- The derivative of the inverse chart is the inverse tangent-bundle trivialization. -/
lemma mfderiv_extChartAt_symm_eq (x₀ : M) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y =
      (chartTriv n x₀).symmL ℝ ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) := by
  have hp : (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y ∈ (chartAt (Fin n → ℝ) x₀).source := by
    rw [← extChartAt_source 𝓘(ℝ, Fin n → ℝ)]; exact (extChartAt _ x₀).map_target hy
  rw [TangentBundle.symmL_trivializationAt hp, PartialEquiv.right_inv _ hy]
  simp [mfderivWithin_univ]
  rfl

/-- The coordinate basis `(∂₀, …, ∂_{n-1})` of `T_p M` (chart at `x₀`), as a Mathlib `Basis`. -/
def coordBasis (x₀ : M) {p : M} (hp : p ∈ (chartTriv n x₀).baseSet) :
    Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :=
  (Pi.basisFun ℝ (Fin n)).map ((chartTriv n x₀).linearEquivAt ℝ p hp).symm

lemma coordBasis_apply (x₀ : M) {p : M} (hp : p ∈ (chartTriv n x₀).baseSet) (i : Fin n) :
    coordBasis x₀ hp i = (chartTriv n x₀).symmL ℝ p (Pi.single i 1) := by
  simp [coordBasis, Trivialization.linearEquivAt_symm_apply, Trivialization.symmL_apply _ hp]

/-- On the chart target, the coordinate components are `g(∂ᵢ, ∂ⱼ)` in the coordinate basis. -/
lemma LorentzianMetric.coordMetric_eq (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (i j : Fin n) :
    g.coordMetric x₀ y i j =
      g.g _ (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) i)
        (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) j) := by
  rw [coordBasis_apply, coordBasis_apply]
  simp only [LorentzianMetric.coordMetric]
  rw [mfderiv_extChartAt_symm_eq x₀ hy]
  rfl

/-- The coordinate matrix is symmetric (everywhere). -/
theorem LorentzianMetric.coordMetric_transpose (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (x₀ : M) (y : Fin n → ℝ) : (g.coordMetric x₀ y)ᵀ = g.coordMetric x₀ y := by
  ext i j
  simp only [Matrix.transpose_apply, LorentzianMetric.coordMetric]
  exact g.symm _ _ _

/-- The coordinate matrix is invertible on the chart target: it is the Gram matrix of the
nondegenerate form `g_p` in the coordinate basis of `T_p M`. -/
theorem LorentzianMetric.coordMetric_isUnit_det (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    IsUnit (g.coordMetric x₀ y).det := by
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (coordBasis x₀ hp)).mp
    (g.lorentzian p).bilinForm_nondegenerate
  have hmat : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp) (g.g p).toBilinForm =
      g.coordMetric x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eq x₀ hy]
    rfl
  rw [← hmat]
  exact hdet.isUnit

/-- The coordinate components are `C^∞` on the chart target. -/
theorem LorentzianMetric.coordMetric_smooth (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (x₀ : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => g.coordMetric x₀ y i j) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  set e := chartTriv n x₀
  set b := Pi.basisFun ℝ (Fin n)
  -- `p ↦ g_p(sᵢ(p), sⱼ(p))` is smooth on the chart domain, for the local frame `s` of `e`.
  have hF : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞
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
    symm_mem_chartTriv_baseSet x₀ hy
  refine (contMDiffOn_iff_contDiffOn.mp hcomp).congr fun y hy => ?_
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hfr : ∀ k, e.localFrame b k ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      coordBasis x₀ hp k := fun k => by
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) (i := k) hp]
    rfl
  simp only [Function.comp, g.coordMetric_eq x₀ hy, hfr]

/-- **The link.** For any smooth Lorentzian metric `g` on `M` and any `x₀ : M`, the coordinate
components `g.coordMetric x₀` form an `IsCoordMetric` (symmetric, invertible, `C^∞`) on the open
chart target, which contains the chart image of `x₀`. So the coordinate curvature predicates
(`IsFlatOn`, `IsVacuumSolution`) are meaningful for every manifold-level Lorentzian metric. -/
theorem LorentzianMetric.isCoordMetric_coordMetric (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (x₀ : M) : IsCoordMetric (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target where
  isOpen := isOpen_extChartAt_target x₀
  symm y _ := g.coordMetric_transpose x₀ y
  isUnit_det _ hy := g.coordMetric_isUnit_det x₀ hy
  smooth i j := g.coordMetric_smooth x₀ i j

/-- **Signature.** On the chart target the coordinate matrix is congruent to `η`:
`g(∂ᵢ,∂ⱼ) = (Pᵀ η P)ᵢⱼ`, where `P` is the change of basis from a Lorentz frame to the coordinate
basis. -/
theorem LorentzianMetric.coordMetric_congr_eta (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P.det ∧ g.coordMetric x₀ y = Pᵀ * eta n * P := by
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  obtain ⟨e, he⟩ := g.lorentzian p
  set f := coordBasis x₀ hp
  refine ⟨e.toMatrix f, Matrix.isUnit_det_of_right_inverse (e.toMatrix_mul_toMatrix_flip f), ?_⟩
  ext i j
  rw [g.coordMetric_eq x₀ hy, IsLorentzianForm.apply_eq_sum e he]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eta, Matrix.diagonal_apply,
    Module.Basis.toMatrix_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The coordinate components of a smooth Lorentzian metric have Lorentzian signature on the chart
target. -/
theorem LorentzianMetric.isLorentzianCoordMetric_coordMetric
    (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) :
    IsLorentzianCoordMetric (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  ⟨g.isCoordMetric_coordMetric x₀, fun _ hy => g.coordMetric_congr_eta x₀ hy⟩

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- …and the chart target is a neighbourhood of `x₀`'s coordinates. -/
lemma mem_chart_target (x₀ : M) :
    extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x₀ ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
  mem_extChartAt_target x₀

end Lightlike
