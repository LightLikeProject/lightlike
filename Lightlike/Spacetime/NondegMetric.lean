import Lightlike.Spacetime.Coordinates

/-!
# Smooth symmetric nondegenerate bilinear fields on a manifold (general metrics)

`NondegMetric I M` is a smooth section `g` of the bundle of bilinear forms on the tangent bundle, symmetric and
nondegenerate at every point: a pseudo-Riemannian metric of any signature. The two cases of the library are
corollaries: a Lorentzian metric (`NondegMetric.ofLorentzian`) and a smooth Riemannian metric of Mathlib
(`NondegMetric.ofRiemannian`). For a manifold modelled on `ℝⁿ`, `NondegMetric.coordMetric` is the matrix of
components in a chart, with the proofs that it is symmetric (`coordMetric_transpose`), invertible
(`coordMetric_isUnit_det`) and smooth (`coordMetric_smooth`) on the chart target, as for Lorentzian metrics
(`LorentzianMetric.coordMetric` is the same expression: `ofLorentzian_coordMetric`). The volume measure of a
general metric is in `VolumeMeasure.lean`.

The structure has the same smoothness field as `LorentzianMetric` and Mathlib's `ContMDiffRiemannianMetric`.
-/

open Bundle Manifold Matrix
open scoped ContDiff

noncomputable section
namespace Lightlike

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A **smooth symmetric nondegenerate bilinear field** on the tangent bundle: a pseudo-Riemannian metric of any
signature, the common generalisation of `LorentzianMetric` and Mathlib's `ContMDiffRiemannianMetric`. -/
structure NondegMetric where
  /-- The metric tensor at each point. -/
  g (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry. -/
  symm (x : M) (v w : TangentSpace I x) : g x v w = g x w v
  /-- Nondegeneracy. -/
  nondegenerate (x : M) (v : TangentSpace I x) (h : ∀ w, g x v w = 0) : v = 0
  /-- Smoothness of `x ↦ gₓ` as a section of the bundle `T*M ⊗ T*M`. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g x))

variable {I M}

namespace NondegMetric

/-- Agreement with Mathlib: the underlying `LinearMap.BilinForm` is nondegenerate. -/
lemma bilinForm_nondegenerate (g : NondegMetric I M) (x : M) : (g.g x).toBilinForm.Nondegenerate :=
  ⟨fun v hv => g.nondegenerate x v fun w => by simpa using hv w,
    fun w hw => g.nondegenerate x w fun v => by simpa [g.symm x w v] using hw v⟩

/-- A Lorentzian metric is a smooth symmetric nondegenerate bilinear field. -/
def ofLorentzian {n : ℕ} (g : LorentzianMetric I M n) : NondegMetric I M where
  g := g.g
  symm := g.symm
  nondegenerate := g.nondegenerate
  contMDiff := g.contMDiff

/-- A smooth Riemannian metric of Mathlib is a smooth symmetric nondegenerate bilinear field. -/
def ofRiemannian (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M => TangentSpace I x)) :
    NondegMetric I M where
  g := h.inner
  symm := h.symm
  nondegenerate x v hv := by
    by_contra hv0
    have := h.pos x v hv0
    rw [hv v] at this
    exact lt_irrefl _ this
  contMDiff := h.contMDiff

end NondegMetric

end General

section Coordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The components `g_{ij}(y) = g(∂ᵢ, ∂ⱼ)` of a metric in the preferred chart of `M`
at `x₀`, where `∂ᵢ` is the coordinate vector field: the image of the standard basis vector `eᵢ`
under the derivative of the inverse chart. Defined for all `y : ℝⁿ`; meaningful on the chart's
target. -/
def NondegMetric.coordMetric (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    g.g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single j 1))


/-- On the chart target, the coordinate components are `g(∂ᵢ, ∂ⱼ)` in the coordinate basis. -/
lemma NondegMetric.coordMetric_eq (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (i j : Fin n) :
    g.coordMetric x₀ y i j =
      g.g _ (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) i)
        (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) j) := by
  rw [coordBasis_apply, coordBasis_apply]
  simp only [NondegMetric.coordMetric]
  rw [mfderiv_extChartAt_symm_eq x₀ hy]
  rfl

/-- The coordinate matrix is symmetric (everywhere). -/
theorem NondegMetric.coordMetric_transpose (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) (y : Fin n → ℝ) : (g.coordMetric x₀ y)ᵀ = g.coordMetric x₀ y := by
  ext i j
  simp only [Matrix.transpose_apply, NondegMetric.coordMetric]
  exact g.symm _ _ _

/-- The coordinate matrix is invertible on the chart target: it is the Gram matrix of the
nondegenerate form `g_p` in the coordinate basis of `T_p M`. -/
theorem NondegMetric.coordMetric_isUnit_det (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    IsUnit (g.coordMetric x₀ y).det := by
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (coordBasis x₀ hp)).mp
    (g.bilinForm_nondegenerate p)
  have hmat : LinearMap.BilinForm.toMatrix (coordBasis x₀ hp) (g.g p).toBilinForm =
      g.coordMetric x₀ y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, g.coordMetric_eq x₀ hy]
    rfl
  rw [← hmat]
  exact hdet.isUnit

/-- The coordinate components are `C^∞` on the chart target. -/
theorem NondegMetric.coordMetric_smooth (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
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


/-- **The link.** For a smooth symmetric nondegenerate bilinear field `g` on `M` and any `x₀ : M`, the coordinate
components `g.coordMetric x₀` form an `IsCoordMetric` (symmetric, invertible, `C^∞`) on the open chart target, which
contains the chart image of `x₀`. -/
theorem NondegMetric.isCoordMetric_coordMetric (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M) :
    IsCoordMetric (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target where
  isOpen := isOpen_extChartAt_target x₀
  symm y _ := g.coordMetric_transpose x₀ y
  isUnit_det _ hy := g.coordMetric_isUnit_det x₀ hy
  smooth i j := g.coordMetric_smooth x₀ i j

/-- **For a Riemannian metric the coordinate matrix is positive definite** on the chart target. -/
theorem NondegMetric.ofRiemannian_coordMetric_posDef
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ) (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    ((NondegMetric.ofRiemannian h).coordMetric x₀ y).PosDef := by
  set g := NondegMetric.ofRiemannian h with hg
  set p := (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y with hpdef
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  set b := coordBasis x₀ hp with hb
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · have := g.coordMetric_transpose x₀ y
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · have hv : (∑ i, x i • b i) ≠ 0 := fun h0 => hx (funext fun i => by
      simpa using Fintype.linearIndependent_iff.1 b.linearIndependent x h0 i)
    have hpos := h.pos p _ hv
    have e1 : star x ⬝ᵥ ((g.coordMetric x₀ y) *ᵥ x) = h.inner p (∑ i, x i • b i) (∑ j, x j • b j) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, ContinuousLinearMap.sum_apply, map_smul,
        ContinuousLinearMap.smul_apply, smul_eq_mul, g.coordMetric_eq x₀ hy, Finset.mul_sum, star_trivial]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hs := h.symm p (coordBasis x₀ hp j) (coordBasis x₀ hp i)
      rw [hs]
      change x i * (h.inner p (coordBasis x₀ hp i) (coordBasis x₀ hp j) * x j) = _
      ring
    rw [e1]; exact hpos

/-- **For a Riemannian metric the volume density is `√(det g)`** (the determinant is positive). -/
theorem NondegMetric.ofRiemannian_abs_det
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, Fin n → ℝ) ∞ (Fin n → ℝ) (fun x : M => TangentSpace 𝓘(ℝ, Fin n → ℝ) x))
    (x₀ : M) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    |((NondegMetric.ofRiemannian h).coordMetric x₀ y).det| = ((NondegMetric.ofRiemannian h).coordMetric x₀ y).det :=
  abs_of_pos (NondegMetric.ofRiemannian_coordMetric_posDef h x₀ hy).det_pos

/-- For a Lorentzian metric the general coordinate matrix is the Lorentzian one. -/
theorem NondegMetric.ofLorentzian_coordMetric (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (x₀ : M) :
    (NondegMetric.ofLorentzian g).coordMetric x₀ = g.coordMetric x₀ := rfl

end Coordinates

end Lightlike
