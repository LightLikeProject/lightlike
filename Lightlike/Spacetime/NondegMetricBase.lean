module

public import Lightlike.Spacetime.Lorentzian

/-!
# Smooth symmetric nondegenerate bilinear fields on a manifold (general metrics)

`NondegMetric I M` is a smooth section `g` of the bundle of bilinear forms on the tangent bundle, symmetric and
nondegenerate at every point: a pseudo-Riemannian metric of any signature, with the same smoothness field as
`LorentzianMetric` and Mathlib's `ContMDiffRiemannianMetric`. A Lorentzian metric (`NondegMetric.ofLorentzian`, also a
coercion) and a smooth Riemannian metric of Mathlib (`NondegMetric.ofRiemannian`) are the two cases of the library.
The coordinate components and the volume measure are in `NondegMetric.lean` and `VolumeMeasure.lean`; the connection,
curvature and the Einstein equations are defined for `NondegMetric` in `Connection.lean`.
-/

@[expose] public section

open Bundle Manifold Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace NondegMetric

/-- Agreement with Mathlib: the underlying `LinearMap.BilinForm` is nondegenerate. -/
lemma bilinForm_nondegenerate (g : NondegMetric I M) (x : M) : (g.g x).toBilinForm.Nondegenerate :=
  ⟨fun v hv => g.nondegenerate x v fun w => by simpa using hv w,
    fun w hw => g.nondegenerate x w fun v => by simpa [g.symm x w v] using hw v⟩

/-- A Lorentzian metric is a smooth symmetric nondegenerate bilinear field (its underlying one). -/
abbrev ofLorentzian {n : ℕ} (g : LorentzianMetric I M n) : NondegMetric I M := g.toNondegMetric

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

namespace NondegMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ}

/-- A Lorentzian metric is a smooth symmetric nondegenerate bilinear field, by `ofLorentzian`. -/
instance : CoeOut (LorentzianMetric I M n) (NondegMetric I M) := ⟨LorentzianMetric.toNondegMetric⟩

end NondegMetric

end Lightlike
