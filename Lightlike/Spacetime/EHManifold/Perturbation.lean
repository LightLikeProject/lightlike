import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.Lorentzian

/-!
# Perturbations of a metric as symmetric tensor fields

* `SymBilinField I M`: a smooth symmetric bilinear field on the tangent bundle (a symmetric `(0,2)` tensor
  field). It is a `NondegMetric` without the nondegeneracy.
* `SymBilinField.coordComp h x₀`: its components in the chart at `x₀`; they are smooth on the chart target
  (`SymBilinField.coordComp_smooth`) and symmetric (`SymBilinField.coordComp_symm`).
* `NondegMetric.addSmul g h t`: the metric `g + t h`, given that it is nondegenerate; its components are
  `g + t h` in every chart (`NondegMetric.coordMetric_addSmul`).

Supporting definitions for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff Matrix

noncomputable section

namespace Lightlike

/-- A **smooth symmetric bilinear field** on the tangent bundle: a symmetric `(0,2)` tensor field. -/
structure SymBilinField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The bilinear form at each point. -/
  h (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry. -/
  symm (x : M) (v w : TangentSpace I x) : h x v w = h x w v
  /-- Smoothness of `x ↦ hₓ` as a section of the bundle `T*M ⊗ T*M`. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- The components `h_{ij}(y) = h(∂ᵢ, ∂ⱼ)` of a symmetric bilinear field in the chart of `M` at `x₀`.
Defined for all `y : ℝⁿ`; meaningful on the chart's target. -/
def SymBilinField.coordComp (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    h.h ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single i 1))
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y
        (Pi.single j 1))

/-- The components are symmetric. -/
lemma SymBilinField.coordComp_symm (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    (y : Fin n → ℝ) (i j : Fin n) : h.coordComp x₀ y i j = h.coordComp x₀ y j i :=
  h.symm _ _ _

lemma SymBilinField.coordComp_eq (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (x₀ : M)
    {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) (i j : Fin n) :
    h.coordComp x₀ y i j =
      h.h _ (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) i)
        (coordBasis x₀ (symm_mem_chartTriv_baseSet x₀ hy) j) := by
  rw [coordBasis_apply, coordBasis_apply]
  simp only [SymBilinField.coordComp]
  rw [mfderiv_extChartAt_symm_eq x₀ hy]
  rfl

/-- The components are `C^∞` on the chart target. -/
theorem SymBilinField.coordComp_smooth (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (x₀ : M) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun y => h.coordComp x₀ y i j) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target := by
  set e := chartTriv n x₀
  set b := Pi.basisFun ℝ (Fin n)
  have hF : ContMDiffOn 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞
      (fun p => h.h p (e.localFrame b i p) (e.localFrame b j p)) e.baseSet := by
    have h1 := ContMDiffOn.clm_bundle_apply₂ (F₁ := Fin n → ℝ) (F₂ := Fin n → ℝ)
      (E₃ := Bundle.Trivial M ℝ) (b := id) (s := e.baseSet)
      h.contMDiff.contMDiffOn (e.contMDiffOn_localFrame_baseSet _ b i)
      (e.contMDiffOn_localFrame_baseSet _ b j)
    intro p hp
    have := h1 p hp
    simp only [contMDiffWithinAt_totalSpace] at this
    exact this.2
  have hcomp := hF.comp (contMDiffOn_extChartAt_symm x₀) fun y hy =>
    symm_mem_chartTriv_baseSet x₀ hy
  refine (contMDiffOn_iff_contDiffOn.mp hcomp).congr fun y hy => ?_
  have hp := symm_mem_chartTriv_baseSet x₀ hy
  have hfr : ∀ k, e.localFrame b k ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y) =
      coordBasis x₀ hp k := fun k => by
    rw [Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) (i := k) hp]
    rfl
  simp only [Function.comp, h.coordComp_eq x₀ hy, hfr]

/-- **The metric `g + t h`**, for a symmetric bilinear field `h`, given that it is nondegenerate. -/
def NondegMetric.addSmul (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M)
    (t : ℝ) (hnd : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0) : NondegMetric 𝓘(ℝ, Fin n → ℝ) M where
  g x := g.g x + t • h.h x
  symm x v w := by
    show g.g x v w + t * h.h x v w = g.g x w v + t * h.h x w v
    rw [g.symm x v w, h.symm x v w]
  nondegenerate x v hv := hnd x v hv
  contMDiff := g.contMDiff.add_section (h.contMDiff.const_smul_section (a := t))

/-- The components of `g + t h` in a chart are the components of `g` plus `t` times those of `h`. -/
lemma NondegMetric.coordMetric_addSmul (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)
    (h : SymBilinField 𝓘(ℝ, Fin n → ℝ) M) (t : ℝ)
    (hnd : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      (∀ w, g.g x v w + t * h.h x v w = 0) → v = 0) (x₀ : M) (y : Fin n → ℝ) :
    (g.addSmul h t hnd).coordMetric x₀ y = g.coordMetric x₀ y + t • h.coordComp x₀ y := by
  ext i j
  rfl

end Lightlike
