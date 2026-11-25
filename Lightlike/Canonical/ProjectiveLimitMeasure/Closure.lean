import Lightlike.Canonical.ProjectiveLimitMeasure.Extension

/-!
# Extension of the cylinder functional to `C(Lim f, ℝ)` (row G2-009, CA2)

The bounded linear functional on the dense subalgebra of cylinder functions extends uniquely to a
continuous linear functional `cylExt` on `C(Lim f, ℝ)` (`ashtekar-lewandowski-1995`, §3.3).
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  [IsDirected ι (· ≤ ·)] [Nonempty ι] [∀ i, CompactSpace (X i)]
  [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, IsFiniteMeasure (μ i)]

omit [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, Nonempty (X i)] in
/-- The cylinder functions form a dense subset of `C(Lim f, ℝ)`. -/
theorem dense_cylAlgebra [CompactSpace (Lim f)] (hf : IsProjSystem f) :
    Dense ((cylAlgebra f hf : Subalgebra ℝ C(Lim f, ℝ)) : Set C(Lim f, ℝ)) := by
  have h := congrArg (fun s : Subalgebra ℝ C(Lim f, ℝ) => (s : Set C(Lim f, ℝ)))
    (topologicalClosure_cylAlgebra f hf)
  rw [dense_iff_closure_eq]
  simpa using h

/-- The cylinder functional as a continuous linear map on the normed subspace of cylinder
functions. -/
noncomputable def cylCLM [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) :
    (cylAlgebra f hf).toSubmodule →L[ℝ] ℝ :=
  LinearMap.mkContinuous (cylFunctional hf hs hμ)
    ((μ (Classical.arbitrary ι)).real Set.univ) (abs_cylFunctional_le hf hs hμ)

/-- **The extension** `Λ̄ : C(Lim f, ℝ) →L[ℝ] ℝ` of the cylinder functional. -/
noncomputable def cylExt [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) :
    C(Lim f, ℝ) →L[ℝ] ℝ :=
  (cylCLM hf hs hμ).extend (cylAlgebra f hf).toSubmodule.subtypeL

/-- The extension agrees with `g ∘ proj i ↦ ∫ g dμ i` on cylinder functions. -/
theorem cylExt_cyl [CompactSpace (Lim f)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ)
    (i : ι) (g : C(X i, ℝ)) : cylExt hf hs hμ (cyl f i g) = ∫ y, g y ∂μ i := by
  have hd : DenseRange (cylAlgebra f hf).toSubmodule.subtypeL :=
    (dense_cylAlgebra hf).denseRange_val
  have hu : IsUniformInducing (cylAlgebra f hf).toSubmodule.subtypeL :=
    isUniformInducing_val _
  have := ContinuousLinearMap.extend_eq (cylCLM hf hs hμ) hd hu
    ⟨cyl f i g, mem_cylAlgebra f hf i g⟩
  exact this.trans (cylFunctional_cyl hf hs hμ i g)

end Lightlike.Rows.G2_009
