import Lightlike.Canonical.ProjectiveLimitMeasure.Surjective
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The functional on cylinder functions (row G2-009, CA2)

For a cylindrically consistent family `μ` of finite Borel measures on a directed system of nonempty
compact Hausdorff spaces with surjective bonding maps, the assignment `g ∘ proj i ↦ ∫ g dμ i` is
well defined on cylinder functions (`integral_eq_of_cyl_eq`).  It is the first half of the
Ashtekar–Lewandowski construction (`ashtekar-lewandowski-1995`, §3.3): the second half extends it
to `C(Lim f, ℝ)` and applies the Riesz–Markov theorem.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i} {μ : ∀ i, Measure (X i)}

/-- Under a consistent family, integrating a pulled-back function over `μ j` gives the integral over
`μ i`. -/
lemma integral_comp_bonding (hf : IsProjSystem f) (hμ : Consistent f μ) {i j : ι} (h : i ≤ j)
    (g : C(X i, ℝ)) : ∫ x, g (f h x) ∂μ j = ∫ y, g y ∂μ i := by
  rw [← hμ i j h, integral_map (hf.cont i j h).measurable.aemeasurable
    g.continuous.aestronglyMeasurable]

/-- **Well-definedness.** Two representations of the same cylinder function have the same
integral. -/
theorem integral_eq_of_cyl_eq [IsDirected ι (· ≤ ·)] [Nonempty ι] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (hμ : Consistent f μ) {i j : ι}
    {g : C(X i, ℝ)} {g' : C(X j, ℝ)} (h : cyl f i g = cyl f j g') :
    ∫ y, g y ∂μ i = ∫ y, g' y ∂μ j := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have h1 := cyl_eq_cyl_comp f hf hik g
  have h2 := cyl_eq_cyl_comp f hf hjk g'
  have hk : g.comp ⟨f hik, hf.cont i k hik⟩ = g'.comp ⟨f hjk, hf.cont j k hjk⟩ := by
    ext z
    obtain ⟨x, rfl⟩ := surjective_proj f hf hs k z
    have := congrArg (fun φ : C(Lim f, ℝ) => φ x) (h1.symm.trans (h.trans h2))
    simpa [cyl_apply] using this
  rw [← integral_comp_bonding hf hμ hik g, ← integral_comp_bonding hf hμ hjk g']
  exact congrArg (fun φ : C(X k, ℝ) => ∫ x, φ x ∂μ k) hk

end Lightlike.Rows.G2_009
