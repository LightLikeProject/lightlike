import Lightlike.Canonical.ProjectiveLimitMeasure.System
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma

/-!
# Compactness of the projective limit and density of cylinder functions (row G2-009, CA2)

For a directed projective system of compact Hausdorff spaces, the limit `Lim f` is compact
Hausdorff, and the *cylinder functions* `g ∘ proj i` (`g` continuous on `X i`) form a subalgebra of
`C(Lim f, ℝ)` that separates points; by Stone–Weierstrass it is dense
(`ashtekar-lewandowski-1995`, §3.3: cylindrical functions are dense in the continuous functions).
-/

open MeasureTheory

namespace Lightlike.Canonical.ProjectiveLimitMeasure

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i)

/-- The projection `Lim f → X i` as a continuous map. -/
def projC (i : ι) : C(Lim f, X i) := ⟨proj f i, continuous_proj f i⟩

@[simp] lemma projC_apply (i : ι) (x : Lim f) : projC f i x = proj f i x := rfl

section Compact

variable [∀ i, T2Space (X i)]

/-- The set of compatible families is closed in the product. -/
lemma isClosed_lim (hf : IsProjSystem f) :
    IsClosed {x : ∀ i, X i | ∀ i j (h : i ≤ j), f h (x j) = x i} := by
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h => ?_
  exact isClosed_eq ((hf.cont i j h).comp (continuous_apply j)) (continuous_apply i)

/-- The projective limit of compact Hausdorff spaces is compact. -/
theorem compactSpace_lim [∀ i, CompactSpace (X i)] (hf : IsProjSystem f) :
    CompactSpace (Lim f) :=
  isCompact_iff_compactSpace.1 (isClosed_lim f hf).isCompact

instance : T2Space (Lim f) := instT2SpaceSubtype

end Compact

/-- A cylinder function: `g ∘ proj i`. -/
def cyl (i : ι) (g : C(X i, ℝ)) : C(Lim f, ℝ) := g.comp (projC f i)

lemma cyl_apply (i : ι) (g : C(X i, ℝ)) (x : Lim f) : cyl f i g x = g (proj f i x) := rfl

/-- Cylinder functions can be pushed up along the bonding maps. -/
lemma cyl_eq_cyl_comp (hf : IsProjSystem f) {i j : ι} (h : i ≤ j) (g : C(X i, ℝ)) :
    cyl f i g = cyl f j (g.comp ⟨f h, hf.cont i j h⟩) := by
  ext x
  simp [cyl_apply, proj_comp f h x]

variable [IsDirected ι (· ≤ ·)] [Nonempty ι]

/-- The subalgebra of cylinder functions in `C(Lim f, ℝ)`. -/
def cylAlgebra (hf : IsProjSystem f) : Subalgebra ℝ C(Lim f, ℝ) where
  carrier := {φ | ∃ i, ∃ g : C(X i, ℝ), φ = cyl f i g}
  mul_mem' := by
    rintro _ _ ⟨i, g, rfl⟩ ⟨j, g', rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, (g.comp ⟨f hik, hf.cont i k hik⟩) * (g'.comp ⟨f hjk, hf.cont j k hjk⟩), ?_⟩
    rw [cyl_eq_cyl_comp f hf hik g, cyl_eq_cyl_comp f hf hjk g']
    ext x
    simp [cyl_apply]
  add_mem' := by
    rintro _ _ ⟨i, g, rfl⟩ ⟨j, g', rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    refine ⟨k, (g.comp ⟨f hik, hf.cont i k hik⟩) + (g'.comp ⟨f hjk, hf.cont j k hjk⟩), ?_⟩
    rw [cyl_eq_cyl_comp f hf hik g, cyl_eq_cyl_comp f hf hjk g']
    ext x
    simp [cyl_apply]
  algebraMap_mem' := by
    intro r
    refine ⟨Classical.arbitrary ι, ContinuousMap.const _ r, ?_⟩
    ext x
    simp [cyl_apply]

lemma mem_cylAlgebra (hf : IsProjSystem f) (i : ι) (g : C(X i, ℝ)) :
    cyl f i g ∈ cylAlgebra f hf := ⟨i, g, rfl⟩

/-- Cylinder functions separate the points of the limit of compact Hausdorff spaces. -/
theorem separatesPoints_cylAlgebra [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    (hf : IsProjSystem f) : (cylAlgebra f hf).SeparatesPoints := by
  intro x y hxy
  have : ∃ i, x.1 i ≠ y.1 i := by
    by_contra hc
    exact hxy (Subtype.ext (funext fun i => not_not.1 fun h => hc ⟨i, h⟩))
  obtain ⟨i, hi⟩ := this
  obtain ⟨g, hg0, hg1, -⟩ := exists_continuous_zero_one_of_isClosed
    (isClosed_singleton (x := x.1 i)) (isClosed_singleton (x := y.1 i))
    (Set.disjoint_singleton.2 hi)
  refine ⟨cyl f i g, ⟨cyl f i g, mem_cylAlgebra f hf i g, rfl⟩, ?_⟩
  have h0 : g (x.1 i) = 0 := hg0 rfl
  have h1 : g (y.1 i) = 1 := hg1 rfl
  simp only [cyl_apply, proj]
  rw [h0, h1]
  exact zero_ne_one

/-- **Density of cylinder functions** (Stone–Weierstrass): the cylinder functions are dense in
`C(Lim f, ℝ)`. -/
theorem topologicalClosure_cylAlgebra [∀ i, CompactSpace (X i)] [∀ i, T2Space (X i)]
    [CompactSpace (Lim f)] (hf : IsProjSystem f) :
    (cylAlgebra f hf).topologicalClosure = ⊤ :=
   ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (separatesPoints_cylAlgebra f hf)

end Lightlike.Canonical.ProjectiveLimitMeasure

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.compactSpace_lim := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.compactSpace_lim
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cyl := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cyl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cylAlgebra := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cylAlgebra
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cyl_apply := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cyl_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.cyl_eq_cyl_comp := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.cyl_eq_cyl_comp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.isClosed_lim := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.isClosed_lim
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.mem_cylAlgebra := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.mem_cylAlgebra
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.projC := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.projC
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.projC_apply := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.projC_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.separatesPoints_cylAlgebra := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.separatesPoints_cylAlgebra
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_009.topologicalClosure_cylAlgebra := _root_.Lightlike.Canonical.ProjectiveLimitMeasure.topologicalClosure_cylAlgebra
