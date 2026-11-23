import Lightlike.Rows.G2_009.Cylinder

/-!
# Surjectivity of the projections of a compact projective limit (row G2-009, CA2)

For a directed projective system of nonempty compact Hausdorff spaces with surjective bonding maps,
every projection `proj f i : Lim f → X i` is surjective.  This is what makes the functional
`g ∘ proj i ↦ ∫ g dμ i` well defined in the construction of the projective limit measure.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

universe u v

variable {ι : Type u} [Preorder ι] {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i)

/-- **Surjectivity of the projections.** In a directed system of nonempty compact Hausdorff
spaces with surjective bonding maps, each `proj f i` is onto (finite intersection property in the
product). -/
theorem surjective_proj [IsDirected ι (· ≤ ·)] [Nonempty ι] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] (hf : IsProjSystem f)
    (hs : ∀ i j (h : i ≤ j), Function.Surjective (f h)) (i : ι) :
    Function.Surjective (proj f i) := by
  intro x
  have hcl : IsClosed {y : ∀ k, X k | y i = x} := isClosed_eq (continuous_apply i) continuous_const
  let t : ι × ι → Set (∀ k, X k) := fun p => ⋂ h : p.1 ≤ p.2, {y | f h (y p.2) = y p.1}
  have htc : ∀ p, IsClosed (t p) := fun p =>
    isClosed_iInter fun h =>
      isClosed_eq ((hf.cont _ _ h).comp (continuous_apply p.2)) (continuous_apply p.1)
  have key := hcl.isCompact.inter_iInter_nonempty t htc ?_
  · obtain ⟨y, hy1, hy2⟩ := key
    have hy : ∀ k l (h : k ≤ l), f h (y l) = y k := fun k l h => by
      have := Set.mem_iInter.1 hy2 (k, l)
      exact Set.mem_iInter.1 this h
    exact ⟨⟨y, hy⟩, hy1⟩
  · intro u
    classical
    obtain ⟨M, hM⟩ := Finset.exists_le (insert i (u.image Prod.fst ∪ u.image Prod.snd))
    have hiM : i ≤ M := hM i (Finset.mem_insert_self _ _)
    have h1 : ∀ p ∈ u, p.1 ≤ M := fun p hp =>
      hM _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)))
    have h2 : ∀ p ∈ u, p.2 ≤ M := fun p hp =>
      hM _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)))
    obtain ⟨z, hz⟩ := hs i M hiM x
    refine ⟨fun k => if h : k ≤ M then f h z else Classical.arbitrary (X k), ?_, ?_⟩
    · show (if h : i ≤ M then f h z else Classical.arbitrary (X i)) = x
      simp [hiM, hz]
    · refine Set.mem_iInter₂.2 fun p hp => Set.mem_iInter.2 fun h => ?_
      show f h (if h' : p.2 ≤ M then f h' z else Classical.arbitrary (X p.2)) =
        (if h' : p.1 ≤ M then f h' z else Classical.arbitrary (X p.1))
      simp [h1 p hp, h2 p hp, hf.comp]

end Lightlike.Rows.G2_009
