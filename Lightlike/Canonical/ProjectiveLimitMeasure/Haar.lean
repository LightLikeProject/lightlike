import Lightlike.Canonical.ProjectiveLimitMeasure.Existence
import Lightlike.Canonical.ProjectiveLimitMeasure.Example
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The Haar family is cylindrically consistent (row G2-009, CA2)

For a probability measure `ν` on a group `G` (the Haar measure of a compact group), the product
measures `μ n = ν^{⊗ (n+1)}` on `G^{n+1}` are consistent for the edge-forgetting bonding maps of
`Example.lean`.  Together with `exists_isLimit` this gives the Ashtekar–Lewandowski measure as a
projective limit of Haar measures (`ashtekar-lewandowski-1995`, §3.3).
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

variable {G : Type} [MeasurableSpace G]

/-- Restricting a product of probability measures along an injection of index types gives the
product of probability measures. -/
theorem pi_map_comp_injective {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] (e : κ → ι)
    (he : Function.Injective e) (ν : Measure G) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : ι => ν).map (fun (x : ι → G) (k : κ) => x (e k)) =
      Measure.pi fun _ : κ => ν := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hmeas : Measurable (fun (x : ι → G) (k : κ) => x (e k)) :=
    Measurable.of_eval fun k => measurable_pi_apply (e k)
  have hs' : ∀ i, MeasurableSet (Function.extend e s (fun _ => (Set.univ : Set G)) i) := by
    intro i
    by_cases h : ∃ k, e k = i
    · obtain ⟨k, rfl⟩ := h
      rw [he.extend_apply]
      exact hs k
    · rw [Function.extend_apply' _ _ _ h]
      exact MeasurableSet.univ
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι → G) (k : κ) => x (e k)) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (Function.extend e s (fun _ => (Set.univ : Set G))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : ∃ k, e k = i
      · obtain ⟨k, rfl⟩ := hi
        rw [he.extend_apply]
        exact h k
      · rw [Function.extend_apply' _ _ _ hi]
        exact Set.mem_univ _
    · intro h k
      have := h (e k)
      rwa [he.extend_apply] at this
  rw [hpre, Measure.pi_pi]
  symm
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image e)), Finset.prod_image
    (fun a _ b _ hab => he hab)]
  · refine Finset.prod_congr rfl fun k _ => ?_
    rw [he.extend_apply]
  · intro i _ hi
    have : ¬ ∃ k, e k = i := by
      rintro ⟨k, rfl⟩
      exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [Function.extend_apply' _ _ _ this, measure_univ]

/-- The product of copies of a probability measure is consistent for the edge-forgetting bonding
maps. -/
theorem consistent_pi (ν : Measure G) [IsProbabilityMeasure ν] :
    Consistent (X := fun n : ℕ => Fin (n + 1) → G) (forget G)
      (fun n => Measure.pi fun _ : Fin (n + 1) => ν) := by
  intro n m h
  exact pi_map_comp_injective (fun k : Fin (n + 1) => Fin.castLE (Nat.succ_le_succ h) k)
    (Fin.castLE_injective _) ν

omit [MeasurableSpace G] in
/-- The edge-forgetting maps are surjective on a group. -/
lemma surjective_forget [TopologicalSpace G] [One G] ⦃n m : ℕ⦄ (h : n ≤ m) :
    Function.Surjective (forget G h) := by
  intro y
  refine ⟨fun k => if hk : (k : ℕ) < n + 1 then y ⟨k, hk⟩ else 1, ?_⟩
  funext k
  simp only [forget, Fin.val_castLE, k.isLt, dite_true]

/-- **The Ashtekar–Lewandowski measure as a projective limit of Haar measures** (here for the
chain of graphs with `n+1` edges): for a probability measure `ν` on a compact metrizable group
`G` (in particular its Haar measure), the product measures `ν^{⊗ (n+1)}` on `G^{n+1}` have a
projective limit on the limit space. -/
theorem exists_isLimit_pi [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [SecondCountableTopology G] [BorelSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] :
    ∃ μ : Measure (Lim (X := fun n : ℕ => Fin (n + 1) → G) (forget G)),
      IsLimit (forget G) μ (fun n => Measure.pi fun _ : Fin (n + 1) => ν) := by
  have : T3Space G := inferInstance
  have : TopologicalSpace.MetrizableSpace G := inferInstance
  have : ∀ n : ℕ, TopologicalSpace.PseudoMetrizableSpace (Fin (n + 1) → G) := fun n => inferInstance
  have : ∀ n : ℕ, HasOuterApproxClosed (Fin (n + 1) → G) := fun n => inferInstance
  exact exists_isLimit (isProjSystem_forget G) (fun _ _ h => surjective_forget h) (consistent_pi ν)

/-- The normalised Haar measure of a compact group is a probability measure. -/
lemma isProbabilityMeasure_haar [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [BorelSpace G] [Nonempty G] :
    IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) := by
  refine ⟨?_⟩
  have h := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts G))
  simpa using h

/-- **The AL measure as a projective limit of Haar measures**: for a compact metrizable group
`G`, the products of normalised Haar measures on `G^{n+1}` have a projective limit. -/
theorem exists_isLimit_haar [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [SecondCountableTopology G] [BorelSpace G] :
    ∃ μ : Measure (Lim (X := fun n : ℕ => Fin (n + 1) → G) (forget G)),
      IsLimit (forget G) μ (fun n => Measure.pi fun _ : Fin (n + 1) =>
        Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) :=
  have : IsProbabilityMeasure (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)) :=
    isProbabilityMeasure_haar
  exists_isLimit_pi _

end Lightlike.Rows.G2_009
