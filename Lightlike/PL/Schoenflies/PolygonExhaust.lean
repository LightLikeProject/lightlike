import Lightlike.PL.Schoenflies.FillHoles
import Lightlike.PL.Schoenflies.PolygonAround
import Lightlike.PL.Schoenflies.ConnectedHull
import Lightlike.PL.Schoenflies.InsideSubset

/-!
# Exhausting the inner region of a Jordan curve by simple polygons

Row G3-188, milestone PL5 (third pass), item 5b.  For a bounded connected open `U ⊆ ℝ²` whose complement is
the closure of a connected set `V`, every nonempty compact `K ⊆ U` lies in the inside of a simple polygon
whose carrier and inside both lie in `U`.  For a Jordan curve, `U` is its bounded complementary component.

* `exists_polygon_around_in`: the abstract statement.
* `jordan_exists_polygon`: the Jordan curve form.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **A simple polygon around a compact set, inside `U`.**  Let `U` be open, connected and bounded, `V`
connected and disjoint from `U` with `Uᶜ ⊆ closure V`.  Every nonempty compact `K ⊆ U` is contained in
`{parity = 1}` of a simple polygon `p` with `p.carrier ⊆ U`, and `{parity = 1} ⊆ U`. -/
theorem exists_polygon_around_in {U V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) (hV : IsConnected V) (hVU : Disjoint V U) (hcov : Uᶜ ⊆ closure V)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (p : Polygon n), p.IsSimple ∧ p.carrier ⊆ U ∧ (∀ z ∈ K, p.parity z = 1) ∧
      ∀ z, p.parity z = 1 → z ∈ U := by
  obtain ⟨K', hK'c, hK'conn, hKK', hK'U⟩ := exists_compact_connected_superset hUo hUc hK hKU
  obtain ⟨n, p, hsimp, hcar, hpar⟩ := exists_simple_polygon_around hK'c hK'conn.isPreconnected
    (hne.mono hKK') hUo hK'U
  have hVc : V ⊆ Uᶜ := fun z hz hzU => Set.disjoint_left.1 hVU hz hzU
  have heq : Uᶜ = closure V :=
    Set.Subset.antisymm hcov (closure_minimal hVc hUo.isClosed_compl)
  have hpre : IsPreconnected Uᶜ := by rw [heq]; exact hV.isPreconnected.closure
  have hub : ¬ Bornology.IsBounded Uᶜ := by
    intro hb
    have : Bornology.IsBounded (Set.univ : Set (ℝ × ℝ)) := by
      have := hUb.union hb
      rwa [Set.union_compl_self] at this
    exact (NormedSpace.unbounded_univ (𝕜 := ℝ) (E := ℝ × ℝ)) this
  exact ⟨n, p, hsimp, hcar, fun z hz => (hpar z (hKK' hz)).2,
    fun z hz => mem_of_parity_eq_one p hcar hpre hub hz⟩

/-- **Jordan curve form.**  For a Jordan curve `f` with bounded complementary component `U`, every nonempty
compact `K ⊆ U` lies in the inside of a simple polygon whose carrier and inside lie in `U`. -/
theorem jordan_exists_polygon {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range f ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → K.Nonempty → K ⊆ U →
        ∃ (n : ℕ) (p : Polygon n), p.IsSimple ∧ p.carrier ⊆ U ∧ (∀ z ∈ K, p.parity z = 1) ∧
          ∀ z, p.parity z = 1 → z ∈ U := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdis, hun, hUb, hVb, hfU, hfV⟩ := jordan_curve_theorem hc hi
  refine ⟨U, hUo, hUc, hUb, hfU, fun K hK hne hKU => ?_⟩
  refine exists_polygon_around_in hUo hUc hUb hVc hdis.symm ?_ hK hne hKU
  intro z hz
  have hz' : z ∈ V ∪ range f := by
    by_cases hzJ : z ∈ range f
    · exact Or.inr hzJ
    · left
      have : z ∈ U ∪ V := by rw [hun]; exact hzJ
      exact this.resolve_left hz
  rcases hz' with h | h
  · exact subset_closure h
  · rw [← hfV] at h
    exact frontier_subset_closure h

end Lightlike.PL.Schoenflies
