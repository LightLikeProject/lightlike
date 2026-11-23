import Lightlike.PL.Schoenflies.RegionCompact

/-!
# A nested exhaustion of the inner Jordan region by simple polygons

Row G3-188, milestone PL5 (third pass), item 5c.  For a bounded connected open `U ⊆ ℝ²` whose complement is
the closure of a connected set `V` (the inner region of a Jordan curve), there is a sequence of simple
polygons `p k` with `region (p k) ⊆ U`, `region (p k) ⊆ inside (p (k+1))`, and every compact `K ⊆ U` lies in
the inside of some `p k`.

* `exists_polygon_inside`: one polygon, with the compact set in the inside (not only parity `1`).
* `exists_polygon_exhaustion`: the nested sequence.
* `jordan_exists_polygon_exhaustion`: the Jordan curve form.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **A simple polygon whose inside contains a compact set, with closed region inside `U`.** -/
theorem exists_polygon_inside {U V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) (hV : IsConnected V) (hVU : Disjoint V U) (hcov : Uᶜ ⊆ closure V)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hne : K.Nonempty) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (_ : NeZero n) (p : Polygon n), p.IsSimple ∧ region p ⊆ U ∧ K ⊆ p.inside := by
  obtain ⟨K', hK'c, hK'conn, hKK', hK'U⟩ := exists_compact_connected_superset hUo hUc hK hKU
  obtain ⟨n, p, hsimp, hcar, hpar⟩ := exists_simple_polygon_around hK'c hK'conn.isPreconnected
    (hne.mono hKK') hUo hK'U
  obtain ⟨z0, hz0⟩ := hne
  have hn : n ≠ 0 := by
    rintro rfl
    have := (hpar z0 (hKK' hz0)).2
    simp [Polygon.parity] at this
  have : NeZero n := ⟨hn⟩
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
  refine ⟨n, ⟨hn⟩, p, hsimp, ?_, fun z hz => ?_⟩
  · rintro z (hz | hz)
    · exact mem_of_parity_eq_one p hcar hpre hub hz.2
    · exact hcar hz
  · exact ⟨(hpar z (hKK' hz)).1, (hpar z (hKK' hz)).2⟩

/-- **A nested exhaustion of `U` by simple polygons.** -/
theorem exists_polygon_exhaustion {U V : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) (hV : IsConnected V) (hVU : Disjoint V U) (hcov : Uᶜ ⊆ closure V) :
    ∃ (N : ℕ → ℕ) (p : ∀ k, Polygon (N k)), (∀ k, NeZero (N k)) ∧ (∀ k, (p k).IsSimple) ∧
      (∀ k, region (p k) ⊆ U) ∧ (∀ k, region (p k) ⊆ (p (k + 1)).inside) ∧
      ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ k, K ⊆ (p k).inside := by
  obtain ⟨z0, hz0⟩ := hUc.nonempty
  have hUcne : (Uᶜ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : U = Set.univ := by rwa [Set.compl_empty_iff] at hemp
    exact (NormedSpace.unbounded_univ (𝕜 := ℝ) (E := ℝ × ℝ)) (this ▸ hUb)
  -- exhausting compact sets
  let Kk : ℕ → Set (ℝ × ℝ) := fun k =>
    ({z | 1 / ((k : ℝ) + 1) ≤ Metric.infDist z Uᶜ} ∩ Metric.closedBall 0 ((k : ℝ) + 1)) ∪ {z0}
  have hKkc : ∀ k, IsCompact (Kk k) := fun k => by
    refine IsCompact.union ?_ isCompact_singleton
    refine (isCompact_closedBall (0 : ℝ × ℝ) ((k : ℝ) + 1)).inter_left ?_
    exact isClosed_le continuous_const (Metric.continuous_infDist_pt _)
  have hKkU : ∀ k, Kk k ⊆ U := fun k => by
    rintro z (⟨hz, -⟩ | hz)
    · by_contra hzU
      have h0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem hzU
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hz' : 1 / ((k : ℝ) + 1) ≤ Metric.infDist z Uᶜ := hz
      linarith
    · rw [mem_singleton_iff.1 hz]; exact hz0
  have hKkne : ∀ k, (Kk k).Nonempty := fun k => ⟨z0, Or.inr rfl⟩
  have hcover : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ k, K ⊆ Kk k := by
    intro K hK hKU
    obtain ⟨δ, hδ, hth⟩ := hK.exists_cthickening_subset_open hUo hKU
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨R, hR⟩ := (hK.isBounded.subset_closedBall (0 : ℝ × ℝ))
    obtain ⟨m', hm'⟩ := exists_nat_ge R
    refine ⟨max m m', fun z hz => Or.inl ⟨?_, ?_⟩⟩
    · show 1 / (((max m m' : ℕ) : ℝ) + 1) ≤ Metric.infDist z Uᶜ
      refine le_trans ?_ ((Metric.le_infDist hUcne).2 (fun w hw => ?_) : δ ≤ _)
      · have : 1 / (((max m m' : ℕ) : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left m m') 1)
        linarith
      · by_contra hlt
        rw [not_le] at hlt
        exact hw (hth (Metric.mem_cthickening_of_dist_le w z δ K hz (by rw [dist_comm]; exact hlt.le)))
    · have := hR hz
      refine Metric.closedBall_subset_closedBall ?_ this
      have : (m' : ℝ) ≤ ((max m m' : ℕ) : ℝ) := by exact_mod_cast le_max_right m m'
      linarith
  -- the recursion
  let Good : (Σ n, Polygon n) → Prop := fun q => NeZero q.1 ∧ q.2.IsSimple ∧ region q.2 ⊆ U
  have step : ∀ (k : ℕ) (q : {q : Σ n, Polygon n // Good q}), ∃ q' : {q : Σ n, Polygon n // Good q},
      Kk k ⊆ q'.1.2.inside ∧ region q.1.2 ⊆ q'.1.2.inside := by
    intro k q
    obtain ⟨⟨n, p⟩, hnz, hsimp, hregU⟩ := q
    have := hnz
    obtain ⟨n', hn', p', hs', hrU', hKp'⟩ := exists_polygon_inside hUo hUc hUb hV hVU hcov
      ((hKkc k).union (isCompact_region hsimp)) ((hKkne k).mono subset_union_left)
      (union_subset (hKkU k) hregU)
    exact ⟨⟨⟨n', p'⟩, hn', hs', hrU'⟩, fun z hz => hKp' (Or.inl hz), fun z hz => hKp' (Or.inr hz)⟩
  obtain ⟨n0, hn0, p0, hs0, hrU0, hKp0⟩ := exists_polygon_inside hUo hUc hUb hV hVU hcov
    (hKkc 0) (hKkne 0) (hKkU 0)
  choose f hf using step
  let seq : ℕ → {q : Σ n, Polygon n // Good q} := fun k =>
    Nat.rec ⟨⟨n0, p0⟩, hn0, hs0, hrU0⟩ (fun k q => f k q) k
  have hseq : ∀ k, seq (k + 1) = f k (seq k) := fun k => rfl
  refine ⟨fun k => (seq k).1.1, fun k => (seq k).1.2, fun k => (seq k).2.1, fun k => (seq k).2.2.1,
    fun k => (seq k).2.2.2, fun k => ?_, fun K hK hKU => ?_⟩
  · have h := (hf k (seq k)).2
    rw [← hseq k] at h
    exact h
  · obtain ⟨k, hk⟩ := hcover K hK hKU
    refine ⟨k + 1, hk.trans ?_⟩
    have h := (hf k (seq k)).1
    rw [← hseq k] at h
    exact h

/-- **Jordan curve form.**  For a Jordan curve `f`, its bounded complementary component `U` is the union of
the insides of a nested sequence of simple polygons with `region (p k) ⊆ inside (p (k+1))`. -/
theorem jordan_exists_polygon_exhaustion {f : Circle → ℝ × ℝ} (hc : Continuous f)
    (hi : Function.Injective f) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range f ∧
      ∃ (N : ℕ → ℕ) (p : ∀ k, Polygon (N k)), (∀ k, NeZero (N k)) ∧ (∀ k, (p k).IsSimple) ∧
        (∀ k, region (p k) ⊆ U) ∧ (∀ k, region (p k) ⊆ (p (k + 1)).inside) ∧
        ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ U → ∃ k, K ⊆ (p k).inside := by
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hdis, hun, hUb, hVb, hfU, hfV⟩ := jordan_curve_theorem hc hi
  refine ⟨U, hUo, hUc, hUb, hfU, ?_⟩
  refine exists_polygon_exhaustion hUo hUc hUb hVc hdis.symm ?_
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
