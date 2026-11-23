import Mathlib

/-!
# A compact subset of a connected open set lies in a compact connected subset

Row G3-188, milestone PL5 (third pass), item 5b, route A.  If `U ⊆ ℝ²` is open and connected and `K ⊆ U` is
compact, there is a compact connected `K'` with `K ⊆ K' ⊆ U`: finitely many closed balls around points of
`K`, joined to a base point by paths in `U` (`U` is path connected, being open and connected).

* `exists_local_compact_connected`: around each `y ∈ U` a compact connected neighbourhood of `y` in `U`
  that contains a given base point.
* `exists_compact_connected_superset`: the statement.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric Filter Topology

/-- Around every point `y` of a connected open `U` there is a compact preconnected neighbourhood of `y`
inside `U` that contains the base point `x0 ∈ U`. -/
lemma exists_local_compact_connected {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hUc : IsConnected U)
    {x0 : ℝ × ℝ} (hx0 : x0 ∈ U) {y : ℝ × ℝ} (hy : y ∈ U) :
    ∃ A : Set (ℝ × ℝ), IsCompact A ∧ IsPreconnected A ∧ x0 ∈ A ∧ A ⊆ U ∧ A ∈ 𝓝 y := by
  have hpc : IsPathConnected U := (hU.isConnected_iff_isPathConnected).1 hUc
  have hj : JoinedIn U x0 y := hpc.joinedIn x0 hx0 y hy
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hy
  set γ := hj.somePath with hγ
  have hγU : ∀ t, γ t ∈ U := hj.somePath_mem
  have hball : closedBall y (r / 2) ⊆ U := fun z hz =>
    hrU (by rw [mem_ball]; exact lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
  refine ⟨closedBall y (r / 2) ∪ range γ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall y (r / 2)).union (isCompact_range γ.continuous)
  · refine IsPreconnected.union' ⟨y, mem_closedBall_self (by linarith), ?_⟩
      (convex_closedBall y (r / 2)).isPreconnected (isConnected_range γ.continuous).isPreconnected
    exact ⟨1, γ.target⟩
  · exact Or.inr ⟨0, γ.source⟩
  · rintro z (hz | ⟨t, rfl⟩)
    · exact hball hz
    · exact hγU t
  · exact mem_of_superset (closedBall_mem_nhds y (by linarith)) subset_union_left

/-- **A compact subset of a connected open set lies in a compact connected subset.** -/
theorem exists_compact_connected_superset {U K : Set (ℝ × ℝ)} (hU : IsOpen U) (hUc : IsConnected U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ IsConnected K' ∧ K ⊆ K' ∧ K' ⊆ U := by
  obtain ⟨x0, hx0⟩ := hUc.nonempty
  have h1 : ∀ y : ℝ × ℝ, y ∈ U → ∃ A : Set (ℝ × ℝ), IsCompact A ∧ IsPreconnected A ∧ x0 ∈ A ∧
      A ⊆ U ∧ A ∈ 𝓝 y := fun y hy => exists_local_compact_connected hU hUc hx0 hy
  choose! A hAc hAp hAx hAU hAn using h1
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover A (fun y hy => hAn y (hKU hy))
  refine ⟨{x0} ∪ ⋃ y ∈ t, A y, ?_, ⟨⟨x0, Or.inl rfl⟩, ?_⟩, ?_, ?_⟩
  · exact isCompact_singleton.union (t.isCompact_biUnion fun y hy => hAc y (hKU (htK y hy)))
  · refine isPreconnected_of_forall x0 fun z hz => ?_
    rcases hz with rfl | hz
    · exact ⟨{z}, by simp, rfl, rfl, isPreconnected_singleton⟩
    · obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hz
      obtain ⟨hyt, hzy⟩ := Set.mem_iUnion.1 hy
      exact ⟨A y, fun w hw => Or.inr (Set.mem_iUnion₂.2 ⟨y, hyt, hw⟩), hAx y (hKU (htK y hyt)), hzy,
        hAp y (hKU (htK y hyt))⟩
  · exact hKt.trans (subset_union_right)
  · rintro z (rfl | hz)
    · exact hx0
    · obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hz
      obtain ⟨hyt, hzy⟩ := Set.mem_iUnion.1 hy
      exact hAU y (hKU (htK y hyt)) hzy

end Lightlike.PL.Schoenflies
