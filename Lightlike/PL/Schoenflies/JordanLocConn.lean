import Mathlib
import Lightlike.PL.Schoenflies.UniformLocalConn
import Lightlike.PL.Schoenflies.JordanClosure

/-!
# The closed inner region of a Jordan curve is uniformly locally connected

Row G3-188, milestone PL5 (third pass), item 5a.  For a Jordan curve `J` with inner component `U` the set
`closure U = U ∪ J` is uniformly locally connected.  The proof is elementary and needs nothing beyond the
Jordan curve theorem in the form `jordan_inner_closure`:

* `unifLocConn_range_circle`: the image of a continuous injective map from the circle is uniformly locally
  connected (it is homeomorphic to the circle, which is locally connected).
* `unifLocConn_closure`: if `U` is an open set, `closure U = U ∪ J` with `J` compact and uniformly locally connected,
  then `closure U` is uniformly locally connected.  A point `y ∈ U` near `x ∈ J` is joined to `x` by the open ball
  `ball y (dist y J)`, which lies in `U`, followed by the nearest point of `J` and a small connected piece of `J`.
* `jordan_closure_unifLocConn`: the combination for a Jordan curve.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric Filter Topology
open scoped Manifold ContDiff

/-- The image of a continuous injective map of the circle into a metric space is uniformly locally connected. -/
theorem unifLocConn_range_circle {X : Type*} [MetricSpace X] {f : Circle → X} (hc : Continuous f)
    (hi : Function.Injective f) : UnifLocConn (range f) := by
  have : LocallyConnectedSpace Circle :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
  refine unifLocConn_of_isCompact (isCompact_range hc) ?_
  rintro _ ⟨t, rfl⟩ ε hε
  have hW : f ⁻¹' ball (f t) ε ∈ 𝓝 t := hc.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε)
  obtain ⟨V, ⟨hVo, htV, hVc⟩, hVW⟩ := (LocallyConnectedSpace.open_connected_basis t).mem_iff.1 hW
  refine ⟨f '' V, image_subset_range _ _, ?_, hVc.image f hc.continuousOn, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hVW hs
  · obtain ⟨O, hO, hOV⟩ := (hc.isClosedEmbedding hi).isInducing.isOpen_iff.1 hVo
    refine mem_nhdsWithin.2 ⟨O, hO, ?_, ?_⟩
    · have : t ∈ f ⁻¹' O := hOV ▸ htV
      exact this
    · rintro _ ⟨hzO, s, rfl⟩
      have : s ∈ f ⁻¹' O := hzO
      exact ⟨s, hOV ▸ this, rfl⟩

/-- If `U` is open with `closure U = U ∪ J`, `U` disjoint from the compact set `J` which is uniformly
locally connected, then `closure U` is uniformly locally connected. -/
theorem unifLocConn_closure {U J : Set (ℝ × ℝ)} (hUo : IsOpen U) (hJc : IsCompact J) (hJn : J.Nonempty)
    (hcl : closure U = U ∪ J) (hUJ : Disjoint U J) (hcomp : IsCompact (closure U))
    (hJl : UnifLocConn J) : UnifLocConn (closure U) := by
  refine unifLocConn_of_isCompact hcomp ?_
  intro x hx ε hε
  have hV : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hdisj : Disjoint U (closure U)ᶜ := disjoint_compl_right_iff_subset.2 subset_closure
  -- the open ball around a point of `U`, of radius its distance to `J`, lies in `U`
  have hpos : ∀ y ∈ U, 0 < Metric.infDist y J := fun y hy =>
    (hJc.isClosed.notMem_iff_infDist_pos hJn).1 (Set.disjoint_left.1 hUJ hy)
  have hball : ∀ y ∈ U, ball y (Metric.infDist y J) ⊆ U := by
    intro y hy
    have hsub : ball y (Metric.infDist y J) ⊆ U ∪ (closure U)ᶜ := by
      intro z hz
      by_cases hzc : z ∈ closure U
      · left
        rw [hcl] at hzc
        rcases hzc with h | h
        · exact h
        · exfalso
          have h1 := Metric.infDist_le_dist_of_mem (x := y) h
          rw [mem_ball, dist_comm] at hz
          exact absurd hz (not_lt.2 h1)
      · right
        exact hzc
    exact ((convex_ball y _).isPreconnected).subset_left_of_subset_union hUo hV hdisj hsub
      ⟨y, mem_ball_self (hpos y hy), hy⟩
  have hx' : x ∈ U ∪ J := hcl ▸ hx
  rcases hx' with hxU | hxJ
  · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x hxU
    have hρ : 0 < min r ε := lt_min hr hε
    refine ⟨ball x (min r ε), fun z hz => subset_closure (hrU ((ball_subset_ball (min_le_left _ _)) hz)),
      ball_subset_ball (min_le_right _ _), (convex_ball _ _).isConnected ⟨x, mem_ball_self hρ⟩, ?_⟩
    exact mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hρ)
  · obtain ⟨δ, hδ, hδJ⟩ := hJl ε hε
    set δ' := min (δ / 2) (ε / 2) with hδ'
    have hδ'0 : 0 < δ' := lt_min (half_pos hδ) (half_pos hε)
    -- every point of `closure U` near `x` is joined to `x` by a small connected subset of `closure U`
    have key : ∀ y ∈ closure U, dist y x < δ' →
        ∃ S : Set (ℝ × ℝ), S ⊆ closure U ∧ S ⊆ ball x ε ∧ IsConnected S ∧ x ∈ S ∧ y ∈ S := by
      intro y hy hyx
      have hyx' : dist y x < δ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
      have hyx'' : dist y x < ε / 2 := lt_of_lt_of_le hyx (min_le_right _ _)
      rw [hcl] at hy
      rcases hy with hyU | hyJ
      · obtain ⟨q, hqJ, hq⟩ := hJc.exists_infDist_eq_dist hJn y
        set d := Metric.infDist y J with hd
        have hdx : d ≤ dist y x := Metric.infDist_le_dist_of_mem hxJ
        have hxq : dist x q < δ := by
          calc dist x q ≤ dist x y + dist y q := dist_triangle _ _ _
            _ = dist y x + d := by rw [dist_comm x y, hq]
            _ < δ := by linarith
        obtain ⟨D, hDJ, hDb, hDc, hxD, hqD⟩ := hδJ x hxJ q hqJ hxq
        have hd0 : 0 < d := hpos y hyU
        have hB : IsPreconnected (ball y d ∪ {q}) :=
          ((convex_ball y d).isPreconnected).subset_closure subset_union_left
            (union_subset subset_closure (by
              rw [singleton_subset_iff, closure_ball y hd0.ne', mem_closedBall, dist_comm, ← hq]))
        have hS : IsPreconnected ((ball y d ∪ {q}) ∪ D) :=
          IsPreconnected.union q (Or.inr rfl) hqD hB hDc.isPreconnected
        refine ⟨(ball y d ∪ {q}) ∪ D, ?_, ?_, ⟨⟨x, Or.inr hxD⟩, hS⟩, Or.inr hxD,
          Or.inl (Or.inl (mem_ball_self hd0))⟩
        · rintro z ((hz | hz) | hz)
          · exact subset_closure (hball y hyU hz)
          · rw [mem_singleton_iff.1 hz]; rw [hcl]; exact Or.inr hqJ
          · rw [hcl]; exact Or.inr (hDJ hz)
        · rintro z ((hz | hz) | hz)
          · rw [mem_ball] at hz ⊢
            calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
              _ < d + dist y x := by linarith
              _ < ε := by linarith
          · rw [mem_singleton_iff.1 hz]; exact hDb hqD
          · exact hDb hz
      · have hxy : dist x y < δ := by rw [dist_comm]; linarith
        obtain ⟨D, hDJ, hDb, hDc, hxD, hyD⟩ := hδJ x hxJ y hyJ hxy
        refine ⟨D, fun z hz => ?_, hDb, hDc, hxD, hyD⟩
        rw [hcl]; exact Or.inr (hDJ hz)
    -- the union of these pieces is a connected neighbourhood of `x`
    set 𝒮 : Set (Set (ℝ × ℝ)) := {S | ∃ y ∈ closure U, dist y x < δ' ∧
      S ⊆ closure U ∧ S ⊆ ball x ε ∧ IsConnected S ∧ x ∈ S ∧ y ∈ S} with h𝒮
    have hxδ : dist x x < δ' := by rw [dist_self]; exact hδ'0
    refine ⟨⋃₀ 𝒮, ?_, ?_, ?_, ?_⟩
    · rintro z ⟨S, ⟨y, -, -, hS, -⟩, hz⟩
      exact hS hz
    · rintro z ⟨S, ⟨y, -, -, -, hS, -⟩, hz⟩
      exact hS hz
    · obtain ⟨S₀, hS₀, hS₀b, hS₀c, hxS₀, -⟩ := key x hx hxδ
      refine ⟨⟨x, S₀, ⟨x, hx, hxδ, hS₀, hS₀b, hS₀c, hxS₀, hxS₀⟩, hxS₀⟩, ?_⟩
      refine isPreconnected_sUnion x 𝒮 ?_ ?_
      · rintro S ⟨y, -, -, -, -, -, hxS, -⟩
        exact hxS
      · rintro S ⟨y, -, -, -, -, hSc, -, -⟩
        exact hSc.isPreconnected
    · refine mem_nhdsWithin.2 ⟨ball x δ', isOpen_ball, mem_ball_self hδ'0, ?_⟩
      rintro y ⟨hyb, hyU⟩
      obtain ⟨S, hS, hSb, hSc, hxS, hyS⟩ := key y hyU hyb
      exact ⟨S, ⟨y, hyU, hyb, hS, hSb, hSc, hxS, hyS⟩, hyS⟩

/-- **The closed inner region of a Jordan curve is uniformly locally connected.** -/
theorem jordan_closure_unifLocConn {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧ frontier U = range f ∧
      closure U = U ∪ range f ∧ UnifLocConn (closure U) := by
  obtain ⟨U, V, hUo, hUc, hUb, hVo, hVc, hVb, hfU, hcl, hcomp, hV, hUJ⟩ := jordan_inner_closure hc hi
  exact ⟨U, hUo, hUc, hUb, hfU, hcl, unifLocConn_closure hUo (isCompact_range hc) (range_nonempty f) hcl hUJ hcomp
    (unifLocConn_range_circle hc hi)⟩

end Lightlike.PL.Schoenflies
