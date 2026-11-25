import Mathlib
import Lightlike.PL.Schoenflies.JanisConn
import Lightlike.PL.Schoenflies.JordanArc
import Lightlike.PL.Schoenflies.JordanClosure

/-!
# The open inside of a Jordan curve is uniformly locally connected

Row G3-188 (PL5), step 2 of the pass-4 plan.  `jordan_inner_ulc`: for every `ε > 0` there is `δ > 0` such
that two points of the open inner region `U` closer than `δ` are joined by a path in `U ∩ ball x ε`.

Proof: if the segment `[x, y]` misses the curve it lies in `U`.  Otherwise let `q` lie on `[x, y] ∩ J`, take
the long arc `B` of `J` avoiding a neighbourhood of `q` (`exists_arc_complement`) and apply
`joinedIn_union_compl_of_isPreconnected` to `J` and `K₂ = (closedBall x ε \ ball x (ε/2)) ∪ B`, whose
intersection with `J` is the arc `B`.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric

/-- A connected set missing the curve and meeting the inside lies in the inside. -/
lemma subset_inner_of_connected {U J S : Set (ℝ × ℝ)} (hUo : IsOpen U) (hcl : closure U = U ∪ J)
    (hS : IsPreconnected S) (hSJ : Disjoint S J) {z : ℝ × ℝ} (hzS : z ∈ S) (hzU : z ∈ U) : S ⊆ U := by
  have hV : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  have hdisj : Disjoint U (closure U)ᶜ := disjoint_compl_right_iff_subset.2 subset_closure
  have hsub : S ⊆ U ∪ (closure U)ᶜ := by
    intro w hw
    by_cases hwc : w ∈ closure U
    · rw [hcl] at hwc
      rcases hwc with h | h
      · exact Or.inl h
      · exact absurd h (Set.disjoint_left.1 hSJ hw)
    · exact Or.inr hwc
  exact hS.subset_left_of_subset_union hUo hV hdisj hsub ⟨z, hzS, hzU⟩

theorem jordan_inner_ulc {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {U : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U) (hcl : closure U = U ∪ range f)
    (hUJ : Disjoint U (range f)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ U, ∀ y ∈ U, dist x y < δ → JoinedIn (U ∩ ball x ε) x y := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, harc⟩ := exists_arc_complement hc hi (ε := ε / 4) (by positivity)
  refine ⟨min (δ₁ / 2) (ε / 4), lt_min (half_pos hδ₁) (by positivity), fun x hx y hy hxy => ?_⟩
  have hxy₁ : dist x y < δ₁ / 2 := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy₂ : dist x y < ε / 4 := lt_of_lt_of_le hxy (min_le_right _ _)
  have hseg_dist : ∀ z ∈ segment ℝ x y, dist z x ≤ dist x y := by
    intro z hz
    have := (convex_closedBall x (dist x y)).segment_subset (mem_closedBall_self dist_nonneg)
      (by rw [mem_closedBall, dist_comm]) hz
    exact mem_closedBall.1 this
  have hseg_dist' : ∀ z ∈ segment ℝ x y, ∀ z' ∈ segment ℝ x y, dist z z' < δ₁ := by
    intro z hz z' hz'
    calc dist z z' ≤ dist z x + dist z' x := by rw [dist_comm z' x]; exact dist_triangle _ _ _
      _ < δ₁ := by linarith [hseg_dist z hz, hseg_dist z' hz']
  by_cases hJ : ∃ q ∈ segment ℝ x y, q ∈ range f
  · obtain ⟨q, hqseg, t₀, hqt⟩ := hJ
    subst hqt
    obtain ⟨B, hBc, hBconn, hBJ, hBnear, hBfar⟩ := harc t₀
    set K₂ : Set (ℝ × ℝ) := (closedBall x ε \ ball x (ε / 2)) ∪ B with hK₂
    have hJc : IsCompact (range f) := isCompact_range hc
    have hK₂c : IsCompact K₂ :=
      ((isCompact_closedBall x ε).diff isOpen_ball).union hBc
    have hqx : dist (f t₀) x ≤ dist x y := hseg_dist _ hqseg
    -- the intersection is the arc
    have hinter : range f ∩ K₂ = B := by
      apply Subset.antisymm
      · rintro z ⟨hzJ, hz | hz⟩
        · by_contra hzB
          have h1 := hBfar z hzJ hzB
          have h2 : dist z x < ε / 2 := by
            calc dist z x ≤ dist z (f t₀) + dist (f t₀) x := dist_triangle _ _ _
              _ < ε / 4 + ε / 4 := by linarith
              _ = ε / 2 := by ring
          exact hz.2 (mem_ball.2 h2)
        · exact hz
      · intro z hz; exact ⟨hBJ hz, Or.inr hz⟩
    have hP : JoinedIn (range f)ᶜ x y := by
      have hpc := (hUo.isConnected_iff_isPathConnected.1 hUc)
      exact (hpc.joinedIn x hx y hy).mono (fun z hz => Set.disjoint_left.1 hUJ hz)
    have hQ : JoinedIn K₂ᶜ x y := by
      refine JoinedIn.of_segment_subset (fun z hz hzK => ?_)
      rcases hzK with hzK | hzK
      · have := hseg_dist z hz
        exact hzK.2 (mem_ball.2 (by linarith))
      · exact hBnear z (hBJ hzK) (hseg_dist' z hz _ hqseg) hzK
    obtain ⟨γ, hγ⟩ := joinedIn_union_compl_of_isPreconnected hJc hK₂c
      (by rw [hinter]; exact hBconn.isPreconnected) hP hQ
    have hγJ : ∀ t, γ t ∉ range f := fun t h => hγ t (Or.inl h)
    have hγS : ∀ t, γ t ∉ closedBall x ε \ ball x (ε / 2) := fun t h => hγ t (Or.inr (Or.inl h))
    have hconn : IsPreconnected (range γ) := (isConnected_range γ.continuous).isPreconnected
    have hball : range γ ⊆ ball x (ε / 2) := by
      have hsub : range γ ⊆ ball x (ε / 2) ∪ (closedBall x ε)ᶜ := by
        rintro _ ⟨t, rfl⟩
        by_cases h1 : γ t ∈ ball x (ε / 2)
        · exact Or.inl h1
        · right
          intro h2
          exact hγS t ⟨h2, h1⟩
      refine hconn.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl ?_ hsub
        ⟨x, ⟨0, by simp⟩, mem_ball_self (by positivity)⟩
      exact Set.disjoint_left.2 fun z hz hz' => hz' (ball_subset_closedBall (ball_subset_ball (by linarith) hz))
    have hU : range γ ⊆ U :=
      subset_inner_of_connected hUo hcl hconn (Set.disjoint_left.2 fun z ⟨t, ht⟩ hzJ => hγJ t (ht ▸ hzJ))
        (⟨0, by simp⟩ : x ∈ range γ) hx
    exact ⟨γ, fun t => ⟨hU ⟨t, rfl⟩, ball_subset_ball (by linarith) (hball ⟨t, rfl⟩)⟩⟩
  · push Not at hJ
    have hsegU : segment ℝ x y ⊆ U :=
      subset_inner_of_connected hUo hcl (convex_segment x y).isPreconnected
        (Set.disjoint_left.2 fun z hz hzJ => hJ z hz hzJ) (left_mem_segment ℝ x y) hx
    refine JoinedIn.of_segment_subset (fun z hz => ⟨hsegU hz, ?_⟩)
    rw [mem_ball]
    exact lt_of_le_of_lt (hseg_dist z hz) (by linarith)

end Lightlike.PL.Schoenflies
