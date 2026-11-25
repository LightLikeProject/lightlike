import Lightlike.PL.Schoenflies.AnnulusConnected

/-!
# The inside of a simple polygon near a carrier point

Row G3-188, milestone PL5 (third pass), item 5c (annulus lemma, chord existence, step 1).

* `local_inside`: the inside analogue of `local_outside`.
* `exists_ray_inside`: from each carrier point `w` of a simple polygon there are points `y` of the inside
  arbitrarily near `w` whose half-open segment `(w, y]` lies in the inside.  This is the starting segment of
  a chord that leaves the polygon into its inside.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL Metric

/-- **The inside is locally connected at the carrier.** At each point `w` of a simple polygon there are
arbitrarily small balls whose intersection with the inside is connected and accumulates at `w`. -/
theorem local_inside {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) {w : ℝ × ℝ}
    (hw : w ∈ p.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ IsPreconnected (p.inside ∩ ball w ρ) ∧
      w ∈ closure (p.inside ∩ ball w ρ) := by
  obtain ⟨a, b, ha, hb, hnp, ρ0, hρ0, hcar⟩ := Polygon.local_data hs hw
  have hρ : 0 < min ρ0 ε := lt_min hρ0 hε
  have hcar' : ∀ z ∈ ball w (min ρ0 ε), z ∈ p.carrier ↔ z - w ∈ ray0 a ∪ ray0 b :=
    fun z hz => hcar z (ball_subset_ball (min_le_left _ _) hz)
  obtain ⟨Q₁, Q₂, h1, h2, h3, h4, h5, y₁, hy₁, y₂, hy₂, hne⟩ :=
    Polygon.exists_sectors hs ha hb hnp hρ hcar'
  obtain ⟨hc, hcl⟩ := local_classes (Polygon.isClosed_carrier p)
    (fun x hx => Polygon.eventually_parity_eq p hx) h1 h2 h3 h4 h5 hy₁ hy₂ hne 1
  refine ⟨min ρ0 ε, hρ, min_le_right _ _, hc, ?_⟩
  have := isOpen_ball.inter_closure (s := ball w (min ρ0 ε)) (t := p.inside)
    ⟨mem_ball_self hρ, hcl⟩
  rwa [inter_comm] at this

/-- **Starting segments into the inside.** For a carrier point `w` of a simple polygon and `ε > 0`
there is `y` in the inside with `dist y w < ε` such that every point `w + t • (y - w)`, `0 < t ≤ 1`, lies
in the inside. -/
theorem exists_ray_inside {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) {w : ℝ × ℝ}
    (hw : w ∈ p.carrier) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ p.inside, dist y w < ε ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → w + t • (y - w) ∈ p.inside := by
  obtain ⟨a, b, ha, hb, hnp, ρ0, hρ0, hcar⟩ := Polygon.local_data hs hw
  have hρ : 0 < min ρ0 ε := lt_min hρ0 hε
  have hmem := Polygon.carrier_subset_closure_class hs 1 hw
  obtain ⟨y, hy, hyb⟩ := Metric.mem_closure_iff.1 hmem (min ρ0 ε) hρ
  have hyin : y ∈ p.inside := hy
  refine ⟨y, hyin, lt_of_lt_of_le (by simpa [dist_comm] using hyb) (min_le_right _ _), ?_⟩
  intro t ht0 ht1
  have hyw : ‖y - w‖ < min ρ0 ε := by
    rw [← dist_eq_norm, dist_comm]; exact hyb
  have hyray : y - w ∉ ray0 a ∪ ray0 b := by
    intro h
    have hyb' : y ∈ ball w (min ρ0 ε) := by simpa [dist_comm] using hyb
    exact hyin.1 ((hcar y (ball_subset_ball (min_le_left _ _) hyb')).2 h)
  have hzball : ∀ s : ℝ, 0 < s → s ≤ 1 → w + s • (y - w) ∈ ball w ρ0 := by
    intro s hs0 hs1
    rw [mem_ball, dist_eq_norm]
    have : w + s • (y - w) - w = s • (y - w) := by abel
    rw [this, norm_smul, Real.norm_of_nonneg hs0.le]
    have hy' : ‖y - w‖ < ρ0 := lt_of_lt_of_le hyw (min_le_left _ _)
    calc s * ‖y - w‖ ≤ 1 * ‖y - w‖ := by gcongr
      _ < ρ0 := by simpa using hy'
  have hznot : ∀ s : ℝ, 0 < s → s ≤ 1 → w + s • (y - w) ∉ p.carrier := by
    intro s hs0 hs1 hz
    have := (hcar _ (hzball s hs0 hs1)).1 hz
    have e : w + s • (y - w) - w = s • (y - w) := by abel
    rw [e] at this
    apply hyray
    rcases this with ⟨r, hr, hr'⟩ | ⟨r, hr, hr'⟩
    · left
      refine ⟨r / s, div_nonneg hr hs0.le, ?_⟩
      have : y - w = (1 / s) • (s • (y - w)) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ hs0.ne', one_smul]
      rw [this, hr', smul_smul]; congr 1; field_simp
    · right
      refine ⟨r / s, div_nonneg hr hs0.le, ?_⟩
      have : y - w = (1 / s) • (s • (y - w)) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ hs0.ne', one_smul]
      rw [this, hr', smul_smul]; congr 1; field_simp
  -- the segment is preconnected, avoids the carrier, so the parity is constant
  have hS : IsPreconnected ((fun s : ℝ => w + s • (y - w)) '' Ioc (0 : ℝ) 1) :=
    isPreconnected_Ioc.image _ (by fun_prop)
  have hSX : (fun s : ℝ => w + s • (y - w)) '' Ioc (0 : ℝ) 1 ⊆ p.carrierᶜ := by
    rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    exact hznot s hs0 hs1
  have hyS : y ∈ (fun s : ℝ => w + s • (y - w)) '' Ioc (0 : ℝ) 1 :=
    ⟨1, ⟨one_pos, le_rfl⟩, by simp⟩
  have hzS : w + t • (y - w) ∈ (fun s : ℝ => w + s • (y - w)) '' Ioc (0 : ℝ) 1 :=
    ⟨t, ⟨ht0, ht1⟩, rfl⟩
  have hpar := constOn_of_isPreconnected (Polygon.isClosed_carrier p)
    (fun x hx => Polygon.eventually_parity_eq p hx) hS hSX hzS hyS
  exact ⟨hznot t ht0 ht1, hpar.trans hyin.2⟩

end Lightlike.PL.Schoenflies
