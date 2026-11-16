import Lightlike.PL.PolygonWedge

/-!
# A diagonal from the extreme vertex

If a simple polygon with at least four vertices has a vertex, other than the extreme vertex `v`
and its two neighbours, in the closed triangle that they span, then the open segment from `v` to
the vertex of that kind closest to `v` (smallest `λ + μ`) lies in the inside.

## Main results

* `Lightlike.PL.Polygon.exists_vz_diagonal`
-/

open Set

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ} {p : Polygon n}

lemma wl_self (v u w : ℝ × ℝ) : wl v u w v = 0 := by simp [wl, cross]

lemma wm_self (v u w : ℝ × ℝ) : wm v u w v = 0 := by simp [wm, cross]

lemma wl_aff {v u w x y : ℝ × ℝ} {a b : ℝ} (h : a + b = 1) :
    wl v u w (a • x + b • y) = a * wl v u w x + b * wl v u w y := by
  have := wf_affine v u w 0 0 x y a b h
  simpa [wf_zero] using this

lemma wm_aff {v u w x y : ℝ × ℝ} {a b : ℝ} (h : a + b = 1) :
    wm v u w (a • x + b • y) = a * wm v u w x + b * wm v u w y := by
  have := wf_affine v u w 0 1 x y a b h
  simpa [wf_one] using this

/-- **The diagonal from the extreme vertex to the nearest vertex in the corner triangle.** -/
theorem exists_vz_diagonal [NeZero n] (hs : p.IsSimple) (hn : 4 ≤ n) {j : Fin n}
    (hext : ∀ i, LexLE (p j) (p i))
    (hz : ∃ i, i ≠ (finRotate n).symm j ∧ i ≠ j ∧ i ≠ finRotate n j ∧
      0 ≤ wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
      0 ≤ wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
      wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) +
        wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ≤ 1) :
    ∃ i, i ≠ j ∧ i ≠ (finRotate n).symm j ∧ i ≠ finRotate n j ∧
      openSegment ℝ (p j) (p i) ⊆ p.inside := by
  classical
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  have hcr : cross (u - v) (w - v) ≠ 0 := corner_cross_ne hs hext
  set g : Fin n → ℝ := fun i => wl v u w (p i) + wm v u w (p i) with hg
  set S : Finset (Fin n) := Finset.univ.filter fun i =>
    i ≠ k ∧ i ≠ j ∧ i ≠ finRotate n j ∧ 0 ≤ wl v u w (p i) ∧ 0 ≤ wm v u w (p i) ∧ g i ≤ 1 with hS
  obtain ⟨i₁, hi₁⟩ := hz
  have hne : S.Nonempty := ⟨i₁, by simpa [hS, hg] using hi₁⟩
  obtain ⟨i₀, hi₀S, hmin⟩ := S.exists_min_image g hne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi₀S
  obtain ⟨h0k, h0j, h0m, hl0, hm0, hg1⟩ := hi₀S
  set z := p i₀ with hzdef
  set c := g i₀ with hc
  -- both coordinates of `z` are positive
  have hedge_i : z ∈ p.edge i₀ := left_mem_segment ℝ _ _
  have hlz : 0 < wl v u w z := by
    refine lt_of_le_of_ne hl0 fun h => ?_
    have hzj : z ∈ p.edge j := by
      refine mem_segment_vw hcr h.symm hm0 ?_
      have : wl v u w z + wm v u w z ≤ 1 := hg1
      linarith
    rcases edge_meet_cases hs h0j hedge_i hzj with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h0k ((finRotate n).injective (h1.trans hkj.symm))
    · exact h0m h1.symm
  have hmz : 0 < wm v u w z := by
    refine lt_of_le_of_ne hm0 fun h => ?_
    have hedgek : p.edge k = segment ℝ v u := by
      simp only [edge, hkj, hu, hv]; exact segment_symm ℝ _ _
    have hzk : z ∈ p.edge k := by
      rw [hedgek]
      refine mem_segment_vu hcr h.symm hl0 ?_
      have : wl v u w z + wm v u w z ≤ 1 := hg1
      linarith
    rcases edge_meet_cases hs h0k hedge_i hzk with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact hs.1 i₀ (by rw [h1]; exact h2)
    · exact h0j (by rw [← h1, hkj])
  have hvert : ∀ i, ¬ (0 < wl v u w (p i) ∧ 0 < wm v u w (p i) ∧
      wl v u w (p i) + wm v u w (p i) < c) := by
    rintro i ⟨ha, hb, hd⟩
    have hik : i ≠ k := by rintro rfl; rw [← hu, wm_u] at hb; exact lt_irrefl _ hb
    have hij : i ≠ j := by rintro rfl; rw [← hv, wl_self] at ha; exact lt_irrefl _ ha
    have him : i ≠ finRotate n j := by rintro rfl; rw [← hw, wl_w] at ha; exact lt_irrefl _ ha
    have hiS : i ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hik, hij, him, ha.le, hb.le, by simp only [hg]; linarith [hg1]⟩
    have := hmin i hiS
    simp only [hg, hc] at this hd
    linarith
  have hc1 : c ≤ 1 := hg1
  have hcpos : 0 < c := by simp only [hc, hg]; linarith
  have hfree : ∀ q ∈ openSegment ℝ v z, q ∉ p.carrier := by
    rintro q ⟨a, b, ha, hb, hab, rfl⟩
    have e1 : wl v u w (a • v + b • z) = b * wl v u w z := by
      rw [wl_aff hab, wl_self]; ring
    have e2 : wm v u w (a • v + b • z) = b * wm v u w z := by
      rw [wm_aff hab, wm_self]; ring
    refine wedge_disjoint_carrier hs hn hcr hc1 hvert ?_ ?_ ?_
    · rw [e1]; exact mul_pos hb hlz
    · rw [e2]; exact mul_pos hb hmz
    · rw [e1, e2]
      have hb1 : b < 1 := by linarith
      have : wl v u w z + wm v u w z = c := rfl
      nlinarith
  obtain ⟨ρ, hρ, hcone⟩ := inside_near_corner hs hext
  refine ⟨i₀, h0j, h0k, h0m, ?_⟩
  have hpre : IsPreconnected (openSegment ℝ v z) := (convex_openSegment v z).isPreconnected
  have hsub : openSegment ℝ v z ⊆ p.carrierᶜ := fun q hq => hfree q hq
  rcases subset_outside_or_inside hpre hsub with h | h
  · exfalso
    set N := ‖z - v‖ with hN
    set b := min (1 / 2 : ℝ) (ρ / (2 * (N + 1))) with hb
    have hN0 : 0 ≤ N := norm_nonneg _
    have hden : 0 < 2 * (N + 1) := by positivity
    have hb0 : 0 < b := lt_min (by norm_num) (div_pos hρ hden)
    have hb1 : b ≤ 1 / 2 := min_le_left _ _
    have hb2 : b ≤ ρ / (2 * (N + 1)) := min_le_right _ _
    set q := (1 - b) • v + b • z with hq
    have hqseg : q ∈ openSegment ℝ v z := ⟨1 - b, b, by linarith, hb0, by ring, rfl⟩
    have hqv : q - v = b • (z - v) := by rw [hq]; ext <;> simp <;> ring
    have hball : q ∈ Metric.ball v ρ := by
      rw [Metric.mem_ball, dist_eq_norm, hqv, norm_smul, Real.norm_of_nonneg hb0.le]
      have h1 : b * (2 * (N + 1)) ≤ ρ := by
        have := mul_le_mul_of_nonneg_right hb2 hden.le
        rwa [div_mul_cancel₀ _ hden.ne'] at this
      nlinarith
    have hqin : q ∈ p.inside := by
      refine hcone q hball ⟨b * wl v u w z, b * wm v u w z, mul_pos hb0 hlz, mul_pos hb0 hmz, ?_⟩
      rw [hqv]
      conv_lhs => rw [sub_eq_wl_wm hcr z]
      rw [smul_add, smul_smul, smul_smul]
    exact (Set.disjoint_left.1 (disjoint_outside_inside p)) (h hqseg) hqin
  · exact h

end Polygon
end Lightlike.PL
