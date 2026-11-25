import Mathlib
import Lightlike.PL.Schoenflies.RegionCompact
import Lightlike.PL.Schoenflies.RegionExtension
import Lightlike.PL.Schoenflies.ChainHit

/-!
# A spoke across the ring between two nested polygons

Row G3-188 (PL5), ring cells.  For simple polygons `p`, `p'` with `region p ⊆ inside p'` and a point `w` of the
carrier of `p`, `exists_spoke` gives a segment `[w', v]` from a point `w'` of the carrier of `p` to a point `v` of
the carrier of `p'` that lies in the ring: its points other than the ends are in `inside p'` and not in
`region p`.  The end `v` is a nearest point of the carrier of `p'` to `w`, and `w'` the last point of `[w, v]` in
`region p`.
-/

open Set Metric Lightlike.PL

namespace Lightlike.PL.Schoenflies

theorem exists_spoke {n m : ℕ} [NeZero n] [NeZero m] {p : Polygon n} {p' : Polygon m} (hs : p.IsSimple)
    (hs' : p'.IsSimple) (hsub : region p ⊆ p'.inside) {w : ℝ × ℝ} (hw : w ∈ p.carrier) :
    ∃ w' ∈ p.carrier, ∃ v ∈ p'.carrier, w' ≠ v ∧ w' ∈ segment ℝ w v ∧
      ∀ z ∈ segment ℝ w' v, z ≠ w' → z ≠ v → z ∈ p'.inside ∧ z ∉ region p := by
  have hKc : IsCompact p'.carrier :=
    (isCompact_region hs').of_isClosed_subset (Polygon.isClosed_carrier p') (carrier_subset_region p')
  have hKne : p'.carrier.Nonempty := by
    refine ⟨p' 0, mem_iUnion.2 ⟨0, ?_⟩⟩
    exact left_mem_segment ℝ _ _
  obtain ⟨v, hvK, hv⟩ := hKc.exists_infDist_eq_dist hKne w
  have hRc : IsCompact (region p) := isCompact_region hs
  have hwR : w ∈ region p := carrier_subset_region p hw
  have hvR : v ∉ region p := fun h => (hsub h).1 hvK
  -- the last point of `[w, v]` in the closed region
  have hSc : IsCompact (segment ℝ w v ∩ region p) := (isCompact_segment' w v).inter_right hRc.isClosed
  obtain ⟨w', hw'S, hmin⟩ := hSc.exists_isMinOn ⟨w, left_mem_segment ℝ w v, hwR⟩
    (f := fun x => dist x v) (by fun_prop)
  have hw'seg : w' ∈ segment ℝ w v := hw'S.1
  have hw'R : w' ∈ region p := hw'S.2
  have hw'v : w' ≠ v := fun h => hvR (h ▸ hw'R)
  have hsubseg : segment ℝ w' v ⊆ segment ℝ w v :=
    (convex_segment w v).segment_subset hw'seg (right_mem_segment ℝ w v)
  -- beyond `w'` the segment leaves the region
  have hout : ∀ z ∈ segment ℝ w' v, z ≠ w' → z ∉ region p := by
    intro z hz hzw hzR
    have h1 : dist w' v ≤ dist z v := hmin (show z ∈ segment ℝ w v ∩ region p from ⟨hsubseg hz, hzR⟩)
    have h2 := dist_add_dist_of_mem_segment hz
    have : dist w' z = 0 := by linarith [dist_nonneg (x := w') (y := z)]
    exact hzw (dist_eq_zero.1 this).symm
  -- `w'` is on the carrier
  have hw'C : w' ∈ p.carrier := by
    rcases hw'R with hin | hc
    · exfalso
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (Polygon.isOpen_inside p) w' hin
      set d := dist w' v with hd
      have hd0 : 0 < d := dist_pos.2 hw'v
      set t : ℝ := min 1 (ε / (2 * d)) with ht
      have ht0 : 0 < t := lt_min one_pos (by positivity)
      have ht1 : t ≤ 1 := min_le_left _ _
      set z : ℝ × ℝ := w' + t • (v - w') with hz
      have hzseg : z ∈ segment ℝ w' v := by
        refine ⟨1 - t, t, by linarith, ht0.le, by ring, ?_⟩
        rw [hz]; module
      have hzw : z ≠ w' := by
        intro h
        have : t • (v - w') = 0 := by rw [hz] at h; simpa using h
        rcases smul_eq_zero.1 this with h0 | h0
        · exact ht0.ne' h0
        · exact hw'v (sub_eq_zero.1 h0).symm
      have hdz : dist z w' < ε := by
        rw [dist_eq_norm, hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm,
          dist_comm]
        calc t * d ≤ ε / (2 * d) * d := by gcongr; exact min_le_right _ _
          _ = ε / 2 := by field_simp
          _ < ε := by linarith
      exact hout z hzseg hzw (Or.inl (hball (mem_ball.2 hdz)))
    · exact hc
  refine ⟨w', hw'C, v, hvK, hw'v, hw'seg, fun z hz hzw hzv => ⟨?_, hout z hz hzw⟩⟩
  -- `z` is in the inside of `p'`
  have hz1 : z ∈ segment ℝ w v := hsubseg hz
  have hd := dist_add_dist_of_mem_segment hz1
  have hzK : z ∉ p'.carrier := by
    intro hzK
    have h1 : infDist z p'.carrier = 0 := (Metric.infDist_zero_of_mem hzK)
    have h2 : infDist w p'.carrier ≤ infDist z p'.carrier + dist w z := infDist_le_infDist_add_dist
    have h3 : 0 < dist z v := dist_pos.2 hzv
    rw [hv, h1] at h2
    linarith
  -- the half-open segment `[w', v)` is preconnected and misses the carrier
  set A : Set (ℝ × ℝ) := (fun t : ℝ => w' + t • (v - w')) '' Ico 0 1 with hA
  have hApre : IsPreconnected A := isPreconnected_Ico.image _ (by fun_prop)
  have hAK : ∀ x ∈ A, x ∉ p'.carrier := by
    rintro _ ⟨t, ⟨ht0, ht1⟩, rfl⟩ hxK
    have hxseg : w' + t • (v - w') ∈ segment ℝ w' v := by
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩; module
    have hxne : w' + t • (v - w') ≠ v := by
      intro h
      have : (1 - t) • (v - w') = 0 := by
        have : v - w' = (v - w') := rfl
        calc (1 - t) • (v - w') = (v - w') - t • (v - w') := by module
          _ = v - (w' + t • (v - w')) := by module
          _ = 0 := by rw [h]; simp
      rcases smul_eq_zero.1 this with h0 | h0
      · linarith
      · exact hw'v (sub_eq_zero.1 h0).symm
    have hxs : w' + t • (v - w') ∈ segment ℝ w v := hsubseg hxseg
    have hdx := dist_add_dist_of_mem_segment hxs
    have h1 : infDist (w' + t • (v - w')) p'.carrier = 0 := Metric.infDist_zero_of_mem hxK
    have h2 : infDist w p'.carrier ≤ infDist (w' + t • (v - w')) p'.carrier + dist w (w' + t • (v - w')) :=
      infDist_le_infDist_add_dist
    have h3 : 0 < dist (w' + t • (v - w')) v := dist_pos.2 hxne
    rw [hv, h1] at h2
    linarith
  have hAcov : A ⊆ p'.outside ∪ p'.inside := by
    intro x hx
    rw [← Polygon.compl_carrier_eq]
    exact hAK x hx
  have hw'A : w' ∈ A := ⟨0, ⟨le_rfl, one_pos⟩, by simp⟩
  have hzA : z ∈ A := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    -- `z = a • w' + b • v` with `b < 1`
    have hb1 : b < 1 := by
      rcases lt_or_eq_of_le (show b ≤ 1 by linarith) with h | h
      · exact h
      · exfalso; apply hzv; have : a = 0 := by linarith
        rw [this, h]; simp
    refine ⟨b, ⟨hb, hb1⟩, ?_⟩
    have : a = 1 - b := by linarith
    rw [this]; module
  rcases hApre.subset_or_subset (Polygon.isOpen_outside p') (Polygon.isOpen_inside p')
      (Polygon.disjoint_outside_inside p') hAcov with hAo | hAi
  · exact absurd (hAo hw'A) (fun h => (Polygon.disjoint_outside_inside p').le_bot ⟨h, hsub hw'R⟩)
  · exact hAi hzA

end Lightlike.PL.Schoenflies
