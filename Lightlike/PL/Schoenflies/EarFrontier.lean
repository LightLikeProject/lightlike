import Mathlib
import Lightlike.PL.Schoenflies.EarBoundary

/-!
# The carrier of a convex polygon is the frontier of its hull

Piece 17 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  For a polygon `c` in
strictly convex position with `n ≥ 3` vertices, `c.carrier = frontier (convexHull ℝ (range c))`
(`carrier_eq_frontier_hull_scp`).  On main `Polygon.carrier_eq_frontier_hull` covers only `n = 3`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- `Hs c` is read with all natural indices. -/
lemma Hs_all {n : ℕ} [NeZero n] {c : Polygon n} {u : ℝ × ℝ} (hu : u ∈ Hs c) (k : ℕ) :
    0 ≤ det3 (c.cyc k) (c.cyc (k + 1)) u := by
  have h := hu (k % n) (Nat.mod_lt _ (NeZero.pos n))
  have e1 : c.cyc (k % n) = c.cyc k := c.cyc_mod k
  have e2 : c.cyc (k % n + 1) = c.cyc (k + 1) := by
    rw [← c.cyc_mod (k % n + 1), ← c.cyc_mod (k + 1), Nat.mod_add_mod]
  rwa [e1, e2] at h

/-- Three consecutive vertices (cyclically) of a polygon in strictly convex position are positively
oriented. -/
lemma scp_triple {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) (h3 : 3 ≤ n) (m : ℕ) :
    0 < det3 (c.cyc m) (c.cyc (m + 1)) (c.cyc (m + 2)) := by
  have e1 : c.cyc (m % n) = c.cyc m := c.cyc_mod m
  have e2 : c.cyc (m % n + 1) = c.cyc (m + 1) := by
    rw [← c.cyc_mod (m % n + 1), ← c.cyc_mod (m + 1), Nat.mod_add_mod]
  have e3 : c.cyc (m % n + 2) = c.cyc (m + 2) := by
    rw [← c.cyc_mod (m % n + 2), ← c.cyc_mod (m + 2), Nat.mod_add_mod]
  rw [← e1, ← e2, ← e3]
  have hr : m % n < n := Nat.mod_lt _ (NeZero.pos n)
  generalize m % n = r at hr ⊢
  by_cases h1 : r + 2 < n
  · exact scp_cyc hc (by omega) (by omega) (by omega) (Or.inl h1)
  · by_cases h2 : r + 2 = n
    · have e : c.cyc (r + 2) = c.cyc 0 := by
        rw [h2]; simpa using c.cyc_self_add 0
      rw [e, det3_cyc (c.cyc 0) (c.cyc r) (c.cyc (r + 1))]
      exact scp_cyc hc (i := 0) (j := r) (k := r + 1) (by omega) (by omega) (by omega)
        (Or.inl (by omega))
    · have h3' : r + 1 = n := by omega
      have e : c.cyc (r + 1) = c.cyc 0 := by
        rw [h3']; simpa using c.cyc_self_add 0
      have e' : c.cyc (r + 2) = c.cyc 1 := by
        rw [show r + 2 = n + 1 by omega]; exact c.cyc_self_add 1
      rw [e, e', ← det3_cyc (c.cyc r) (c.cyc 0) (c.cyc 1)]
      exact scp_cyc hc (i := 0) (j := 1) (k := r) (by omega) (by omega) (by omega)
        (Or.inl (by omega))

/-- A point on the line `ab` is on the segment `[a, b]` when the orientations against the two
neighbouring edges have the right sign. -/
lemma mem_segment_of_det3 {p a b q u : ℝ × ℝ} (D1 : 0 < det3 p a b) (D2 : 0 < det3 a b q)
    (hp : 0 ≤ det3 p a u) (hq : 0 ≤ det3 b q u) (h0 : det3 a b u = 0) : u ∈ segment ℝ a b := by
  have hab : a ≠ b := by
    rintro rfl
    rw [det3_self_right] at D1
    exact lt_irrefl _ D1
  have hN : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_contra hcon
    apply hab
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    exact Prod.ext (by linarith) (by linarith)
  have h0' : (b.1 - a.1) * (u.2 - a.2) - (u.1 - a.1) * (b.2 - a.2) = 0 := by
    simp only [det3, cross, Prod.fst_sub, Prod.snd_sub] at h0
    linarith
  obtain ⟨t, hx⟩ : ∃ t : ℝ, u = a + t • (b - a) := by
    refine ⟨((u.1 - a.1) * (b.1 - a.1) + (u.2 - a.2) * (b.2 - a.2)) /
      ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2), ?_⟩
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
      field_simp
      linear_combination (-(b.2 - a.2)) * h0'
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
      field_simp
      linear_combination (b.1 - a.1) * h0'
  subst hx
  have e1 : det3 p a (a + t • (b - a)) = t * det3 p a b := by
    simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  have e2 : det3 b q (a + t • (b - a)) = (1 - t) * det3 a b q := by
    simp only [det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]; ring
  rw [e1] at hp
  rw [e2] at hq
  have ht0 : 0 ≤ t := by by_contra h; nlinarith
  have ht1 : t ≤ 1 := by by_contra h; nlinarith
  rw [segment_eq_image']
  exact ⟨t, ⟨ht0, ht1⟩, rfl⟩

/-- A point of `Hs c` on the line of the edge `k` lies on the edge. -/
lemma mem_edge_of_det3_zero {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c)
    (h3 : 3 ≤ n) {u : ℝ × ℝ} (hu : u ∈ Hs c) {k : ℕ}
    (h0 : det3 (c.cyc k) (c.cyc (k + 1)) u = 0) : u ∈ segment ℝ (c.cyc k) (c.cyc (k + 1)) := by
  have i1 : c.cyc (k + n - 1 + 1) = c.cyc k := by
    rw [show k + n - 1 + 1 = n + k by omega]; exact c.cyc_self_add k
  have i2 : c.cyc (k + n - 1 + 2) = c.cyc (k + 1) := by
    rw [show k + n - 1 + 2 = n + (k + 1) by omega]; exact c.cyc_self_add (k + 1)
  have D1 := scp_triple hc h3 (k + n - 1)
  rw [i1, i2] at D1
  have hp := Hs_all hu (k + n - 1)
  rw [i1] at hp
  exact mem_segment_of_det3 D1 (scp_triple hc h3 k) hp (Hs_all hu (k + 1)) h0

lemma isClosed_hull {n : ℕ} (c : Fin n → ℝ × ℝ) : IsClosed (convexHull ℝ (range c)) :=
  ((Set.finite_range c).isCompact_convexHull ℝ).isClosed

lemma continuous_det3_right (a b : ℝ × ℝ) : Continuous fun u : ℝ × ℝ => det3 a b u := by
  unfold det3 cross; fun_prop

/-- The frontier of the hull lies on the carrier. -/
lemma frontier_subset_carrier {n : ℕ} [NeZero n] {c : Polygon n} (h3 : 3 ≤ n)
    (hc : StrictConvexPos c) : frontier (convexHull ℝ (range c)) ⊆ c.carrier := by
  intro x hx
  rw [(isClosed_hull c).frontier_eq, hull_eq_Hs h3 hc] at hx
  obtain ⟨hxH, hxi⟩ := hx
  by_contra hxc
  have hne : ∀ k, k < n → 0 < det3 (c.cyc k) (c.cyc (k + 1)) x := by
    intro k hk
    refine lt_of_le_of_ne (hxH k hk) fun h0 => hxc ?_
    exact (Polygon.mem_carrier_iff (by omega)).2 ⟨k, hk, mem_edge_of_det3_zero hc h3 hxH h0.symm⟩
  apply hxi
  have hopen : IsOpen (⋂ k ∈ Set.Iio n, {u : ℝ × ℝ | 0 < det3 (c.cyc k) (c.cyc (k + 1)) u}) :=
    (Set.finite_Iio n).isOpen_biInter fun k _ =>
      isOpen_lt continuous_const (continuous_det3_right _ _)
  refine mem_interior.2 ⟨_, ?_, hopen, ?_⟩
  · intro u hu k hk
    have := mem_iInter₂.1 hu k hk
    exact le_of_lt this
  · exact mem_iInter₂.2 fun k hk => hne k hk

/-- The carrier lies on the frontier of the hull. -/
lemma carrier_subset_frontier {n : ℕ} [NeZero n] {c : Polygon n} (h3 : 3 ≤ n)
    (hc : StrictConvexPos c) : c.carrier ⊆ frontier (convexHull ℝ (range c)) := by
  intro x hx
  obtain ⟨k, hk, hxs⟩ := (Polygon.mem_carrier_iff (by omega)).1 hx
  have hmem : ∀ m : ℕ, c.cyc m ∈ range c := fun m =>
    ⟨⟨m % n, Nat.mod_lt _ (NeZero.pos n)⟩, rfl⟩
  have hxH : x ∈ convexHull ℝ (range c) :=
    segment_subset_convexHull (hmem k) (hmem (k + 1)) hxs
  rw [(isClosed_hull c).frontier_eq]
  refine ⟨hxH, fun hint => ?_⟩
  set a := c.cyc k
  set b := c.cyc (k + 1)
  have hD : 0 < det3 a b (c.cyc (k + 2)) := scp_triple hc h3 k
  have hab : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_contra hcon
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have : b = a := Prod.ext (by linarith) (by linarith)
    rw [this] at hD
    simp [det3, cross] at hD
  rw [segment_eq_image'] at hxs
  obtain ⟨t, -, hxt⟩ := hxs
  have hx_def : x = a + t • (b - a) := hxt.symm
  set w : ℝ × ℝ := (b.2 - a.2, -(b.1 - a.1)) with hw
  have hdet : ∀ ε : ℝ, det3 a b (x + ε • w) = -ε * ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2) := by
    intro ε
    simp only [hx_def, hw, det3, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  have hg : Continuous fun ε : ℝ => x + ε • w := by fun_prop
  have ht : Filter.Tendsto (fun ε : ℝ => x + ε • w) (nhds 0) (nhds x) := by
    simpa using hg.tendsto 0
  have h1 : ∀ᶠ ε in nhds (0 : ℝ), x + ε • w ∈ interior (convexHull ℝ (range c)) :=
    ht.eventually (isOpen_interior.mem_nhds hint)
  have h2 := h1.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  obtain ⟨ε, hε, hεpos⟩ := (h2.and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  have hin := hull_eq_Hs h3 hc ▸ interior_subset hε
  have := hin k hk
  rw [hdet ε] at this
  nlinarith

/-- **The carrier of a convex polygon is the frontier of its hull.**  For a polygon `c` with `n ≥ 3`
vertices in strictly convex position, the union of its edges is the frontier of the convex hull of its
vertices. (On main this is `Polygon.carrier_eq_frontier_hull`, for triangles only.) -/
theorem carrier_eq_frontier_hull_scp {n : ℕ} [NeZero n] {c : Polygon n} (h3 : 3 ≤ n)
    (hc : StrictConvexPos c) : c.carrier = frontier (convexHull ℝ (range c)) :=
  Subset.antisymm (carrier_subset_frontier h3 hc) (frontier_subset_carrier h3 hc)

end Lightlike.PL.Schoenflies
