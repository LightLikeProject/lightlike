import Lightlike.PL.PolygonJordan
import Lightlike.PL.Schoenflies.BoundaryPoly

/-!
# The leftmost square of a lattice region lies inside its boundary polygon

Row G3-188, milestone PL5 (third pass), item 5b, route A, step R4.  Let `P = latticePoly v` be a simple
lattice polygon all of whose edges are boundary edges of a set `S` of unit squares, and let `s ∈ S` be a
square with minimal first coordinate whose left edge is an edge of `P`.  Then the centre of `s` is not on
`P` and has parity `1` (it is inside `P`).

* `mem_seg_vert`: a point strictly between the endpoints of a vertical segment lies on it.
* `parity_across_vertical`: the parity jumps across a vertical edge.
* `carrier_vert`: a point of `P` with non-integer height lies on a vertical boundary edge.
* `parity_leftmost`: the centre of the leftmost square has parity `1`.
-/

namespace Lightlike.PL.Schoenflies

open Set Filter Topology Metric Lightlike.PL

/-- A point strictly between the endpoints of a vertical segment lies on it. -/
lemma mem_seg_vert {a u2 v2 r : ℝ} (hr : (u2 < r ∧ r < v2) ∨ (v2 < r ∧ r < u2)) :
    (a, r) ∈ segment ℝ (a, u2) (a, v2) := by
  have key : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 → s * u2 + t * v2 = r →
      (a, r) ∈ segment ℝ (a, u2) (a, v2) := fun s t h1 h2 h3 h4 =>
    ⟨s, t, h1, h2, h3, Prod.ext (by simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
                                    linear_combination a * h3)
      (by simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; exact h4)⟩
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hd : 0 < v2 - u2 := by linarith
    refine key ((v2 - r) / (v2 - u2)) ((r - u2) / (v2 - u2)) (div_nonneg (by linarith) hd.le)
      (div_nonneg (by linarith) hd.le) ?_ ?_
    · field_simp; ring
    · field_simp; ring
  · have hd : 0 < u2 - v2 := by linarith
    refine key ((r - v2) / (u2 - v2)) ((u2 - r) / (u2 - v2)) (div_nonneg (by linarith) hd.le)
      (div_nonneg (by linarith) hd.le) ?_ ?_
    · field_simp; ring
    · field_simp; ring

/-- **The parity jumps across a vertical edge.** -/
theorem parity_across_vertical {n : ℕ} {P : Polygon n} (hs : P.IsSimple) {e : Fin n}
    {a b0 b1 r : ℝ} (hu : P e = (a, b0)) (hv : P (finRotate n e) = (a, b1))
    (hr : (b0 < r ∧ r < b1) ∨ (b1 < r ∧ r < b0)) :
    ∃ ε > 0, ∀ η : ℝ, 0 < η → η < ε → P.parity (a + η, r) = P.parity (a - η, r) + 1 := by
  have hw : (a, r) ∈ P.edge e := by
    unfold Polygon.edge; rw [hu, hv]; exact mem_seg_vert hr
  have h1 : (a, r) ≠ P e := by
    rw [hu]; intro h
    have := congrArg Prod.snd h
    simp only at this
    rcases hr with ⟨x, y⟩ | ⟨x, y⟩ <;> linarith
  have h2 : (a, r) ≠ P (finRotate n e) := by
    rw [hv]; intro h
    have := congrArg Prod.snd h
    simp only at this
    rcases hr with ⟨x, y⟩ | ⟨x, y⟩ <;> linarith
  obtain ⟨c, hc⟩ := Polygon.exists_parity_sides hs hw h1 h2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hc
  refine ⟨ε, hε, fun η h0 h1' => ?_⟩
  have hd : ∀ x : ℝ, dist (a + x, r) (a, r) = |x| := by
    intro x; simp [Prod.dist_eq]
  have hp := hball (y := (a + η, r)) (by rw [hd, abs_of_pos h0]; exact h1')
  have hm := hball (y := (a + (-η), r)) (by rw [hd, abs_neg, abs_of_pos h0]; exact h1')
  have hcr : ∀ x : ℝ, cross (P (finRotate n e) - P e) ((a + x, r) - (a, r)) = -((b1 - b0) * x) := by
    intro x; rw [hu, hv]; simp only [cross, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hcr] at hp hm
  rw [sub_eq_add_neg]
  have h11 : ∀ c : ZMod 2, c + 1 + 1 = c := by decide
  rcases hr with ⟨x, y⟩ | ⟨x, y⟩
  · have hb : 0 < b1 - b0 := by linarith
    rw [hp.2 (by nlinarith), hm.1 (by nlinarith)]
  · have hb : b1 - b0 < 0 := by linarith
    rw [hp.1 (by nlinarith), hm.2 (by nlinarith), h11]

/-- A point of the lattice polygon with non-integer height lies on a vertical boundary edge. -/
lemma carrier_vert {S : Set (ℤ × ℤ)} {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hadj : ∀ i, BdAdj S (v i) (v (finRotate n i))) {z : ℝ × ℝ}
    (hz : z ∈ (latticePoly v).carrier) (hz2 : ∀ y : ℤ, z.2 ≠ y) :
    ∃ x y : ℤ, VB S x y ∧ z.1 = x := by
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  have hi' : z ∈ segment ℝ (pt (v i)) (pt (v (finRotate n i))) := hi
  obtain ⟨x, y, ⟨he, hy, -, -⟩ | ⟨he, hx, -, -⟩⟩ := seg_unit (hadj i).unitStep hi'
  · exact absurd hy (hz2 y)
  · exact ⟨x, y, bdAdj_vert (hadj i) he, hx⟩

/-- **The centre of the leftmost square is inside the boundary polygon.** -/
theorem parity_leftmost {S : Set (ℤ × ℤ)} {n : ℕ} {v : Fin n → ℤ × ℤ}
    (hadj : ∀ i, BdAdj S (v i) (v (finRotate n i))) (hs : (latticePoly v).IsSimple)
    {s : ℤ × ℤ} (hmin : ∀ t ∈ S, s.1 ≤ t.1)
    (hedge : ∃ i, ({v i, v (finRotate n i)} : Set (ℤ × ℤ)) = {(s.1, s.2), (s.1, s.2 + 1)}) :
    (((s.1 : ℝ) + 1 / 2, (s.2 : ℝ) + 1 / 2) ∉ (latticePoly v).carrier) ∧
      (latticePoly v).parity ((s.1 : ℝ) + 1 / 2, (s.2 : ℝ) + 1 / 2) = 1 := by
  set P := latticePoly v with hP
  have hrow : ∀ y : ℤ, (s.2 : ℝ) + 1 / 2 ≠ y := by
    intro y h
    have h1 : (2 * y : ℝ) = 2 * s.2 + 1 := by linarith
    have h' : 2 * y = 2 * s.2 + 1 := by exact_mod_cast h1
    omega
  -- the open ray to the left of the edge misses the polygon
  have hray : ∀ t : ℝ, t < s.1 → (t, (s.2 : ℝ) + 1 / 2) ∉ P.carrier := by
    intro t ht hc
    obtain ⟨x, y, hB, hx⟩ := carrier_vert hadj hc hrow
    have hx' : t = x := hx
    have hxs : x < s.1 := by
      have : (x : ℝ) < s.1 := by linarith
      exact_mod_cast this
    rcases hB with ⟨h1, -⟩ | ⟨h1, -⟩
    · have h3 : s.1 ≤ x := hmin _ h1
      omega
    · have h3 : s.1 ≤ x - 1 := hmin _ h1
      omega
  -- the open segment to the right misses the polygon
  have hseg : ∀ t : ℝ, (s.1 : ℝ) < t → t < s.1 + 1 → (t, (s.2 : ℝ) + 1 / 2) ∉ P.carrier := by
    intro t h1 h2 hc
    obtain ⟨x, y, -, hx⟩ := carrier_vert hadj hc hrow
    have hx' : t = x := hx
    have a1 : s.1 < x := by
      have : (s.1 : ℝ) < x := by linarith
      exact_mod_cast this
    have a2 : x < s.1 + 1 := by
      have : (x : ℝ) < s.1 + 1 := by linarith
      exact_mod_cast this
    omega
  -- parity zero on the left
  obtain ⟨M, hM0, hM⟩ := Polygon.exists_bound P
  have hx0 : -(M + 1) - |(s.1 : ℝ)| - 1 < s.1 := by
    have := neg_abs_le (s.1 : ℝ)
    linarith
  have hfar : P.parity (-(M + 1) - |(s.1 : ℝ)| - 1, (s.2 : ℝ) + 1 / 2) = 0 := by
    refine Polygon.parity_eq_zero_far hM0 hM ?_
    rw [Prod.norm_def]
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    show M < |(-(M + 1) - |(s.1 : ℝ)| - 1)|
    rw [lt_abs]; right; linarith [abs_nonneg (s.1 : ℝ)]
  have hcl := Polygon.isClosed_carrier P
  have hev : ∀ x ∉ P.carrier, ∀ᶠ y in 𝓝 x, P.parity y = P.parity x :=
    fun x hx => Polygon.eventually_parity_eq P hx
  have hrayS : Iio (s.1 : ℝ) ×ˢ ({(s.2 : ℝ) + 1 / 2} : Set ℝ) ⊆ P.carrierᶜ := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    have h2' : z.2 = (s.2 : ℝ) + 1 / 2 := h2
    have e : z = (z.1, (s.2 : ℝ) + 1 / 2) := Prod.ext rfl h2'
    rw [e]; exact hray z.1 h1
  have hrayc : IsPreconnected (Iio (s.1 : ℝ) ×ˢ ({(s.2 : ℝ) + 1 / 2} : Set ℝ)) :=
    ((convex_Iio _).prod (convex_singleton _)).isPreconnected
  -- the edge
  obtain ⟨i, hi⟩ := hedge
  have hvert : ∃ b0 b1 : ℝ, P i = ((s.1 : ℝ), b0) ∧ P (finRotate n i) = ((s.1 : ℝ), b1) ∧
      ((b0 < (s.2 : ℝ) + 1 / 2 ∧ (s.2 : ℝ) + 1 / 2 < b1) ∨
        (b1 < (s.2 : ℝ) + 1 / 2 ∧ (s.2 : ℝ) + 1 / 2 < b0)) := by
    rcases Set.pair_eq_pair_iff.1 hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨s.2, s.2 + 1, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
      · show pt (v i) = _; rw [h1]; simp [pt]
      · show pt (v (finRotate n i)) = _; rw [h2]; simp [pt]
      · linarith
      · linarith
    · refine ⟨s.2 + 1, s.2, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩
      · show pt (v i) = _; rw [h1]; simp [pt]
      · show pt (v (finRotate n i)) = _; rw [h2]; simp [pt]
      · linarith
      · linarith
  obtain ⟨b0, b1, hu, hv', hr⟩ := hvert
  obtain ⟨ε, hε, hj⟩ := parity_across_vertical hs hu hv' hr
  set η : ℝ := min (ε / 2) (1 / 4) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by norm_num)
  have hηε : η < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hleft : P.parity ((s.1 : ℝ) - η, (s.2 : ℝ) + 1 / 2) = 0 := by
    rw [← hfar]
    exact constOn_of_isPreconnected hcl hev hrayc hrayS
      (a := ((s.1 : ℝ) - η, (s.2 : ℝ) + 1 / 2))
      (b := (-(M + 1) - |(s.1 : ℝ)| - 1, (s.2 : ℝ) + 1 / 2))
      ⟨by show (s.1 : ℝ) - η < s.1; linarith, rfl⟩ ⟨by show _ < (s.1 : ℝ); exact hx0, rfl⟩
  have hright : P.parity ((s.1 : ℝ) + η, (s.2 : ℝ) + 1 / 2) = 1 := by
    rw [hj η hη0 hηε, hleft]; simp
  have hsegS : Ioo (s.1 : ℝ) (s.1 + 1) ×ˢ ({(s.2 : ℝ) + 1 / 2} : Set ℝ) ⊆ P.carrierᶜ := by
    intro z hz
    obtain ⟨⟨h1, h1'⟩, h2⟩ := hz
    have h2' : z.2 = (s.2 : ℝ) + 1 / 2 := h2
    have e : z = (z.1, (s.2 : ℝ) + 1 / 2) := Prod.ext rfl h2'
    rw [e]; exact hseg z.1 h1 h1'
  have hsegc : IsPreconnected (Ioo (s.1 : ℝ) (s.1 + 1) ×ˢ ({(s.2 : ℝ) + 1 / 2} : Set ℝ)) :=
    ((convex_Ioo _ _).prod (convex_singleton _)).isPreconnected
  refine ⟨hseg _ (by linarith) (by linarith), ?_⟩
  rw [← hright]
  exact constOn_of_isPreconnected hcl hev hsegc hsegS
    (a := ((s.1 : ℝ) + 1 / 2, (s.2 : ℝ) + 1 / 2)) (b := ((s.1 : ℝ) + η, (s.2 : ℝ) + 1 / 2))
    ⟨⟨by show (s.1 : ℝ) < s.1 + 1 / 2; linarith, by show (s.1 : ℝ) + 1 / 2 < s.1 + 1; linarith⟩, rfl⟩
    ⟨⟨by show (s.1 : ℝ) < s.1 + η; linarith, by show (s.1 : ℝ) + η < s.1 + 1; linarith⟩, rfl⟩

end Lightlike.PL.Schoenflies
