import Mathlib
import Lightlike.PL.Schoenflies.EarInduction

/-!
# The ear step of the polygonal Schoenflies theorem

Piece 13 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  If a simple polygon `q`
has an ear at the vertex `0` and `d` is in strictly convex position, then a map `f` with
`Spec (q.right 2) (d.right 2) f` for the clipped polygons extends, by the triangle map on the ear
`0, 1, 2`, to a map `F` with `Spec q d F` (`ear_step`).
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- The cyclic vertices of the clipped polygon: `(q.right 2).cyc j = q.cyc (2 + j)` below the
length `n - 1`. -/
lemma right_cyc {n : ℕ} [NeZero n] (q : Polygon n) {j : ℕ} (hj : j < n - 2 + 1) :
    (q.right 2).cyc j = q.cyc (2 + j) := by
  rw [(q.right 2).cyc_of_lt hj]; rfl

/-- The closing edge of the clipped polygon is the diagonal from vertex `0` to vertex `2`. -/
lemma right_last {n : ℕ} [NeZero n] (r : Polygon n) (h4 : 4 ≤ n) :
    (r.right 2).cyc (n - 2) = r.cyc 0 ∧ (r.right 2).cyc (n - 2 + 1) = r.cyc 2 := by
  constructor
  · rw [right_cyc r (by omega)]
    have : 2 + (n - 2) = n + 0 := by omega
    rw [this, Polygon.cyc_self_add]
  · have h := Polygon.cyc_self_add (r.right 2) 0
    rw [add_zero] at h
    rw [h, right_cyc r (by omega)]

/-- `EdgeAff` only has to be checked for the indices `i < n`. -/
lemma edgeAff_of_lt {n : ℕ} [NeZero n] {p c : Polygon n} {f : ℝ × ℝ → ℝ × ℝ}
    (h : ∀ i < n, ∀ t ∈ Icc (0 : ℝ) 1,
      f (p.cyc i + t • (p.cyc (i + 1) - p.cyc i)) = c.cyc i + t • (c.cyc (i + 1) - c.cyc i)) :
    EdgeAff p c f := by
  intro i t ht
  have key : ∀ r : Polygon n, r.cyc (i % n) = r.cyc i ∧ r.cyc (i % n + 1) = r.cyc (i + 1) := by
    intro r
    refine ⟨r.cyc_mod i, ?_⟩
    rw [← r.cyc_mod (i % n + 1), ← r.cyc_mod (i + 1), Nat.mod_add_mod]
  have := h (i % n) (Nat.mod_lt _ (NeZero.pos n)) t ht
  rwa [(key p).1, (key p).2, (key c).1, (key c).2] at this

/-- A point of the edge `[u, v]`, written with its parameter, lies in the hull of a set containing
the endpoints. -/
lemma edge_mem_hull {u v : ℝ × ℝ} {S : Set (ℝ × ℝ)} (hu : u ∈ S) (hv : v ∈ S) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : u + t • (v - u) ∈ convexHull ℝ S :=
  segment_subset_convexHull hu hv (by rw [segment_eq_image']; exact ⟨t, ht, rfl⟩)

/-- **The ear step.**  Clipping the ear at vertex `0` off `q` and off the convex polygon `d`, a
solution `f` of the smaller problem (on `n - 1` vertices) extends to a solution of the problem for
`q` and `d`. -/
theorem ear_step {n : ℕ} [NeZero n] (h4 : 4 ≤ n) {q d : Polygon n} (hs : q.IsSimple)
    (hear : q.Ear 0) (hd : StrictConvexPos d)
    (IH : ∀ p' c' : Polygon (n - 2 + 1), p'.IsSimple → StrictConvexPos c' →
      ∃ f, Spec p' c' f) :
    ∃ F, Spec q d F := by
  have hD : openSegment ℝ (q.cyc 0) (q.cyc 2) ⊆ q.inside := by
    simpa [Polygon.Ear] using hear
  have hopen : ∀ x ∈ openSegment ℝ (q.cyc 0) (q.cyc 2), x ∉ q.carrier := fun x hx hxc =>
    (hD hx).1 hxc
  have hsR := Polygon.isSimple_right hs (b := 2) le_rfl (by omega) hopen
  have hsL := Polygon.isSimple_left hs (b := 2) le_rfl (by omega) hopen
  obtain ⟨f, hf1, hf2, hf3⟩ := IH _ _ hsR (scp_right hd)
  have hq3 : det3 (q.cyc 0) (q.cyc 1) (q.cyc 2) ≠ 0 := by
    simpa [Polygon.left] using det3_ne_zero_of_isSimple hsL
  have hd3 : det3 (d.cyc 0) (d.cyc 1) (d.cyc 2) ≠ 0 :=
    (scp_cyc hd (by omega) (by omega) (by omega) (Or.inl (by omega))).ne'
  obtain ⟨hreg, hseg⟩ := region_ear_split hs h4 hear
  obtain ⟨hhull, hhseg⟩ := hull_range_ear_split hd (by omega : 3 ≤ n)
  set g := triMap (q.cyc 0) (q.cyc 1) (q.cyc 2) (d.cyc 0) (d.cyc 1) (d.cyc 2) with hg
  have hB : BijOn g (convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2})
      (convexHull ℝ {d.cyc 0, d.cyc 1, d.cyc 2}) := triMap_bijOn hq3 hd3
  have hfg : EqOn f g (region (q.right 2) ∩ convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2}) := by
    rw [hseg]
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h1 := hf2 (n - 2) t ht
    obtain ⟨ql1, ql2⟩ := right_last q h4
    obtain ⟨dl1, dl2⟩ := right_last d h4
    rw [ql1, ql2, dl1, dl2] at h1
    rw [h1, hg, triMap_affine, triMap_a, triMap_c hq3]
  have hAB : convexHull ℝ (range (d.right 2)) ∩ convexHull ℝ {d.cyc 0, d.cyc 1, d.cyc 2} ⊆
      g '' (region (q.right 2) ∩ convexHull ℝ {q.cyc 0, q.cyc 1, q.cyc 2}) := by
    rw [hhseg, hseg, hg, triMap_image_segment_ac hq3]
  obtain ⟨F, hF, hFA, hFB⟩ := exists_bijOn_union_glue hf1 hB hfg hAB
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hreg, hhull]; exact hF
  · apply edgeAff_of_lt
    intro i hi t ht
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · have hq0 : q.cyc 0 ∈ ({q.cyc 0, q.cyc 1, q.cyc 2} : Set (ℝ × ℝ)) := by simp
      have hq1 : q.cyc 1 ∈ ({q.cyc 0, q.cyc 1, q.cyc 2} : Set (ℝ × ℝ)) := by simp
      have hq2 : q.cyc 2 ∈ ({q.cyc 0, q.cyc 1, q.cyc 2} : Set (ℝ × ℝ)) := by simp
      interval_cases i
      · show F (q.cyc 0 + t • (q.cyc 1 - q.cyc 0)) = d.cyc 0 + t • (d.cyc 1 - d.cyc 0)
        rw [hFB (edge_mem_hull hq0 hq1 ht), hg, triMap_affine, triMap_a, triMap_b hq3]
      · show F (q.cyc 1 + t • (q.cyc 2 - q.cyc 1)) = d.cyc 1 + t • (d.cyc 2 - d.cyc 1)
        rw [hFB (edge_mem_hull hq1 hq2 ht), hg, triMap_affine, triMap_b hq3, triMap_c hq3]
    · obtain ⟨j, rfl⟩ : ∃ j, i = 2 + j := ⟨i - 2, by omega⟩
      have hj : j < n - 2 + 1 := by omega
      have hj1 : j + 1 < n - 2 + 1 := by omega
      have eq1 : ∀ r : Polygon n, r.cyc (2 + j + 1) = (r.right 2).cyc (j + 1) := fun r => by
        rw [right_cyc r hj1, add_assoc]
      have hmem : q.cyc (2 + j) + t • (q.cyc (2 + j + 1) - q.cyc (2 + j)) ∈ region (q.right 2) := by
        rw [eq1 q, ← right_cyc q hj]
        refine Or.inr (Polygon.segment_cyc_subset_carrier (p := q.right 2) (by omega) hj ?_)
        rw [segment_eq_image']
        exact ⟨t, ht, rfl⟩
      rw [hFA hmem, eq1 q, eq1 d, ← right_cyc q hj, ← right_cyc d hj]
      exact hf2 j t ht
  · obtain ⟨L, hL, hLR⟩ := hf3
    have hsub : ∀ t ∈ L, t.src ⊆ region (q.right 2) := fun t ht x hx => by
      rw [hLR]; exact mem_iUnion₂.2 ⟨t, ht, hx⟩
    refine ⟨⟨q.cyc 0, q.cyc 1, q.cyc 2, d.cyc 0, d.cyc 1, d.cyc 2⟩ :: L, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ⟨hq3, hd3, fun x hx => hFB hx⟩
      · obtain ⟨h1, h2, h3⟩ := hL t ht
        exact ⟨h1, h2, fun x hx => (hFA (hsub t ht hx)).trans (h3 hx)⟩
    · rw [hreg, hLR]
      ext x
      simp only [mem_union, mem_iUnion, List.mem_cons, exists_prop]
      constructor
      · rintro (⟨t, ht, hx⟩ | hx)
        · exact ⟨t, Or.inr ht, hx⟩
        · exact ⟨_, Or.inl rfl, hx⟩
      · rintro ⟨t, rfl | ht, hx⟩
        · exact Or.inr hx
        · exact Or.inl ⟨t, ht, hx⟩

end Lightlike.PL.Schoenflies
