import Mathlib
import Lightlike.PL.Schoenflies.EarMain

/-!
# The boundary of the polygonal Schoenflies map

Piece 16 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).

* `image_carrier`: an edge-affine map `f` (`EdgeAff p c f`) sends the carrier of `p` onto the
  carrier of `c`.
* `Hs c`: the intersection of the closed half-planes left of the edges of `c`;
  `hull_eq_Hs`: for a polygon `c` in strictly convex position, `convexHull (range c) = Hs c`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **An edge-affine map carries the carrier of `p` onto the carrier of `c`.** -/
theorem image_carrier {n : ℕ} [NeZero n] (hn : 2 ≤ n) {p c : Polygon n} {f : ℝ × ℝ → ℝ × ℝ}
    (h : EdgeAff p c f) : f '' p.carrier = c.carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, hkn, hk⟩ := (Polygon.mem_carrier_iff hn).1 hx
    rw [segment_eq_image'] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    refine (Polygon.mem_carrier_iff hn).2 ⟨k, hkn, ?_⟩
    rw [segment_eq_image']
    exact ⟨t, ht, (h k t ht).symm⟩
  · intro hy
    obtain ⟨k, hkn, hk⟩ := (Polygon.mem_carrier_iff hn).1 hy
    rw [segment_eq_image'] at hk
    obtain ⟨t, ht, rfl⟩ := hk
    refine ⟨_, (Polygon.mem_carrier_iff hn).2 ⟨k, hkn, ?_⟩, h k t ht⟩
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩

/-- A point with three nonnegative orientations against the sides of a positively oriented triangle
lies in the triangle. -/
lemma tri_mem_hull {a b c u : ℝ × ℝ} (hD : 0 < det3 a b c) (h1 : 0 ≤ det3 b c u)
    (h2 : 0 ≤ det3 c a u) (h3 : 0 ≤ det3 a b u) : u ∈ convexHull ℝ {a, b, c} := by
  have hsum : det3 b c u + det3 c a u + det3 a b u = det3 a b c := by
    simp only [det3, cross, Prod.fst_sub, Prod.snd_sub]; ring
  have hD' : det3 a b c ≠ 0 := hD.ne'
  have hu : u = (det3 b c u / det3 a b c) • a + (det3 c a u / det3 a b c) • b +
      (det3 a b u / det3 a b c) • c := by
    apply Prod.ext
    · simp only [det3, cross, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.smul_fst,
        smul_eq_mul] at hD' ⊢
      field_simp
      ring
    · simp only [det3, cross, Prod.fst_sub, Prod.snd_sub, Prod.snd_add, Prod.smul_snd,
        smul_eq_mul] at hD' ⊢
      field_simp
      ring
  have hmem := (convex_convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))).sum_mem
    (t := (Finset.univ : Finset (Fin 3)))
    (w := ![det3 b c u / det3 a b c, det3 c a u / det3 a b c, det3 a b u / det3 a b c])
    (z := ![a, b, c])
    (by intro i _; fin_cases i <;> simp <;> positivity)
    (by simp [Fin.sum_univ_three]; field_simp; linarith)
    (by
      intro i _
      fin_cases i <;> simp <;> exact subset_convexHull ℝ _ (by simp))
  simp only [Fin.sum_univ_three] at hmem
  simpa [← hu] using hmem

/-- The intersection of the closed half-planes to the left of the edges of `c`. -/
def Hs {n : ℕ} [NeZero n] (c : Polygon n) : Set (ℝ × ℝ) :=
  {u | ∀ k, k < n → 0 ≤ det3 (c.cyc k) (c.cyc (k + 1)) u}

lemma convex_Hs {n : ℕ} [NeZero n] (c : Polygon n) : Convex ℝ (Hs c) := by
  have : Hs c = ⋂ k : ℕ, ⋂ (_ : k < n), {u | 0 ≤ det3 (c.cyc k) (c.cyc (k + 1)) u} := by
    ext u; simp [Hs]
  rw [this]
  exact convex_iInter fun k => convex_iInter fun _ => convex_det3_nonneg _ _

/-- Every vertex of a polygon in strictly convex position lies in `Hs c`. -/
lemma vertex_mem_Hs {n : ℕ} [NeZero n] {c : Polygon n} (hc : StrictConvexPos c) (j : Fin n) :
    c j ∈ Hs c := by
  obtain ⟨j, hj⟩ := j
  have hcj : c ⟨j, hj⟩ = c.cyc j := (c.cyc_of_lt hj).symm
  show c ⟨j, hj⟩ ∈ Hs c
  rw [hcj]
  intro k hk
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · by_cases h0 : k + 1 < n ∨ 0 < j
    · have := (scp_cyc hc hjk (by omega) (by omega) h0).le
      rwa [← det3_cyc] at this
    · have hj0 : j = 0 := by omega
      have hk1 : k + 1 = n := by omega
      have : c.cyc (k + 1) = c.cyc 0 := by
        rw [hk1]; simpa using c.cyc_self_add 0
      rw [this, hj0, det3_self_right]
  · rw [det3_self_left_right]
  · by_cases hk1 : k + 1 = j
    · rw [hk1, det3_self_right]
    · exact (scp_cyc hc (by omega) (by omega) (by omega) (Or.inl hj)).le

/-- **The half-plane description of a convex polygon, hard inclusion.**  By strong induction on the
number of vertices, cutting off the ear at the vertex `1`. -/
theorem Hs_subset_hull : ∀ (n : ℕ) [NeZero n] (c : Polygon n), 3 ≤ n → StrictConvexPos c →
    Hs c ⊆ convexHull ℝ (range c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _ c h3 hc u hu
    have hD : 0 < det3 (c.cyc 0) (c.cyc 1) (c.cyc 2) :=
      scp_cyc hc (by omega) (by omega) (by omega) (Or.inl (by omega))
    have e0 : 0 ≤ det3 (c.cyc 0) (c.cyc 1) u := by simpa using hu 0 (by omega)
    have e1 : 0 ≤ det3 (c.cyc 1) (c.cyc 2) u := by simpa using hu 1 (by omega)
    have hsub : convexHull ℝ {c.cyc 0, c.cyc 1, c.cyc 2} ⊆ convexHull ℝ (range c) := by
      apply convexHull_mono
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨0, by omega⟩, (c.cyc_of_lt (by omega)).symm⟩
      · exact ⟨⟨1, by omega⟩, (c.cyc_of_lt (by omega)).symm⟩
      · exact ⟨⟨2, by omega⟩, (c.cyc_of_lt (by omega)).symm⟩
    rcases Nat.lt_or_ge n 4 with h | h4
    · obtain rfl : n = 3 := by omega
      have e2 : 0 ≤ det3 (c.cyc 2) (c.cyc 0) u := by
        have := hu 2 (by omega)
        have h30 : c.cyc (2 + 1) = c.cyc 0 := by simpa using c.cyc_self_add 0
        rwa [h30] at this
      exact hsub (tri_mem_hull hD e1 e2 e0)
    · by_cases hd : 0 ≤ det3 (c.cyc 0) (c.cyc 2) u
      · have hu' : u ∈ Hs (c.right 2) := by
          intro k hk
          obtain ⟨l1, l2⟩ := right_last c h4
          by_cases hkn : k = n - 2
          · subst hkn
            rw [l1, l2]; exact hd
          · rw [right_cyc c (by omega), right_cyc c (by omega)]
            exact hu (2 + k) (by omega)
        have := ih (n - 2 + 1) (by omega) (c.right 2) (by omega) (scp_right hc) hu'
        rw [(hull_range_ear_split hc h3).1]
        exact Or.inl this
      · have e2 : 0 ≤ det3 (c.cyc 2) (c.cyc 0) u := by
          rw [det3_swap]; linarith [not_le.1 hd]
        exact hsub (tri_mem_hull hD e1 e2 e0)

/-- **A polygon in strictly convex position bounds the intersection of its edge half-planes.** -/
theorem hull_eq_Hs {n : ℕ} [NeZero n] {c : Polygon n} (h3 : 3 ≤ n) (hc : StrictConvexPos c) :
    convexHull ℝ (range c) = Hs c :=
  Subset.antisymm (convexHull_min (by rintro _ ⟨j, rfl⟩; exact vertex_mem_Hs hc j) (convex_Hs c))
    (Hs_subset_hull n c h3 hc)

end Lightlike.PL.Schoenflies
