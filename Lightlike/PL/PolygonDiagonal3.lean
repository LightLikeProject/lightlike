import Lightlike.PL.PolygonDiagonal2

/-!
# Points of the line through the two neighbours of the corner

Two points `x`, `y` on the line `λ + μ = 1` through `u` and `w`, with `λ` taking the value `0`
and `1` between them, have the points `w` and `u` on the segment between them.
-/

open Set

namespace Lightlike.PL

variable {v u w x y : ℝ × ℝ}

/-- On the line `λ + μ = 1`, the point of the segment `[x, y]` with prescribed `λ` between those
of `x` and `y`. -/
lemma exists_point_on_line (hx : wl v u w x + wm v u w x = 1) (hy : wl v u w y + wm v u w y = 1)
    {τ : ℝ} (hxy : wl v u w x < wl v u w y) (h1 : wl v u w x ≤ τ) (h2 : τ ≤ wl v u w y) :
    ∃ P ∈ segment ℝ x y, wl v u w P = τ ∧ wm v u w P = 1 - τ := by
  set r := (τ - wl v u w x) / (wl v u w y - wl v u w x) with hr
  have hd : 0 < wl v u w y - wl v u w x := by linarith
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hd.le
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hd]; linarith
  refine ⟨(1 - r) • x + r • y, ⟨1 - r, r, by linarith, hr0, by ring, rfl⟩, ?_, ?_⟩
  · rw [Polygon.wl_aff (by ring)]
    rw [hr]; field_simp; ring
  · rw [Polygon.wm_aff (by ring)]
    have e1 : wm v u w x = 1 - wl v u w x := by linarith
    have e2 : wm v u w y = 1 - wl v u w y := by linarith
    rw [e1, e2, hr]; field_simp; ring

/-- **The corners lie on a segment through the diagonal.** If `[x, y]` lies on the line through
`u` and `w`, contains a point strictly between them, and neither end is strictly between them,
then `u` and `w` are on `[x, y]`. -/
lemma corners_mem_segment (hcr : cross (u - v) (w - v) ≠ 0)
    (hx : wl v u w x + wm v u w x = 1) (hy : wl v u w y + wm v u w y = 1)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (hq0 : 0 < wl v u w (s • x + t • y)) (hq1 : wl v u w (s • x + t • y) < 1)
    (hxl : wl v u w x ≤ 0 ∨ 1 ≤ wl v u w x) (hyl : wl v u w y ≤ 0 ∨ 1 ≤ wl v u w y) :
    u ∈ segment ℝ x y ∧ w ∈ segment ℝ x y := by
  have hq : wl v u w (s • x + t • y) = s * wl v u w x + t * wl v u w y := Polygon.wl_aff hst
  have hPw : ∀ P : ℝ × ℝ, wl v u w P = 0 → wm v u w P = 1 → P = w := by
    intro P h0 h1
    have h' : P - v = w - v := by rw [sub_eq_wl_wm hcr P, h0, h1]; simp
    exact sub_left_injective h'
  have hPu : ∀ P : ℝ × ℝ, wl v u w P = 1 → wm v u w P = 0 → P = u := by
    intro P h0 h1
    have h' : P - v = u - v := by rw [sub_eq_wl_wm hcr P, h0, h1]; simp
    exact sub_left_injective h'
  have key : ∀ x y : ℝ × ℝ, wl v u w x + wm v u w x = 1 → wl v u w y + wm v u w y = 1 →
      wl v u w x ≤ 0 → 1 ≤ wl v u w y → u ∈ segment ℝ x y ∧ w ∈ segment ℝ x y := by
    intro x y hx hy h1 h2
    have hxy : wl v u w x < wl v u w y := by linarith
    obtain ⟨P, hP, hP0, hP1⟩ := exists_point_on_line hx hy hxy h1 (by linarith : (0 : ℝ) ≤ wl v u w y)
    obtain ⟨Q, hQ, hQ0, hQ1⟩ := exists_point_on_line hx hy hxy (by linarith : wl v u w x ≤ 1) h2
    refine ⟨?_, ?_⟩
    · have : Q = u := hPu Q hQ0 (by rw [hQ1]; ring)
      rw [← this]; exact hQ
    · have : P = w := hPw P hP0 (by rw [hP1]; ring)
      rw [← this]; exact hP
  rcases hxl with h1 | h1 <;> rcases hyl with h2 | h2
  · exfalso; nlinarith
  · exact key x y hx hy h1 h2
  · have := key y x hy hx h2 h1
    rw [segment_symm]; exact this
  · exfalso; nlinarith

end Lightlike.PL
