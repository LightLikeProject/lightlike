import Lightlike.PL.PolygonDiagonal
import Lightlike.PL.WedgeChord

/-!
# Barycentric coordinates at a corner, and wedges

For three points `v`, `u`, `w` of the plane with `u - v` and `w - v` not parallel, every point `x`
is `v + λ (u - v) + μ (w - v)`. The functions `λ`, `μ` and `c - λ - μ` are affine; the open
wedge `{λ > 0, μ > 0, λ + μ < c}` is the interior of the triangle with corner `v` cut by the
line `λ + μ = c`.

## Main definitions

* `Lightlike.PL.wl`, `Lightlike.PL.wm`: the two barycentric coordinates
* `Lightlike.PL.wf`: the three affine functions that define the wedge
-/

open Set

namespace Lightlike.PL

/-- The coordinate along `u - v` of `x` in the frame `(v; u - v, w - v)`. -/
noncomputable def wl (v u w x : ℝ × ℝ) : ℝ := cross (x - v) (w - v) / cross (u - v) (w - v)

/-- The coordinate along `w - v` of `x` in the frame `(v; u - v, w - v)`. -/
noncomputable def wm (v u w x : ℝ × ℝ) : ℝ := cross (u - v) (x - v) / cross (u - v) (w - v)

/-- The three affine functions whose common positivity is the wedge of height `c`. -/
noncomputable def wf (v u w : ℝ × ℝ) (c : ℝ) : Fin 3 → ℝ × ℝ → ℝ
  | 0 => fun x => wl v u w x
  | 1 => fun x => wm v u w x
  | 2 => fun x => c - wl v u w x - wm v u w x

lemma wf_zero (v u w : ℝ × ℝ) (c : ℝ) (x : ℝ × ℝ) : wf v u w c 0 x = wl v u w x := rfl
lemma wf_one (v u w : ℝ × ℝ) (c : ℝ) (x : ℝ × ℝ) : wf v u w c 1 x = wm v u w x := rfl
lemma wf_two (v u w : ℝ × ℝ) (c : ℝ) (x : ℝ × ℝ) :
    wf v u w c 2 x = c - wl v u w x - wm v u w x := rfl

/-- The three functions are affine. -/
lemma wf_affine (v u w : ℝ × ℝ) (c : ℝ) (i : Fin 3) (x y : ℝ × ℝ) (s t : ℝ) (hst : s + t = 1) :
    wf v u w c i (s • x + t • y) = s * wf v u w c i x + t * wf v u w c i y := by
  obtain rfl : s = 1 - t := by linarith
  have hl : wl v u w ((1 - t) • x + t • y) = (1 - t) * wl v u w x + t * wl v u w y := by
    unfold wl cross; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hm : wm v u w ((1 - t) • x + t • y) = (1 - t) * wm v u w x + t * wm v u w y := by
    unfold wm cross; simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  fin_cases i
  · simp only [Fin.zero_eta, wf_zero]; exact hl
  · simp only [Fin.mk_one, wf_one]; exact hm
  · show c - wl v u w _ - wm v u w _ = _
    rw [hl, hm]; show _ = (1 - t) * (c - wl v u w x - wm v u w x) + t * (c - wl v u w y - wm v u w y)
    ring

variable {v u w : ℝ × ℝ}

/-- Every point is `v` plus its two coordinates times the two edge vectors. -/
lemma sub_eq_wl_wm (h : cross (u - v) (w - v) ≠ 0) (x : ℝ × ℝ) :
    x - v = wl v u w x • (u - v) + wm v u w x • (w - v) := by
  unfold wl wm
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    unfold cross; simp only [Prod.fst_sub, Prod.snd_sub]; ring

lemma wl_w : wl v u w w = 0 := by
  unfold wl
  have : cross (w - v) (w - v) = 0 := by unfold cross; ring
  rw [this, zero_div]

lemma wm_w (h : cross (u - v) (w - v) ≠ 0) : wm v u w w = 1 := by
  unfold wm; exact div_self h

lemma wl_u (h : cross (u - v) (w - v) ≠ 0) : wl v u w u = 1 := by
  unfold wl; exact div_self h

lemma wm_u : wm v u w u = 0 := by
  unfold wm
  have : cross (u - v) (u - v) = 0 := by unfold cross; ring
  rw [this, zero_div]

/-- On the segment from `v` to `w` the first coordinate vanishes. -/
lemma wl_of_mem_segment {x : ℝ × ℝ} (hx : x ∈ segment ℝ v w) : wl v u w x = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  obtain rfl : a = 1 - b := by linarith
  unfold wl cross
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  have : ((1 - b) * v.1 + b * w.1 - v.1) * (w.2 - v.2) - ((1 - b) * v.2 + b * w.2 - v.2) *
      (w.1 - v.1) = 0 := by ring
  rw [this, zero_div]

/-- On the segment from `v` to `u` the second coordinate vanishes. -/
lemma wm_of_mem_segment {x : ℝ × ℝ} (hx : x ∈ segment ℝ v u) : wm v u w x = 0 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hx
  obtain rfl : a = 1 - b := by linarith
  unfold wm cross
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  have : (u.1 - v.1) * ((1 - b) * v.2 + b * u.2 - v.2) - (u.2 - v.2) *
      ((1 - b) * v.1 + b * u.1 - v.1) = 0 := by ring
  rw [this, zero_div]

/-- A point with vanishing first coordinate and second coordinate in `[0,1]` is on the segment
from `v` to `w`. -/
lemma mem_segment_vw (h : cross (u - v) (w - v) ≠ 0) {x : ℝ × ℝ} (h0 : wl v u w x = 0)
    (hm0 : 0 ≤ wm v u w x) (hm1 : wm v u w x ≤ 1) : x ∈ segment ℝ v w := by
  refine Polygon.mem_segment_of_sub_eq hm0 hm1 ?_
  rw [sub_eq_wl_wm h x, h0, zero_smul, zero_add]

/-- A point with vanishing second coordinate and first coordinate in `[0,1]` is on the segment
from `v` to `u`. -/
lemma mem_segment_vu (h : cross (u - v) (w - v) ≠ 0) {x : ℝ × ℝ} (h0 : wm v u w x = 0)
    (hl0 : 0 ≤ wl v u w x) (hl1 : wl v u w x ≤ 1) : x ∈ segment ℝ v u := by
  refine Polygon.mem_segment_of_sub_eq hl0 hl1 ?_
  rw [sub_eq_wl_wm h x, h0, zero_smul, add_zero]


namespace Polygon

variable {n : ℕ} {p : Polygon n}

/-- **Two edges of a simple polygon meet only at a shared vertex.** If two different edges
`i`, `j` have a common point `x`, then `j` follows `i` and `x` is the vertex between them, or `i`
follows `j` and `x` is the vertex between them. -/
lemma edge_meet_cases (hs : p.IsSimple) {i j : Fin n} (hij : i ≠ j) {x : ℝ × ℝ}
    (hi : x ∈ p.edge i) (hj : x ∈ p.edge j) :
    (finRotate n i = j ∧ x = p j) ∨ (finRotate n j = i ∧ x = p i) := by
  by_cases h1 : finRotate n i = j
  · left
    refine ⟨h1, ?_⟩
    have := hs.2.2 i
    rw [h1] at this
    have hx : x ∈ p.edge i ∩ p.edge j := ⟨hi, hj⟩
    rw [this] at hx
    exact hx
  · by_cases h2 : finRotate n j = i
    · right
      refine ⟨h2, ?_⟩
      have := hs.2.2 j
      rw [h2] at this
      have hx : x ∈ p.edge j ∩ p.edge i := ⟨hj, hi⟩
      rw [this] at hx
      exact hx
    · exact (Set.disjoint_left.1 (hs.2.1 i j hij h1 h2) hi hj).elim

/-- Three steps of the cyclic rotation on `n ≥ 4` points move every point. -/
lemma finRotate_three_ne (hn : 4 ≤ n) (j : Fin n) :
    finRotate n (finRotate n (finRotate n j)) ≠ j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  simp only [finRotate_apply] at h
  have h3 : j + 1 + 1 + 1 = j + 0 := by simpa using h
  have h5 : j + (1 + 1 + 1) = j + 0 := by rw [← add_assoc, ← add_assoc]; exact h3
  have h6 := add_left_cancel h5
  have h7 := congrArg Fin.val h6
  have h1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt (show 1 < m + 1 by omega)]
  have h0 : ((0 : Fin (m + 1)) : ℕ) = 0 := rfl
  rw [Fin.val_add, Fin.val_add, h1, h0] at h7
  rw [Nat.mod_eq_of_lt (show 1 + 1 < m + 1 by omega)] at h7
  rw [Nat.mod_eq_of_lt (show 1 + 1 + 1 < m + 1 by omega)] at h7
  omega

end Polygon

end Lightlike.PL
