import Mathlib

/-!
# Simple polygons in the plane

The first step towards the Jordan curve and Schoenflies theorems in the plane: simple closed
polygons, their edges and their union.

A polygon with `n` vertices is a map `p : Fin n → ℝ × ℝ`; its edges are the segments from `p i`
to the next vertex `p (finRotate n i)`. It is **simple** when the edges are nondegenerate and two
different edges meet only at a shared endpoint of consecutive edges.

## Main definitions

* `PL.Polygon.edge`: the `i`-th edge.
* `PL.Polygon.carrier`: the union of the edges.
* `PL.Polygon.IsSimple`: the edges are nondegenerate and meet only at consecutive endpoints.
-/

open Set

namespace Lightlike.PL

/-- A closed polygon with `n` vertices in the plane. -/
abbrev Polygon (n : ℕ) := Fin n → ℝ × ℝ

namespace Polygon

variable {n : ℕ} (p : Polygon n)

/-- The `i`-th edge, the segment from `p i` to the next vertex. -/
def edge (i : Fin n) : Set (ℝ × ℝ) := segment ℝ (p i) (p (finRotate n i))

/-- The union of the edges. -/
def carrier : Set (ℝ × ℝ) := ⋃ i, p.edge i

/-- A polygon is **simple** when each edge is nondegenerate, two different edges that are not
consecutive are disjoint, and consecutive edges meet only at their shared vertex. -/
def IsSimple : Prop :=
  (∀ i, p i ≠ p (finRotate n i)) ∧
  (∀ i j, i ≠ j → finRotate n i ≠ j → finRotate n j ≠ i → Disjoint (p.edge i) (p.edge j)) ∧
  (∀ i, p.edge i ∩ p.edge (finRotate n i) = {p (finRotate n i)})

/-- **A simple polygon has at least three vertices.** One vertex has a degenerate edge, and with
two vertices the two edges are the same segment, which meets its neighbour in more than a
vertex; so the hypothesis `[NeZero n]` of the Jordan theorem is the only convention needed. -/
theorem three_le_of_isSimple [NeZero n] (hs : p.IsSimple) : 3 ≤ n := by
  by_contra h
  have hn : n = 1 ∨ n = 2 := by have := NeZero.pos n; omega
  rcases hn with rfl | rfl
  · exact hs.1 0 (by simp)
  · have h3 := hs.2.2 0
    have e0 : finRotate 2 0 = 1 := rfl
    have e1 : finRotate 2 1 = 0 := rfl
    have hmem : p 0 ∈ p.edge 0 ∩ p.edge (finRotate 2 0) := by
      refine ⟨left_mem_segment ℝ _ _, ?_⟩
      simpa [Polygon.edge, e0, e1] using right_mem_segment ℝ (p 1) (p 0)
    rw [h3] at hmem
    have h4 : p 0 = p 1 := by simpa [e0] using Set.mem_singleton_iff.1 hmem
    exact hs.1 0 (by simpa [e0] using h4)

end Polygon

/-! ## Crossings of the horizontal ray -/

/-- The abscissa where the line through `u` and `v` meets the horizontal line at height `h`. -/
noncomputable def xAt (u v : ℝ × ℝ) (h : ℝ) : ℝ :=
  u.1 + (h - u.2) * (v.1 - u.1) / (v.2 - u.2)

/-- The horizontal ray from `x` to the right **crosses** the edge from `u` to `v`, with the
half-open rule at the endpoints (an endpoint counts as above the ray exactly when its height is
greater than that of `x`), so that every vertex is handled uniformly. -/
def CrossesRay (u v x : ℝ × ℝ) : Prop :=
  (u.2 ≤ x.2 ∧ x.2 < v.2 ∨ v.2 ≤ x.2 ∧ x.2 < u.2) ∧ x.1 < xAt u v x.2

/-- At a height reached by the edge `[u, v]` and different at its two ends, the point of the line
at that height is on the segment. -/
lemma mk_xAt_mem_segment {u v : ℝ × ℝ} {h : ℝ} (hne : u.2 ≠ v.2)
    (hh : u.2 ≤ h ∧ h ≤ v.2 ∨ v.2 ≤ h ∧ h ≤ u.2) : (xAt u v h, h) ∈ segment ℝ u v := by
  set t := (h - u.2) / (v.2 - u.2) with ht
  have hd : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht0 : 0 ≤ t := by
    rcases hh with ⟨a, b⟩ | ⟨a, b⟩
    · exact div_nonneg (by linarith) (by linarith [lt_of_le_of_ne (a.trans b) hne])
    · exact div_nonneg_of_nonpos (by linarith) (by linarith [lt_of_le_of_ne (a.trans b) (Ne.symm hne)])
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one_iff]
    rcases hh with ⟨a, b⟩ | ⟨a, b⟩
    · exact .inl ⟨by linarith [lt_of_le_of_ne (a.trans b) hne], by linarith⟩
    · exact .inr (.inr ⟨by linarith [lt_of_le_of_ne (a.trans b) (Ne.symm hne)], by linarith⟩)
  refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, xAt, ht]
    field_simp
    ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ht]
    field_simp
    ring

/-- A point at the height of a horizontal segment and between its ends in abscissa is on it. -/
lemma mk_mem_segment_horizontal {x y : ℝ × ℝ} {c : ℝ} (hxy : x.2 = y.2) (h1 : x.1 < c)
    (h2 : c ≤ y.1) : (c, x.2) ∈ segment ℝ x y := by
  have hd : y.1 - x.1 ≠ 0 := by linarith
  have hpos : 0 < y.1 - x.1 := by linarith
  set t := (c - x.1) / (y.1 - x.1) with ht
  refine ⟨1 - t, t, ?_, ?_, by ring, ?_⟩
  · rw [ht, sub_nonneg, div_le_one hpos]; linarith
  · exact div_nonneg (by linarith) hpos.le
  · ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, ht]
      field_simp
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ← hxy]
      ring

/-- Moving the point along a horizontal segment that misses an edge does not change whether the
ray crosses that edge. -/
lemma crossesRay_congr_horizontal {u v x y : ℝ × ℝ} (hxy : x.2 = y.2)
    (hmiss : Disjoint (segment ℝ x y) (segment ℝ u v)) :
    CrossesRay u v x ↔ CrossesRay u v y := by
  have key : ∀ x y : ℝ × ℝ, x.2 = y.2 → Disjoint (segment ℝ x y) (segment ℝ u v) →
      CrossesRay u v x → CrossesRay u v y := by
    intro x y hxy hmiss ⟨hc, hlt⟩
    refine ⟨by rw [← hxy]; exact hc, ?_⟩
    rw [← hxy]
    by_contra hge
    rw [not_lt] at hge
    have hne : u.2 ≠ v.2 := by rcases hc with ⟨a, b⟩ | ⟨a, b⟩ <;> intro e <;> linarith
    have hmem := mk_xAt_mem_segment hne (h := x.2) (by
      rcases hc with ⟨a, b⟩ | ⟨a, b⟩
      · exact .inl ⟨a, b.le⟩
      · exact .inr ⟨a, b.le⟩)
    exact (Set.disjoint_left.1 hmiss) (mk_mem_segment_horizontal hxy hlt hge) hmem
  exact ⟨key x y hxy hmiss, key y x hxy.symm (by rwa [segment_symm])⟩

/-! ## Local behaviour of one edge -/

open Filter Topology

/-- The crossing condition with the opposite half-open rule at the endpoints: an endpoint counts
as below the ray when its height is strictly less than that of `x`. -/
def CrossesRay' (u v x : ℝ × ℝ) : Prop :=
  (u.2 < x.2 ∧ ¬ v.2 < x.2 ∨ v.2 < x.2 ∧ ¬ u.2 < x.2) ∧ x.1 < xAt u v x.2

/-- Whether a number is at most `y₂`, for `y₂` near `x₂`: the half-open rule of `CrossesRay` for
`y₂ ≥ x₂` and the opposite one for `y₂ < x₂`. -/
lemma eventually_le_side (e : ℝ) (x : ℝ × ℝ) :
    ∀ᶠ y in 𝓝 x, (e ≤ y.2 ↔ if x.2 ≤ y.2 then e ≤ x.2 else e < x.2) := by
  rcases lt_trichotomy e x.2 with h | h | h
  · filter_upwards [continuous_snd.continuousAt.eventually (lt_mem_nhds h)] with y hy
    simp only [hy.le, true_iff]
    split_ifs with hc
    · exact h.le
    · exact h
  · filter_upwards with y
    subst h
    split_ifs with hc <;> simp [hc]
  · filter_upwards [continuous_snd.continuousAt.eventually (gt_mem_nhds h)] with y hy
    have : ¬ e ≤ y.2 := not_le.2 hy
    simp only [this, false_iff]
    split_ifs with hc
    · exact not_le.2 h
    · exact not_lt.2 h.le

/-- Near a point `x` off the edge `[u, v]`, whether the ray from `y` crosses the edge is given by the
rule of `CrossesRay` at `x` when `y` is not below `x`, and by the opposite rule when it is. -/
lemma eventually_crossesRay_side {u v x : ℝ × ℝ} (hx : x ∉ segment ℝ u v) :
    ∀ᶠ y in 𝓝 x, (CrossesRay u v y ↔
      if x.2 ≤ y.2 then CrossesRay u v x else CrossesRay' u v x) := by
  have e1 := eventually_le_side u.2 x
  have e2 := eventually_le_side v.2 x
  have hH : ∀ᶠ y in 𝓝 x, ((u.2 ≤ y.2 ∧ y.2 < v.2 ∨ v.2 ≤ y.2 ∧ y.2 < u.2) ↔
      if x.2 ≤ y.2 then (u.2 ≤ x.2 ∧ x.2 < v.2 ∨ v.2 ≤ x.2 ∧ x.2 < u.2)
      else (u.2 < x.2 ∧ ¬ v.2 < x.2 ∨ v.2 < x.2 ∧ ¬ u.2 < x.2)) := by
    filter_upwards [e1, e2] with y h1 h2
    have : (u.2 ≤ y.2 ∧ y.2 < v.2 ∨ v.2 ≤ y.2 ∧ y.2 < u.2) ↔
        (u.2 ≤ y.2 ∧ ¬ v.2 ≤ y.2 ∨ v.2 ≤ y.2 ∧ ¬ u.2 ≤ y.2) := by simp only [not_le]
    rw [this, h1, h2]
    split_ifs with hc <;> simp only [not_le]
  have key : u.2 ≠ v.2 → (u.2 ≤ x.2 ∧ x.2 ≤ v.2 ∨ v.2 ≤ x.2 ∧ x.2 ≤ u.2) →
      x.1 = xAt u v x.2 → False := fun hne hh he => hx (by
    have := mk_xAt_mem_segment hne hh
    rwa [← he] at this)
  have hA : x.1 = xAt u v x.2 → ¬ (u.2 ≤ x.2 ∧ x.2 < v.2 ∨ v.2 ≤ x.2 ∧ x.2 < u.2) :=
    fun he h => key (by rcases h with ⟨a, b⟩ | ⟨a, b⟩ <;> intro e <;> linarith)
      (by rcases h with ⟨a, b⟩ | ⟨a, b⟩
          · exact .inl ⟨a, b.le⟩
          · exact .inr ⟨a, b.le⟩) he
  have hB : x.1 = xAt u v x.2 → ¬ (u.2 < x.2 ∧ ¬ v.2 < x.2 ∨ v.2 < x.2 ∧ ¬ u.2 < x.2) :=
    fun he h => key (by
        rcases h with ⟨a, b⟩ | ⟨a, b⟩
        · intro e; have := not_lt.1 b; rw [e] at a; linarith
        · intro e; have := not_lt.1 b; rw [← e] at a; linarith)
      (by rcases h with ⟨a, b⟩ | ⟨a, b⟩
          · exact .inl ⟨a.le, not_lt.1 b⟩
          · exact .inr ⟨a.le, not_lt.1 b⟩) he
  by_cases hne : x.1 = xAt u v x.2
  · filter_upwards [hH] with y hy
    unfold CrossesRay CrossesRay'
    rw [hy]
    split_ifs with hc
    · exact ⟨fun h => absurd h.1 (hA hne), fun h => absurd h.1 (hA hne)⟩
    · exact ⟨fun h => absurd h.1 (hB hne), fun h => absurd h.1 (hB hne)⟩
  · by_cases huv : u.2 = v.2
    · filter_upwards [hH] with y hy
      unfold CrossesRay CrossesRay'
      rw [hy]
      split_ifs with hc <;> simp [huv]
    · have hcont : Continuous fun y : ℝ × ℝ => xAt u v y.2 - y.1 := by
        unfold xAt
        have : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
        fun_prop
      have hab : ∀ᶠ y in 𝓝 x, (y.1 < xAt u v y.2 ↔ x.1 < xAt u v x.2) := by
        rcases lt_or_gt_of_ne hne with h | h
        · filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds (sub_pos.2 h))] with y hy
          simp only [h, iff_true]
          linarith
        · filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds (sub_neg.2 h))] with y hy
          have h' : ¬ x.1 < xAt u v x.2 := not_lt.2 h.le
          simp only [h', iff_false, not_lt]
          linarith
      filter_upwards [hH, hab] with y hy hy2
      unfold CrossesRay CrossesRay'
      rw [hy, hy2]
      split_ifs with hc <;> rfl

/-! ## The two half-open rules differ by an even number of crossings -/

open Classical in
/-- The indicator of a proposition in `ZMod 2`. -/
noncomputable def ind (P : Prop) : ZMod 2 := if P then 1 else 0

/-- The vertex `w` lies on the horizontal line of `x`, to its right. -/
def OnRight (w x : ℝ × ℝ) : Prop := w.2 = x.2 ∧ x.1 < w.1

lemma ind_add_self (P : Prop) : ind P + ind P = 0 := by
  unfold ind; split_ifs <;> decide

lemma xAt_left {u v : ℝ × ℝ} {h : ℝ} (e : u.2 = h) : xAt u v h = u.1 := by
  simp [xAt, e]

lemma xAt_right {u v : ℝ × ℝ} {h : ℝ} (hne : u.2 ≠ v.2) (e : v.2 = h) : xAt u v h = v.1 := by
  have : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  rw [xAt, ← e]
  field_simp
  ring

/-- A horizontal edge cannot have exactly one endpoint to the right of a point on its line that is
not on the edge. -/
lemma onRight_horizontal {u v x : ℝ × ℝ} (hx : x ∉ segment ℝ u v) (hu : u.2 = x.2)
    (hv : v.2 = x.2) : (x.1 < u.1 ↔ x.1 < v.1) := by
  by_contra hne
  apply hx
  have hxy : u.2 = v.2 := hu.trans hv.symm
  rcases lt_or_ge x.1 u.1 with h1 | h1
  · have h2 : ¬ x.1 < v.1 := fun h => hne ⟨fun _ => h, fun _ => h1⟩
    rw [not_lt] at h2
    rcases eq_or_lt_of_le h2 with h3 | h3
    · have : x = v := Prod.ext h3.symm hv.symm
      rw [this]; exact right_mem_segment ℝ u v
    · rw [segment_symm]
      have := mk_mem_segment_horizontal (x := v) (y := u) hxy.symm h3 h1.le
      rwa [show x = (x.1, v.2) from Prod.ext rfl hv.symm]
  · have h2 : x.1 < v.1 := by
      by_contra h
      exact hne ⟨fun h' => absurd h' (not_lt.2 h1), fun h' => absurd h' h⟩
    rcases eq_or_lt_of_le h1 with h3 | h3
    · have : x = u := Prod.ext h3.symm hu.symm
      rw [this]; exact left_mem_segment ℝ u v
    · have := mk_mem_segment_horizontal (x := u) (y := v) hxy h3 h2.le
      rwa [show x = (x.1, u.2) from Prod.ext rfl hu.symm]

set_option linter.unusedSimpArgs false in
/-- For one edge off `x`, the two half-open rules differ exactly at the endpoints that lie on the
line of `x`, to its right. -/
lemma ind_crossesRay_add {u v x : ℝ × ℝ} (hx : x ∉ segment ℝ u v) :
    ind (CrossesRay u v x) + ind (CrossesRay' u v x) = ind (OnRight u x) + ind (OnRight v x) := by
  unfold ind CrossesRay CrossesRay' OnRight
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases lt_trichotomy u.2 x.2 with hu | hu | hu <;>
    rcases lt_trichotomy v.2 x.2 with hv | hv | hv <;>
    by_cases hA : x.1 < xAt u v x.2
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · have hne : u.2 ≠ v.2 := fun e => by rw [e, hv] at hu; exact lt_irrefl _ hu
    have hxa := xAt_right hne hv
    simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.le, hv.ge, hA, h11, hxa]
  · have hne : u.2 ≠ v.2 := fun e => by rw [e, hv] at hu; exact lt_irrefl _ hu
    have hxa := xAt_right hne hv
    simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.le, hv.ge, hA, h11, hxa]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · have hne : u.2 ≠ v.2 := fun e => by rw [← e, hu] at hv; exact lt_irrefl _ hv
    have hxa := xAt_left (v := v) hu
    simp [hu, hu.le, hu.ge, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11, hxa]
  · have hne : u.2 ≠ v.2 := fun e => by rw [← e, hu] at hv; exact lt_irrefl _ hv
    have hxa := xAt_left (v := v) hu
    simp [hu, hu.le, hu.ge, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11, hxa]
  · have hh := onRight_horizontal hx hu hv
    by_cases hB : x.1 < v.1 <;> simp [hu, hv, hh, hB, h11]
  · have hh := onRight_horizontal hx hu hv
    by_cases hB : x.1 < v.1 <;> simp [hu, hv, hh, hB, h11]
  · have hne : u.2 ≠ v.2 := fun e => by rw [← e, hu] at hv; exact lt_irrefl _ hv
    have hxa := xAt_left (v := v) hu
    simp [hu, hu.le, hu.ge, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11, hxa]
  · have hne : u.2 ≠ v.2 := fun e => by rw [← e, hu] at hv; exact lt_irrefl _ hv
    have hxa := xAt_left (v := v) hu
    simp [hu, hu.le, hu.ge, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11, hxa]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · have hne : u.2 ≠ v.2 := fun e => by rw [e, hv] at hu; exact lt_irrefl _ hu
    have hxa := xAt_right hne hv
    simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.le, hv.ge, hA, h11, hxa]
  · have hne : u.2 ≠ v.2 := fun e => by rw [e, hv] at hu; exact lt_irrefl _ hu
    have hxa := xAt_right hne hv
    simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.le, hv.ge, hA, h11, hxa]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]
  · simp [hu, hu.ne, hu.ne', hu.le, not_le.2 hu, not_lt.2 hu.le, hv, hv.ne, hv.ne', hv.le, not_le.2 hv, not_lt.2 hv.le, hA, h11]

/-! ## The parity of the crossings of a polygon -/

namespace Polygon

variable {n : ℕ} (p : Polygon n)

/-- The parity of the number of edges crossed by the horizontal ray to the right of `x`. -/
noncomputable def parity (x : ℝ × ℝ) : ZMod 2 :=
  ∑ i, ind (CrossesRay (p i) (p (finRotate n i)) x)

/-- The same parity with the opposite half-open rule at the endpoints. -/
noncomputable def parity' (x : ℝ × ℝ) : ZMod 2 :=
  ∑ i, ind (CrossesRay' (p i) (p (finRotate n i)) x)

lemma ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  rw [propext h]

/-- Off the polygon, the two half-open rules give the same parity: the endpoints on the line of
`x` to its right come in pairs around the polygon. -/
lemma parity_add_parity' {x : ℝ × ℝ} (hx : x ∉ p.carrier) : p.parity x + p.parity' x = 0 := by
  have hxe : ∀ i, x ∉ segment ℝ (p i) (p (finRotate n i)) := fun i h =>
    hx (Set.mem_iUnion.2 ⟨i, h⟩)
  unfold parity parity'
  rw [← Finset.sum_add_distrib]
  simp_rw [ind_crossesRay_add (hxe _)]
  rw [Finset.sum_add_distrib]
  have : ∑ i, ind (OnRight (p (finRotate n i)) x) = ∑ i, ind (OnRight (p i) x) :=
    Equiv.sum_comp (finRotate n) fun i => ind (OnRight (p i) x)
  rw [this]
  exact CharTwo.add_self_eq_zero _

/-- **The parity is locally constant off the polygon.** -/
theorem eventually_parity_eq {x : ℝ × ℝ} (hx : x ∉ p.carrier) :
    ∀ᶠ y in 𝓝 x, p.parity y = p.parity x := by
  have hxe : ∀ i, x ∉ segment ℝ (p i) (p (finRotate n i)) := fun i h =>
    hx (Set.mem_iUnion.2 ⟨i, h⟩)
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, (CrossesRay (p i) (p (finRotate n i)) y ↔
      if x.2 ≤ y.2 then CrossesRay (p i) (p (finRotate n i)) x
      else CrossesRay' (p i) (p (finRotate n i)) x) :=
    Filter.eventually_all.2 fun i => eventually_crossesRay_side (hxe i)
  have h2 : p.parity' x = p.parity x := by
    have := p.parity_add_parity' hx
    exact (CharTwo.add_eq_zero.1 this).symm
  filter_upwards [hall] with y hy
  unfold parity
  split_ifs at hy with hc
  · exact Finset.sum_congr rfl fun i _ => ind_congr ((hy i).trans (by simp [hc]))
  · refine (?_ : _ = p.parity' x).trans h2
    exact Finset.sum_congr rfl fun i _ => ind_congr ((hy i).trans (by simp [hc]))

end Polygon
end Lightlike.PL
