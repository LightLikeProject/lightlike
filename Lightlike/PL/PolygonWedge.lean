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


/-- **No edge of a simple polygon meets an empty wedge at the extreme corner.** Let `v = p j` with
neighbours `u` and `w`, and `u - v`, `w - v` not parallel. If no vertex lies in the open wedge
`{λ > 0, μ > 0, λ + μ < c}` with `0 < c ≤ 1`, then the carrier misses the wedge. Here `n ≥ 4`:
for a triangle the edge from `w` to `u` crosses the wedge `c = 1`. -/
theorem wedge_disjoint_carrier (hs : p.IsSimple) (hn : 4 ≤ n) {j : Fin n}
    (hcr : cross (p ((finRotate n).symm j) - p j) (p (finRotate n j) - p j) ≠ 0)
    {c : ℝ} (hc1 : c ≤ 1)
    (hvert : ∀ i, ¬ (0 < wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
      0 < wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) ∧
      wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) +
        wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) (p i) < c))
    {q : ℝ × ℝ} (hq1 : 0 < wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) q)
    (hq2 : 0 < wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) q)
    (hq3 : wl (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) q +
      wm (p j) (p ((finRotate n).symm j)) (p (finRotate n j)) q < c) :
    q ∉ p.carrier := by
  intro hqc
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hqc
  set k := (finRotate n).symm j with hk
  have hkj : finRotate n k = j := by rw [hk]; exact Equiv.apply_symm_apply _ _
  set v := p j with hv
  set u := p k with hu
  set w := p (finRotate n j) with hw
  set x := p e with hx
  set y := p (finRotate n e) with hy
  set f := wf v u w c with hf
  have hfa := wf_affine v u w c
  have hqf : ∀ i, 0 < f i q := by
    intro i
    rcases (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
    · exact hq1
    · exact hq2
    · rw [hf, wf_two]; linarith
  have hnot : ∀ z : ℝ × ℝ, ¬ (0 < wl v u w z ∧ 0 < wm v u w z ∧ wl v u w z + wm v u w z < c) →
      ∃ i, f i z ≤ 0 := by
    intro z hz
    by_contra hcon
    apply hz
    have h0 : 0 < f 0 z := lt_of_not_ge fun h => hcon ⟨0, h⟩
    have h1 : 0 < f 1 z := lt_of_not_ge fun h => hcon ⟨1, h⟩
    have h2 : 0 < f 2 z := lt_of_not_ge fun h => hcon ⟨2, h⟩
    rw [hf, wf_zero] at h0
    rw [hf, wf_one] at h1
    rw [hf, wf_two] at h2
    exact ⟨h0, h1, by linarith⟩
  have hqe := he
  obtain ⟨hxi⟩ : Nonempty (∃ i, f i x ≤ 0) := ⟨hnot x (hvert e)⟩
  obtain ⟨hyi⟩ : Nonempty (∃ i, f i y ≤ 0) := ⟨hnot y (hvert _)⟩
  have heq : p.edge e = segment ℝ x y := rfl
  rw [heq] at he
  obtain ⟨r, hr, hr0, a, hax, har⟩ := exists_boundary_point hfa hqf hxi
  have hyq : q ∈ segment ℝ y x := by rw [segment_symm]; exact he
  obtain ⟨r', hr', hr'0, b, hby, hbr⟩ := exists_boundary_point hfa hqf hyi
  have hrE : r ∈ segment ℝ x y :=
    (convex_segment x y).segment_subset (left_mem_segment ℝ x y) he hr
  have hr'E : r' ∈ segment ℝ x y := by
    rw [segment_symm]
    exact (convex_segment y x).segment_subset (left_mem_segment ℝ y x) hyq hr'
  obtain ⟨s, t, hs0, ht0, hst, hqst⟩ := he
  have hqa : ∀ i, f i q = s * f i x + t * f i y := by
    intro i; rw [← hqst]; exact hfa i x y s t hst
  have key : ∀ i, f i x ≤ 0 → f i y ≤ 0 → False := by
    intro i h1 h2
    have := hqa i
    have := hqf i
    nlinarith [mul_nonneg hs0 (neg_nonneg.2 h1), mul_nonneg ht0 (neg_nonneg.2 h2)]
  -- the edge is neither of the two edges at `v`
  have hej : e ≠ j := by
    intro h
    rw [h] at hqe
    have : q ∈ segment ℝ v w := hqe
    have := wl_of_mem_segment (u := u) this
    linarith
  have hek : e ≠ k := by
    intro h
    rw [h] at hqe
    have h1 : q ∈ segment ℝ u v := by simpa [edge, hkj] using hqe
    rw [segment_symm] at h1
    have := wm_of_mem_segment (w := w) h1
    linarith
  have hedgek : p.edge k = segment ℝ v u := by
    simp only [edge, hkj, hu, hv]; exact segment_symm ℝ _ _
  have hE : ∀ r ∈ p.edge e, (∀ i, 0 ≤ f i r) →
      (f 0 r = 0 → finRotate n j = e ∧ r = x) ∧ (f 1 r = 0 → finRotate n e = k ∧ r = u) := by
    intro r hrE hr0
    have h0 := hr0 0
    have h1 := hr0 1
    have h2 := hr0 2
    rw [hf, wf_zero] at h0
    rw [hf, wf_one] at h1
    rw [hf, wf_two] at h2
    constructor
    · intro hz
      have hz' : wl v u w r = 0 := hz
      have hrj : r ∈ p.edge j := mem_segment_vw hcr hz' h1 (by linarith)
      rcases edge_meet_cases hs hej hrE hrj with ⟨h3, -⟩ | ⟨h3, h4⟩
      · exact absurd ((finRotate n).injective (h3.trans hkj.symm)) hek
      · exact ⟨h3, h4⟩
    · intro hz
      have hz' : wm v u w r = 0 := hz
      have hrk : r ∈ p.edge k := by
        rw [hedgek]; exact mem_segment_vu hcr hz' h0 (by linarith)
      rcases edge_meet_cases hs hek hrE hrk with ⟨h3, h4⟩ | ⟨h3, -⟩
      · exact ⟨h3, h4⟩
      · exact absurd (hkj.symm.trans (h3.trans rfl) |>.symm) hej
  have P0 : finRotate n j = e → x = w := fun h => by rw [hx, ← h]
  have P1 : finRotate n e = k → y = u := fun h => by rw [hy, h]
  have fw0 : x = w → f 0 x ≤ 0 := fun h => by rw [h, hf, wf_zero, wl_w]
  have fw2 : x = w → f 2 x ≤ 0 := fun h => by
    rw [h, hf, wf_two, wl_w, wm_w hcr]; linarith
  have fu1 : y = u → f 1 y ≤ 0 := fun h => by rw [h, hf, wf_one, wm_u]
  have fu2 : y = u → f 2 y ≤ 0 := fun h => by
    rw [h, hf, wf_two, wl_u hcr, wm_u]; linarith
  have hX := hE r hrE hr0
  have hY := hE r' hr'E hr'0
  have h3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases h3 a with rfl | rfl | rfl <;> rcases h3 b with rfl | rfl | rfl
  · exact key 0 hax hby
  · obtain ⟨h1, -⟩ := hX.1 har
    obtain ⟨h2, -⟩ := hY.2 hbr
    have : finRotate n (finRotate n (finRotate n j)) = j := by rw [h1, h2, hkj]
    exact finRotate_three_ne hn j this
  · exact key 2 (fw2 (P0 (hX.1 har).1)) hby
  · exact key 0 (fw0 (P0 (hY.1 hbr).1)) hby
  · exact key 1 hax hby
  · exact key 1 hax (fu1 (P1 (hX.2 har).1))
  · exact key 0 (fw0 (P0 (hY.1 hbr).1)) hby
  · exact key 2 hax (fu2 (P1 (hY.2 hbr).1))
  · exact key 2 hax hby

end Polygon

end Lightlike.PL
