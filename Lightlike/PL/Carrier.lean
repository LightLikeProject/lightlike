import Lightlike.PL.Realisation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Open simplices and carriers

For a finite set `s` of points of a real vector space, `openHull s` is the **open simplex**: the
convex combinations of the points of `s` in which every point has positive weight. When `s` is
affinely independent the weights of a point are unique, so the open simplices of the faces of `s`
partition its convex hull. In a geometric complex `K` this gives every point `x` of `|K|` a
unique face whose open simplex contains it, the **carrier** of `x` (Rourke–Sanderson,
*Introduction to piecewise-linear topology*, ch. 2; Lickorish, *Simplicial moves on complexes and
manifolds*, §2).

## Main results

* `eq_of_mem_openHull`: two faces of an affinely independent set whose open simplices meet are
  equal.
* `notMem_affineSpan_of_mem_openHull`: a point of the open simplex of `s` is not in the affine
  span of a proper subset of `s`.
* `SComplex.IsGeom.existsUnique_carrier`: in a geometric complex every point of the underlying set
  lies in the open simplex of exactly one face.
* `exists_exit`: the ray from a point of the open simplex through another point of the simplex
  leaves the simplex at a point of its boundary.
-/

open Finset

namespace Lightlike.PL

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-! ## Open simplices -/

/-- The **open simplex** spanned by `s`: the convex combinations of the points of `s` in which
every point has positive weight. -/
def openHull (s : Finset E) : Set E :=
  {x | ∃ w : E → ℝ, (∀ y ∈ s, 0 < w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x}

lemma openHull_subset_convexHull (s : Finset E) : openHull s ⊆ convexHull ℝ (s : Set E) := by
  rintro x ⟨w, hw, h1, rfl⟩
  exact Finset.mem_convexHull'.2 ⟨w, fun y hy => (hw y hy).le, h1, rfl⟩

/-- The open simplex of the empty set is empty. -/
@[simp] lemma openHull_empty : openHull (∅ : Finset E) = ∅ := by
  ext x
  simp [openHull]

lemma nonempty_of_mem_openHull {s : Finset E} {x : E} (hx : x ∈ openHull s) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp at hx

/-- A vertex lies in its own open simplex. -/
lemma mem_openHull_singleton (y : E) : y ∈ openHull ({y} : Finset E) :=
  ⟨fun _ => 1, by simp, by simp, by simp⟩

/-- Every point of a closed simplex lies in the open simplex of one of its faces: the points
with positive weight. -/
lemma exists_openHull_of_mem_convexHull {s : Finset E} {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : ∃ t ⊆ s, x ∈ openHull t := by
  classical
  obtain ⟨w, hw0, hw1, rfl⟩ := Finset.mem_convexHull'.1 hx
  have hpos : ∀ y ∈ s, w y ≠ 0 → 0 < w y := fun y hy hne => lt_of_le_of_ne (hw0 y hy) hne.symm
  refine ⟨s.filter (fun y => 0 < w y), filter_subset _ _, w, fun y hy => (mem_filter.1 hy).2,
    ?_, ?_⟩
  · rw [sum_filter_of_ne hpos, hw1]
  · rw [sum_filter_of_ne fun y hy hne => hpos y hy (left_ne_zero_of_smul hne)]

/-- Extending weights on `t ⊆ s` by zero does not change the weighted sums. -/
lemma sum_extend_zero [DecidableEq E] {s t : Finset E} (hts : t ⊆ s) (u : E → ℝ) :
    (∑ y ∈ s, (if y ∈ t then u y else 0)) = ∑ y ∈ t, u y ∧
      (∑ y ∈ s, (if y ∈ t then u y else 0) • y) = ∑ y ∈ t, u y • y := by
  constructor
  · rw [sum_ite_mem, inter_eq_right.2 hts]
  · simp_rw [ite_smul, zero_smul]
    rw [sum_ite_mem, inter_eq_right.2 hts]

/-- **The key uniqueness fact.** If `x` is in the open simplex of an affinely independent `s` and
`x` is an affine combination of the points of `t ⊆ s` (weights of any sign), then `t = s`. -/
lemma subset_of_mem_openHull {s t : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (hts : t ⊆ s) {x : E} (hx : x ∈ openHull s) {u : E → ℝ} (hu1 : ∑ y ∈ t, u y = 1)
    (hux : ∑ y ∈ t, u y • y = x) : s ⊆ t := by
  classical
  obtain ⟨w, hw, hw1, rfl⟩ := hx
  obtain ⟨he1, hex⟩ := sum_extend_zero hts u
  intro y hy
  by_contra hyt
  have key := hs.eq_of_sum_eq_sum_subtype (w₁ := w) (w₂ := fun z => if z ∈ t then u z else 0)
    (by rw [hw1, he1, hu1]) (by rw [hex, hux]) y hy
  simp only [hyt, ↓reduceIte] at key
  exact (hw y hy).ne' key

/-- Two faces of an affinely independent set whose open simplices meet are equal. -/
lemma eq_of_mem_openHull {s t u : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : t ⊆ s) (hu : u ⊆ s) {x : E} (hxt : x ∈ openHull t) (hxu : x ∈ openHull u) : t = u := by
  classical
  obtain ⟨w, hw, hw1, hwx⟩ := hxt
  obtain ⟨v, hv, hv1, hvx⟩ := hxu
  obtain ⟨he1, hex⟩ := sum_extend_zero ht w
  obtain ⟨hf1, hfx⟩ := sum_extend_zero hu v
  have key := hs.eq_of_sum_eq_sum_subtype (w₁ := fun z => if z ∈ t then w z else 0)
    (w₂ := fun z => if z ∈ u then v z else 0) (by rw [he1, hf1, hw1, hv1])
    (by rw [hex, hfx, hwx, hvx])
  ext y
  constructor
  · intro hy
    have := key y (ht hy)
    simp only [hy, ↓reduceIte] at this
    by_contra hyu
    simp only [hyu, ↓reduceIte] at this
    exact (hw y hy).ne' this
  · intro hy
    have := key y (hu hy)
    simp only [hy, ↓reduceIte] at this
    by_contra hyt
    simp only [hyt, ↓reduceIte] at this
    exact (hv y hy).ne' this.symm

/-- A point of the open simplex of an affinely independent `s` does not lie in the closed simplex
of a proper subset of `s`. -/
lemma notMem_convexHull_of_mem_openHull {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s) (hne : t ≠ s) {x : E}
    (hx : x ∈ openHull s) : x ∉ convexHull ℝ (t : Set E) := by
  intro hxt
  obtain ⟨u, hu1, hu, hux⟩ := Finset.mem_convexHull'.1 hxt
  exact hne (hts.antisymm (subset_of_mem_openHull hs hts hx hu (hux)))

/-- Affine combinations of a finite set, as weights on that set. -/
lemma exists_weights_of_mem_affineSpan {t : Finset E} {x : E}
    (hx : x ∈ affineSpan ℝ (t : Set E)) :
    ∃ u : E → ℝ, ∑ y ∈ t, u y = 1 ∧ ∑ y ∈ t, u y • y = x := by
  classical
  have hx' : x ∈ affineSpan ℝ (id '' (t : Set E)) := by rwa [Set.image_id]
  rw [Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype] at hx'
  obtain ⟨fs, hfs, u, hu1, rfl⟩ := hx'
  have hfs' : fs ⊆ t := fun y hy => hfs (mem_coe.2 hy)
  obtain ⟨he1, hex⟩ := sum_extend_zero hfs' u
  refine ⟨fun y => if y ∈ fs then u y else 0, he1.trans hu1, ?_⟩
  rw [hex, fs.affineCombination_eq_linear_combination _ _ hu1]
  rfl

/-- A point of the open simplex of an affinely independent `s` is not in the affine span of a
proper subset of `s`. -/
lemma notMem_affineSpan_of_mem_openHull {s t : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hts : t ⊆ s) (hne : t ≠ s) {x : E}
    (hx : x ∈ openHull s) : x ∉ affineSpan ℝ (t : Set E) := by
  intro hxt
  obtain ⟨u, hu1, hux⟩ := exists_weights_of_mem_affineSpan hxt
  exact hne (hts.antisymm (subset_of_mem_openHull hs hts hx hu1 hux))

/-- A convex combination with positive weight on a point of the open simplex and the rest in the
closed simplex lies in the open simplex. -/
lemma combo_mem_openHull {s : Finset E} {b y : E} (hb : b ∈ openHull s)
    (hy : y ∈ convexHull ℝ (s : Set E)) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    l • b + (1 - l) • y ∈ openHull s := by
  obtain ⟨w, hw, hw1, rfl⟩ := hb
  obtain ⟨v, hv, hv1, rfl⟩ := Finset.mem_convexHull'.1 hy
  refine ⟨fun z => l * w z + (1 - l) * v z, fun z hz => ?_, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg (mul_pos hl0 (hw z hz))
      (mul_nonneg (sub_nonneg.2 hl1) (hv z hz))
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw1, hv1]
    ring
  · simp only [add_smul, mul_smul, sum_add_distrib, ← smul_sum]

/-- **The ray leaves the simplex.** For `b` in the open simplex of an affinely independent `s`
and `x ≠ b` in its closed simplex, the ray from `b` through `x` meets the boundary: for some
`t ≥ 1` the point `b + t • (x - b)` is in the closed simplex but not in the open one. -/
lemma exists_exit {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {b x : E}
    (hb : b ∈ openHull s) (hx : x ∈ convexHull ℝ (s : Set E)) (hne : x ≠ b) :
    ∃ t : ℝ, 1 ≤ t ∧ b + t • (x - b) ∈ convexHull ℝ (s : Set E) ∧
      b + t • (x - b) ∉ openHull s := by
  classical
  obtain ⟨wb, hwb, hwb1, rfl⟩ := hb
  obtain ⟨wx, hwx, hwx1, rfl⟩ := Finset.mem_convexHull'.1 hx
  set D := s.filter fun y => wx y < wb y with hD
  have hDne : D.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have hle : ∀ y ∈ s, wb y ≤ wx y := fun y hy => by
      by_contra hlt
      have : y ∈ D := mem_filter.2 ⟨hy, lt_of_not_ge hlt⟩
      rw [h] at this
      exact notMem_empty y this
    have heq := (sum_eq_sum_iff_of_le hle).1 (hwb1.trans hwx1.symm)
    exact hne (sum_congr rfl fun y hy => by rw [heq y hy]).symm
  obtain ⟨y₀, hy₀, hmin⟩ := exists_min_image D (fun y => wb y / (wb y - wx y)) hDne
  obtain ⟨hy₀s, hy₀lt⟩ := mem_filter.1 hy₀
  set t := wb y₀ / (wb y₀ - wx y₀) with ht
  have hpos₀ : 0 < wb y₀ - wx y₀ := sub_pos.2 hy₀lt
  have ht1 : 1 ≤ t := (one_le_div hpos₀).2 (by linarith [hwx y₀ hy₀s])
  -- the weights of the exit point
  set c : E → ℝ := fun y => wb y + t * (wx y - wb y) with hc
  have hpt : (∑ y ∈ s, wb y • y) + t • ((∑ y ∈ s, wx y • y) - ∑ y ∈ s, wb y • y) =
      ∑ y ∈ s, c y • y := by
    simp only [hc, add_smul, mul_smul, sub_smul, sum_add_distrib, sum_sub_distrib, smul_sum,
      smul_sub]
  have hc1 : ∑ y ∈ s, c y = 1 := by
    simp only [hc, sum_add_distrib, ← mul_sum, sum_sub_distrib, hwb1, hwx1]
    ring
  have hc0 : ∀ y ∈ s, 0 ≤ c y := fun y hy => by
    by_cases hyD : wx y < wb y
    · have hle : t ≤ wb y / (wb y - wx y) := hmin y (mem_filter.2 ⟨hy, hyD⟩)
      have hp : 0 < wb y - wx y := sub_pos.2 hyD
      rw [le_div_iff₀ hp] at hle
      simp only [hc]
      nlinarith
    · simp only [hc]
      have : 0 ≤ wx y - wb y := by linarith [le_of_not_gt hyD]
      nlinarith [hwb y hy]
  have hcy₀ : c y₀ = 0 := by
    simp only [hc, ht]
    field_simp
    ring
  refine ⟨t, ht1, ?_, ?_⟩
  · rw [hpt]
    exact Finset.mem_convexHull'.2 ⟨c, hc0, hc1, rfl⟩
  · rintro ⟨w', hw', hw'1, hw'x⟩
    rw [hpt] at hw'x
    have := hs.eq_of_sum_eq_sum_subtype (w₁ := w') (w₂ := c) (hw'1.trans hc1.symm) hw'x y₀ hy₀s
    exact (hw' y₀ hy₀s).ne' (this.trans hcy₀)

/-! ## Carriers in a geometric complex -/

namespace SComplex

/-- Every point of the closed simplex of a face lies in the open simplex of a subface. -/
lemma exists_face_openHull {K : SComplex E} {s : Finset E} (hs : s ∈ K) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : ∃ t ∈ K, t ⊆ s ∧ x ∈ openHull t := by
  obtain ⟨t, hts, ht⟩ := exists_openHull_of_mem_convexHull hx
  exact ⟨t, down_mem hs hts, hts, ht⟩

/-- Every point of the underlying set lies in the open simplex of some face. -/
lemma exists_carrier {K : SComplex E} {x : E} (hx : x ∈ K.space) :
    ∃ s ∈ K, x ∈ openHull s := by
  obtain ⟨s, hs, hxs⟩ := mem_space.1 hx
  obtain ⟨t, ht, -, hxt⟩ := exists_face_openHull hs hxs
  exact ⟨t, ht, hxt⟩

/-- **Carriers are unique**: in a geometric complex, the open simplices of distinct faces are
disjoint. -/
lemma IsGeom.eq_of_mem_openHull {K : SComplex E} (hK : IsGeom K) {s t : Finset E} (hs : s ∈ K)
    (ht : t ∈ K) {x : E} (hxs : x ∈ openHull s) (hxt : x ∈ openHull t) : s = t := by
  classical
  have hx : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [coe_inter]
    exact hK.inter s hs t ht ⟨openHull_subset_convexHull _ hxs, openHull_subset_convexHull _ hxt⟩
  obtain ⟨u, hu, hxu⟩ := exists_openHull_of_mem_convexHull hx
  have h₁ : u = s :=
    Lightlike.PL.eq_of_mem_openHull (hK.indep s hs) (hu.trans inter_subset_left) subset_rfl hxu hxs
  have h₂ : u = t :=
    Lightlike.PL.eq_of_mem_openHull (hK.indep t ht) (hu.trans inter_subset_right) subset_rfl hxu hxt
  exact h₁.symm.trans h₂

/-- In a geometric complex every point of the underlying set lies in the open simplex of exactly
one face, its **carrier**. -/
theorem IsGeom.existsUnique_carrier {K : SComplex E} (hK : IsGeom K) {x : E} (hx : x ∈ K.space) :
    ∃! s, s ∈ K ∧ x ∈ openHull s := by
  obtain ⟨s, hs, hxs⟩ := exists_carrier hx
  exact ⟨s, ⟨hs, hxs⟩, fun t ⟨ht, hxt⟩ => hK.eq_of_mem_openHull ht hs hxt hxs⟩

/-- The carrier of a point of a closed simplex is a face of that simplex. -/
lemma IsGeom.subset_of_mem_openHull {K : SComplex E} (hK : IsGeom K) {s t : Finset E}
    (hs : s ∈ K) (ht : t ∈ K) {x : E} (hxs : x ∈ convexHull ℝ (s : Set E))
    (hxt : x ∈ openHull t) : t ⊆ s := by
  obtain ⟨u, hu, hus, hxu⟩ := exists_face_openHull hs hxs
  rw [← hK.eq_of_mem_openHull hu ht hxu hxt]
  exact hus

end SComplex

end Lightlike.PL
