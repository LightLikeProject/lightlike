import Lightlike.Regge.Complex

/-!
# The manifold condition at edges

`Lightlike/Regge/Complex.lean` classifies edges combinatorially: an edge is a boundary edge if it
lies in a triangle contained in only one tetrahedron, and interior otherwise. On an arbitrary
complex this classification has no geometric meaning (three tetrahedra may share a triangle, say).
This file adds the condition under which it does.

In a triangulated 3-manifold the tetrahedra around an interior edge `ab` form a ring: their
vertices other than `a, b` form a cycle `w 0, w 1, …, w (n-1), w n = w 0`, the **link** of the edge,
and the tetrahedra are `{a, b, w i, w (i+1)}`. Around a boundary edge they form a fan whose link is
a path `w 0, …, w n`.

## Main results

* `IsCycleLink K a b n w`: the link of `{a, b}` is a cycle of length `n ≥ 3`.
* `IsPathLink K a b n w`: the link of `{a, b}` is a path with `n ≥ 1` edges.
* `IsEdgeManifold K`: the link of every edge is a cycle or a path. This is the part of the
  combinatorial manifold condition that Regge calculus uses (curvature sits on edges); the full
  condition would also ask the links of vertices to be spheres or discs.

* `IsCycleLink.mem_intEdges`, `IsPathLink.mem_bdryEdges`: an edge with a cycle link is interior and
  an edge with a path link is a boundary edge.
* `IsEdgeManifold.mem_intEdges_iff`, `IsEdgeManifold.mem_bdryEdges_iff`: on an edge-manifold the
  combinatorial classification of `Lightlike/Regge/Complex.lean` is exactly cycle links versus path
  links.
* `IsCycleLink.angleSum_eq`: around an edge with a cycle link, the angle sum runs once over the
  ring of tetrahedra.
-/

open Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3)

variable {V : Type*} [DecidableEq V]

/-- The successor of `i` in the cycle `0 → 1 → ⋯ → n - 1 → 0`. -/
def cycSucc (n i : ℕ) : ℕ := if i + 1 < n then i + 1 else 0

/-- The successor stays in the cycle. -/
theorem cycSucc_lt {n i : ℕ} (hn : 0 < n) : cycSucc n i < n := by
  unfold cycSucc
  split_ifs <;> omega

/-- The link of the edge `{a, b}` in `K` is a cycle of length `n ≥ 3`: the tetrahedra of `K`
containing `{a, b}` are exactly `{a, b, w i, w (i+1)}` for `i < n`, where `w 0, …, w (n-1)` are
distinct vertices other than `a` and `b`, and `w n = w 0`. -/
structure IsCycleLink (K : Complex3 V) (a b : V) (n : ℕ) (w : ℕ → V) : Prop where
  ne : a ≠ b
  three_le : 3 ≤ n
  ne_a : ∀ i < n, w i ≠ a
  ne_b : ∀ i < n, w i ≠ b
  inj : Set.InjOn w (range n)
  closed : w n = w 0
  star_eq : star K {a, b} = (range n).image fun i => {a, b, w i, w (i + 1)}

/-- The link of the edge `{a, b}` in `K` is a path with `n ≥ 1` edges: the tetrahedra of `K`
containing `{a, b}` are exactly `{a, b, w i, w (i+1)}` for `i < n`, where `w 0, …, w n` are
distinct vertices other than `a` and `b`. -/
structure IsPathLink (K : Complex3 V) (a b : V) (n : ℕ) (w : ℕ → V) : Prop where
  ne : a ≠ b
  one_le : 1 ≤ n
  ne_a : ∀ i ≤ n, w i ≠ a
  ne_b : ∀ i ≤ n, w i ≠ b
  inj : Set.InjOn w (range (n + 1))
  star_eq : star K {a, b} = (range n).image fun i => {a, b, w i, w (i + 1)}

/-- `K` is an **edge-manifold**: the link of every edge is a cycle (interior edge) or a path
(boundary edge). -/
def IsEdgeManifold (K : Complex3 V) : Prop :=
  ∀ e ∈ K.edges, ∃ a b n w, e = {a, b} ∧ (IsCycleLink K a b n w ∨ IsPathLink K a b n w)

namespace IsCycleLink

variable {K : Complex3 V} {a b : V} {n : ℕ} {w : ℕ → V}

/-- In a cycle link, `w (i+1)` is the link vertex with index `cycSucc n i`. -/
theorem w_succ (h : IsCycleLink K a b n w) {i : ℕ} (hi : i < n) :
    w (i + 1) = w (cycSucc n i) := by
  unfold cycSucc
  split_ifs with h1
  · rfl
  · rw [show i + 1 = n by omega, h.closed]

/-- The link vertices `w 0, …, w (n-1)` are distinct. -/
theorem w_inj (h : IsCycleLink K a b n w) {i j : ℕ} (hi : i < n) (hj : j < n) (hw : w i = w j) :
    i = j :=
  h.inj (by simpa using hi) (by simpa using hj) hw

/-- The `n` tetrahedra around the edge are distinct. -/
theorem injOn_tet (h : IsCycleLink K a b n w) :
    Set.InjOn (fun i => ({a, b, w i, w (i + 1)} : Finset V)) (range n) := by
  intro i hi j hj hij
  simp only [coe_range, Set.mem_Iio] at hi hj
  have h3 := h.three_le
  have hsi : cycSucc n i < n := cycSucc_lt (by omega)
  have hsj : cycSucc n j < n := cycSucc_lt (by omega)
  have hij' : ({a, b, w i, w (cycSucc n i)} : Finset V) = {a, b, w j, w (cycSucc n j)} := by
    rw [← h.w_succ hi, ← h.w_succ hj]
    exact hij
  have m1 : w i ∈ ({a, b, w j, w (cycSucc n j)} : Finset V) := by rw [← hij']; simp
  have m2 : w (cycSucc n i) ∈ ({a, b, w j, w (cycSucc n j)} : Finset V) := by rw [← hij']; simp
  simp only [mem_insert, mem_singleton] at m1 m2
  rcases m1 with h1 | h1 | h1 | h1
  · exact absurd h1 (h.ne_a i hi)
  · exact absurd h1 (h.ne_b i hi)
  · exact h.w_inj hi hj h1
  · have e1 := h.w_inj hi hsj h1
    exfalso
    rcases m2 with h2 | h2 | h2 | h2
    · exact h.ne_a _ hsi h2
    · exact h.ne_b _ hsi h2
    · have e2 := h.w_inj hsi hj h2
      unfold cycSucc at e1 e2
      split_ifs at e1 e2 <;> omega
    · have e2 := h.w_inj hsi hsj h2
      unfold cycSucc at e1 e2
      split_ifs at e1 e2 <;> omega

/-- The tetrahedron `{a, b, w i, w (i+1)}`, `i < n`, belongs to `K`. -/
theorem tet_mem (h : IsCycleLink K a b n w) {i : ℕ} (hi : i < n) :
    ({a, b, w i, w (i + 1)} : Finset V) ∈ K.tets := by
  have : ({a, b, w i, w (i + 1)} : Finset V) ∈ star K {a, b} := by
    rw [h.star_eq]
    exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
  exact (mem_filter.mp this).1

/-- An edge with a cycle link is an edge of `K`. -/
theorem mem_edges (h : IsCycleLink K a b n w) : ({a, b} : Finset V) ∈ K.edges :=
  Complex3.mem_edges.mpr ⟨_, h.tet_mem (i := 0) (by have := h.three_le; omega),
    by simp [insert_subset_iff], card_pair h.ne⟩

/-- **An edge whose link is a cycle is interior**: each triangle `{a, b, w k}` lies in the two
tetrahedra `{a, b, w (k-1), w k}` and `{a, b, w k, w (k+1)}`, so none is a boundary triangle. -/
theorem mem_intEdges (h : IsCycleLink K a b n w) : ({a, b} : Finset V) ∈ intEdges K := by
  refine mem_filter.mpr ⟨h.mem_edges, ?_⟩
  rintro ⟨f, hf, hsub⟩
  have h3 := h.three_le
  simp only [bdryTris, mem_filter] at hf
  obtain ⟨t, ht, hft, hf3⟩ := Complex3.mem_tris.mp hf.1
  have htstar : t ∈ star K {a, b} := mem_filter.mpr ⟨ht, hsub.trans hft⟩
  rw [h.star_eq, mem_image] at htstar
  obtain ⟨i, hi, rfl⟩ := htstar
  rw [mem_range] at hi
  -- the third vertex `v` of `f`
  have hcard : #(f \ {a, b}) = 1 := by rw [card_sdiff_of_subset hsub, hf3, card_pair h.ne]
  obtain ⟨v, hv⟩ := card_pos.mp (show 0 < #(f \ {a, b}) by omega)
  rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hv
  have hvt := hft hv.1
  simp only [mem_insert, mem_singleton] at hvt
  -- `v = w k` for some `k < n`
  obtain ⟨k, hk, rfl⟩ : ∃ k < n, v = w k := by
    rcases hvt with h1 | h1 | h1 | h1
    · exact absurd h1 hv.2.1
    · exact absurd h1 hv.2.2
    · exact ⟨i, hi, h1⟩
    · exact ⟨cycSucc n i, cycSucc_lt (by omega), h1.trans (h.w_succ hi)⟩
  have hf_eq : f = {a, b, w k} := by
    symm
    apply eq_of_subset_of_card_le
    · simp only [insert_subset_iff, singleton_subset_iff]
      exact ⟨hsub (by simp), hsub (by simp), hv.1⟩
    · have : #({a, b, w k} : Finset V) = 3 := by
        rw [card_insert_of_notMem (by simp [h.ne, (h.ne_a k hk).symm]),
          card_pair (h.ne_b k hk).symm]
      omega
  -- the previous index `p`, with `w (p+1) = w k`
  set p := if k = 0 then n - 1 else k - 1 with hp_def
  have hp : p < n := by rw [hp_def]; split_ifs <;> omega
  have hpk : w (p + 1) = w k := by
    rw [hp_def]
    split_ifs with hk0
    · rw [show n - 1 + 1 = n by omega, h.closed, hk0]
    · rw [show k - 1 + 1 = k by omega]
  have hne : ({a, b, w k, w (k + 1)} : Finset V) ≠ {a, b, w p, w (p + 1)} := by
    intro he
    have := h.injOn_tet (by simpa using hk) (by simpa using hp) he
    rw [hp_def] at this
    split_ifs at this <;> omega
  have hsub2 : ({{a, b, w k, w (k + 1)}, {a, b, w p, w (p + 1)}} : Finset (Finset V)) ⊆
      star K f := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact mem_filter.mpr ⟨h.tet_mem hk, by rw [hf_eq]; intro x; simp; tauto⟩
    · refine mem_filter.mpr ⟨h.tet_mem hp, ?_⟩
      rw [hf_eq, hpk]
      intro x
      simp
      tauto
  have := card_le_card hsub2
  rw [card_pair hne, hf.2] at this
  omega

/-- The four vertices of each tetrahedron `{a, b, w i, w (i+1)}` of the ring are distinct. -/
theorem tet_distinct (h : IsCycleLink K a b n w) {i : ℕ} (hi : i < n) :
    a ≠ w i ∧ a ≠ w (i + 1) ∧ b ≠ w i ∧ b ≠ w (i + 1) ∧ w i ≠ w (i + 1) := by
  have h3 := h.three_le
  have hs : cycSucc n i < n := cycSucc_lt (by omega)
  rw [h.w_succ hi]
  refine ⟨(h.ne_a i hi).symm, (h.ne_a _ hs).symm, (h.ne_b i hi).symm, (h.ne_b _ hs).symm, ?_⟩
  intro he
  have := h.w_inj hi hs he
  unfold cycSucc at this
  split_ifs at this <;> omega

/-- Around an edge with a cycle link, the angle sum runs once over the ring of tetrahedra. -/
theorem angleSum_eq (h : IsCycleLink K a b n w) (ℓ : Finset V → ℝ) :
    angleSum K ℓ {a, b} = ∑ i ∈ range n, dihedralAt ℓ {a, b, w i, w (i + 1)} {a, b} := by
  rw [angleSum, h.star_eq, sum_image h.injOn_tet]

/-- The edge lies in exactly `n` tetrahedra. -/
theorem card_star (h : IsCycleLink K a b n w) : #(star K {a, b}) = n := by
  rw [h.star_eq, card_image_of_injOn h.injOn_tet, card_range]

end IsCycleLink

namespace IsPathLink

variable {K : Complex3 V} {a b : V} {n : ℕ} {w : ℕ → V}

/-- The tetrahedron `{a, b, w i, w (i+1)}`, `i < n`, belongs to `K`. -/
theorem tet_mem (h : IsPathLink K a b n w) {i : ℕ} (hi : i < n) :
    ({a, b, w i, w (i + 1)} : Finset V) ∈ K.tets := by
  have : ({a, b, w i, w (i + 1)} : Finset V) ∈ star K {a, b} := by
    rw [h.star_eq]
    exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩
  exact (mem_filter.mp this).1

/-- **An edge whose link is a path is a boundary edge**: the triangle `{a, b, w 0}` at the end of
the path lies only in the tetrahedron `{a, b, w 0, w 1}`. -/
theorem mem_bdryEdges (h : IsPathLink K a b n w) : ({a, b} : Finset V) ∈ bdryEdges K := by
  have h1 := h.one_le
  have hT := h.tet_mem (i := 0) (by omega)
  have hw0a := h.ne_a 0 (by omega)
  have hw0b := h.ne_b 0 (by omega)
  have hstar : star K {a, b, w 0} = {{a, b, w 0, w (0 + 1)}} := by
    ext t
    simp only [star, mem_filter, mem_singleton]
    constructor
    · rintro ⟨ht, hsub⟩
      have : t ∈ star K {a, b} :=
        mem_filter.mpr ⟨ht, (by simp [insert_subset_iff] : ({a, b} : Finset V) ⊆ {a, b, w 0}).trans
          hsub⟩
      rw [h.star_eq, mem_image] at this
      obtain ⟨i, hi, rfl⟩ := this
      rw [mem_range] at hi
      have hw : w 0 ∈ ({a, b, w i, w (i + 1)} : Finset V) := hsub (by simp)
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with hw | hw | hw | hw
      · exact absurd hw hw0a
      · exact absurd hw hw0b
      · have := h.inj (by simp only [coe_range, Set.mem_Iio]; omega)
          (by simp only [coe_range, Set.mem_Iio]; omega) hw
        subst this
        rfl
      · have := h.inj (by simp only [coe_range, Set.mem_Iio]; omega)
          (by simp only [coe_range, Set.mem_Iio]; omega) hw
        omega
    · rintro rfl
      exact ⟨hT, by intro x; simp; tauto⟩
  have hcard3 : #({a, b, w 0} : Finset V) = 3 := by
    rw [card_insert_of_notMem (by simp [h.ne, hw0a.symm]), card_pair hw0b.symm]
  refine mem_filter.mpr ⟨Complex3.mem_edges.mpr ⟨_, hT, by simp [insert_subset_iff],
    card_pair h.ne⟩, ⟨{a, b, w 0}, ?_, by simp [insert_subset_iff]⟩⟩
  refine mem_filter.mpr ⟨Complex3.mem_tris.mpr ⟨_, hT, by intro x; simp; tauto, hcard3⟩, ?_⟩
  rw [hstar, card_singleton]

end IsPathLink

/-- On an edge-manifold, the interior edges are exactly the edges whose link is a cycle. -/
theorem IsEdgeManifold.mem_intEdges_iff {K : Complex3 V} (hK : IsEdgeManifold K)
    {e : Finset V} : e ∈ intEdges K ↔ ∃ a b n w, e = {a, b} ∧ IsCycleLink K a b n w := by
  constructor
  · intro he
    obtain ⟨a, b, n, w, rfl, hc | hp⟩ := hK e (mem_filter.mp he).1
    · exact ⟨a, b, n, w, rfl, hc⟩
    · exact absurd hp.mem_bdryEdges (disjoint_left.mp (disjoint_intEdges_bdryEdges K) he)
  · rintro ⟨a, b, n, w, rfl, hc⟩
    exact hc.mem_intEdges

/-- On an edge-manifold, the boundary edges are exactly the edges whose link is a path. -/
theorem IsEdgeManifold.mem_bdryEdges_iff {K : Complex3 V} (hK : IsEdgeManifold K)
    {e : Finset V} : e ∈ bdryEdges K ↔ ∃ a b n w, e = {a, b} ∧ IsPathLink K a b n w := by
  constructor
  · intro he
    obtain ⟨a, b, n, w, rfl, hc | hp⟩ := hK e (mem_filter.mp he).1
    · exact absurd he (disjoint_left.mp (disjoint_intEdges_bdryEdges K) hc.mem_intEdges)
    · exact ⟨a, b, n, w, rfl, hp⟩
  · rintro ⟨a, b, n, w, rfl, hp⟩
    exact hp.mem_bdryEdges

end Lightlike.Regge
