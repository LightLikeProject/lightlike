import Lightlike.FourD.Complex
import Lightlike.PonzanoRegge.Amplitude
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Boundary data of 4-complexes

The **star** of a face is the set of 4-simplices containing it. A tetrahedron is a **boundary
tetrahedron** if it lies in exactly one 4-simplex. As in `Lightlike/Regge/Complex.lean` (`bdryTris`)
no manifold condition is imposed in the definitions; the conditions used are named explicitly.

## Definitions

* `star K f`: the 4-simplices of `K` containing `f`.
* `bdryTets K`: the tetrahedra in exactly one 4-simplex.
* `IsPseudo4 K`: every tetrahedron lies in at most two 4-simplices (a pseudo-manifold with
  boundary, without the connectedness condition).
* `IsClosed4 K`: every tetrahedron lies in exactly two 4-simplices (a closed pseudo-manifold,
  without connectedness), the 4-dimensional analogue of `Lightlike.PR.IsClosed2`.
* `boundary K : Lightlike.PR.Complex3 V`: the boundary tetrahedra as a 3-complex, in the form used by
  the Ponzano–Regge and Regge files.

## Main results

* `card_supersets`: a `k`-element subset `t` of `S` lies in exactly `#S - k` of the
  `(k+1)`-element subsets of `S`. This is the counting behind all the face incidences below.
* `isClosed4_iff`: closed means pseudo-manifold without boundary tetrahedra.
* `even_card_bdryTets`: **the boundary has no boundary (mod 2)**. In a pseudo-manifold every
  triangle lies in an even number of boundary tetrahedra.
* For a single 4-simplex `s` (the data carried by a 15j symbol or a 4D Regge simplex):
  `bdryTets_simplex` (its boundary is its five tetrahedra), `tets_simplex_eq_image_erase` (they
  are `s \ {v}` for the five vertices `v`), `card_inter_erase` (two of them meet in a triangle),
  `boundary_simplex_closed` (every triangle of the boundary lies in exactly two of its
  tetrahedra, so the boundary is a closed 3-complex). So the tetrahedra and triangles of a
  4-simplex are the vertices and edges of the complete graph on five vertices.
* `isClosed4_sphere`: the boundary of a 5-simplex is closed.
-/

open Finset

namespace Lightlike.FourD

variable {V : Type*} [DecidableEq V]

/-- A `k`-element subset `t` of `S` lies in exactly `#S - k` of the `(k+1)`-element subsets of
`S`: they are `insert x t` for `x ∈ S \ t`. -/
theorem card_supersets {S t : Finset V} (htS : t ⊆ S) :
    #((S.powersetCard (#t + 1)).filter (t ⊆ ·)) = #S - #t := by
  have h : (S.powersetCard (#t + 1)).filter (t ⊆ ·) = (S \ t).image (insert · t) := by
    ext u
    simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
    constructor
    · rintro ⟨⟨huS, hu⟩, htu⟩
      obtain ⟨x, hx⟩ : ∃ x, u \ t = {x} := card_eq_one.mp (by rw [card_sdiff_of_subset htu, hu]; omega)
      have hxu : x ∈ u \ t := hx ▸ mem_singleton_self x
      refine ⟨x, ⟨huS (mem_sdiff.mp hxu).1, (mem_sdiff.mp hxu).2⟩, ?_⟩
      rw [insert_eq, ← hx, sdiff_union_of_subset htu]
    · rintro ⟨x, ⟨hxS, hxt⟩, rfl⟩
      exact ⟨⟨insert_subset hxS htS, card_insert_of_notMem hxt⟩, subset_insert x t⟩
  rw [h, card_image_of_injOn, card_sdiff_of_subset htS]
  intro x hx y hy hxy
  have hxy' : insert x t = insert y t := hxy
  have : x ∈ insert y t := hxy' ▸ mem_insert_self x t
  rcases mem_insert.mp this with h | h
  · exact h
  · exact absurd h (mem_sdiff.mp hx).2

namespace Complex4

/-- The 4-simplices containing the face `f`. -/
def star (K : Complex4 V) (f : Finset V) : Finset (Finset V) := K.simps.filter (f ⊆ ·)

/-- The boundary tetrahedra: those lying in exactly one 4-simplex. -/
def bdryTets (K : Complex4 V) : Finset (Finset V) := K.tets.filter fun t => #(K.star t) = 1

/-- Every tetrahedron lies in at most two 4-simplices. -/
def IsPseudo4 (K : Complex4 V) : Prop := ∀ t ∈ K.tets, #(K.star t) ≤ 2

/-- Every tetrahedron lies in exactly two 4-simplices: `K` has no boundary. -/
def IsClosed4 (K : Complex4 V) : Prop := ∀ t ∈ K.tets, #(K.star t) = 2

lemma mem_star {K : Complex4 V} {f s : Finset V} : s ∈ K.star f ↔ s ∈ K.simps ∧ f ⊆ s :=
  mem_filter

/-- A face lies in at least one 4-simplex. -/
lemma star_nonempty {K : Complex4 V} {k : ℕ} {f : Finset V} (hf : f ∈ K.faces k) :
    (K.star f).Nonempty := by
  obtain ⟨s, hs, hfs, -⟩ := mem_faces.mp hf
  exact ⟨s, mem_star.mpr ⟨hs, hfs⟩⟩

lemma mem_bdryTets {K : Complex4 V} {t : Finset V} :
    t ∈ K.bdryTets ↔ t ∈ K.tets ∧ #(K.star t) = 1 := mem_filter

/-- `K` is closed exactly when it is a pseudo-manifold without boundary tetrahedra. -/
theorem isClosed4_iff {K : Complex4 V} : K.IsClosed4 ↔ K.IsPseudo4 ∧ K.bdryTets = ∅ := by
  constructor
  · intro h
    refine ⟨fun t ht => (h t ht).le, eq_empty_of_forall_notMem fun t ht => ?_⟩
    have := (mem_bdryTets.mp ht).2
    rw [h t (mem_bdryTets.mp ht).1] at this
    exact absurd this (by norm_num)
  · rintro ⟨hP, hB⟩ t ht
    have h1 := (star_nonempty ht).card_pos
    have h2 := hP t ht
    have h3 : #(K.star t) ≠ 1 := fun h1 =>
      notMem_empty t (hB ▸ mem_bdryTets.mpr ⟨ht, h1⟩)
    omega

/-- The boundary tetrahedra as a 3-complex. -/
def boundary (K : Complex4 V) : Lightlike.PR.Complex3 V where
  tets := K.bdryTets
  card_eq _ ht := card_of_mem_faces (mem_bdryTets.mp ht).1

/-- A 4-simplex `s` containing a triangle `f` contains exactly two tetrahedra through `f`. -/
lemma card_tets_through {f s : Finset V} (hf : #f = 3) (hs : #s = 5) (hfs : f ⊆ s) :
    #((s.powersetCard 4).filter (f ⊆ ·)) = 2 := by
  have := card_supersets hfs
  rw [hf, hs] at this
  exact this

/-- **The boundary has no boundary, mod 2.** In a pseudo-manifold, every triangle lies in an
even number of boundary tetrahedra. (Count the pairs `f ⊆ t ⊆ s` with `t` a tetrahedron and `s`
a 4-simplex: each 4-simplex through `f` gives two, and each tetrahedron through `f` gives one or
two.) -/
theorem even_card_bdryTets {K : Complex4 V} (hK : K.IsPseudo4) {f : Finset V} (hf : #f = 3) :
    Even #(K.bdryTets.filter (f ⊆ ·)) := by
  set T := K.tets.filter (f ⊆ ·) with hT
  -- double counting of the pairs (t, s)
  have hcount : ∑ t ∈ T, #(K.star t) = 2 * #(K.star f) := by
    have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T) (t := K.simps)
      (r := fun t s => t ⊆ s)
    simp only [bipartiteAbove, bipartiteBelow] at this
    rw [show ∑ t ∈ T, #(K.star t) = ∑ t ∈ T, #(K.simps.filter (t ⊆ ·)) from rfl, this,
      ← sum_filter_add_sum_filter_not K.simps (f ⊆ ·)]
    have h0 : ∀ s ∈ K.simps.filter (¬ f ⊆ ·), #(T.filter (· ⊆ s)) = 0 := by
      intro s hs
      refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun t ht hts => ?_)
      exact (mem_filter.mp hs).2 (((mem_filter.mp ht).2).trans hts)
    have h2 : ∀ s ∈ K.simps.filter (f ⊆ ·), #(T.filter (· ⊆ s)) = 2 := by
      intro s hs
      obtain ⟨hsK, hfs⟩ := mem_filter.mp hs
      rw [← card_tets_through hf (K.card_eq s hsK) hfs]
      congr 1
      ext t
      simp only [hT, mem_filter, mem_powersetCard, mem_faces]
      constructor
      · rintro ⟨⟨⟨_, _, _, ht⟩, hft⟩, hts⟩
        exact ⟨⟨hts, ht⟩, hft⟩
      · rintro ⟨⟨hts, ht⟩, hft⟩
        exact ⟨⟨⟨s, hsK, hts, ht⟩, hft⟩, hts⟩
    rw [sum_congr rfl h0, sum_congr rfl h2, sum_const_zero, add_zero, sum_const, smul_eq_mul,
      mul_comm]
    rfl
  -- every tetrahedron through `f` lies in one or two 4-simplices
  rw [← sum_filter_add_sum_filter_not T (fun t => #(K.star t) = 1)] at hcount
  have h1 : ∑ t ∈ T.filter (fun t => #(K.star t) = 1), #(K.star t) =
      #(T.filter fun t => #(K.star t) = 1) := by
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun t ht => (mem_filter.mp ht).2
  have h2 : ∑ t ∈ T.filter (fun t => ¬ #(K.star t) = 1), #(K.star t) =
      2 * #(T.filter fun t => ¬ #(K.star t) = 1) := by
    rw [card_eq_sum_ones, mul_sum, mul_one]
    refine sum_congr rfl fun t ht => ?_
    obtain ⟨htT, hne⟩ := mem_filter.mp ht
    have htK := (mem_filter.mp htT).1
    have := hK t htK
    have := (star_nonempty htK).card_pos
    omega
  rw [h1, h2] at hcount
  have hB : K.bdryTets.filter (f ⊆ ·) = T.filter fun t => #(K.star t) = 1 := by
    ext t
    simp only [hT, bdryTets, mem_filter]
    tauto
  rw [hB]
  exact ⟨#(K.star f) - #(T.filter fun t => ¬ #(K.star t) = 1), by omega⟩

/-! ## The boundary of a single 4-simplex -/

/-- The tetrahedra of a 4-simplex `s` are the sets `s \ {v}`, one for each vertex `v`. -/
theorem tets_simplex_eq_image_erase {s : Finset V} (hs : #s = 5) :
    (simplex s hs).tets = s.image s.erase := by
  show (simplex s hs).faces 3 = _
  rw [faces_simplex]
  ext t
  simp only [mem_powersetCard, mem_image]
  constructor
  · rintro ⟨hts, ht⟩
    obtain ⟨v, hv⟩ : ∃ v, s \ t = {v} := card_eq_one.mp (by rw [card_sdiff_of_subset hts, hs, ht])
    have hvs : v ∈ s \ t := hv ▸ mem_singleton_self v
    refine ⟨v, (mem_sdiff.mp hvs).1, ?_⟩
    rw [erase_eq, ← hv, Finset.sdiff_sdiff_eq_self hts]
  · rintro ⟨v, hv, rfl⟩
    exact ⟨erase_subset v s, by rw [card_erase_of_mem hv, hs]⟩

/-- The tetrahedra `s \ {v}` and `s \ {w}` of a 4-simplex, for `v ≠ w`, meet in the triangle
`s \ {v, w}`. -/
theorem card_inter_erase {s : Finset V} (hs : #s = 5) {v w : V} (hv : v ∈ s) (hw : w ∈ s)
    (hvw : v ≠ w) : #(s.erase v ∩ s.erase w) = 3 := by
  have h : s.erase v ∩ s.erase w = (s.erase v).erase w := by
    ext x
    simp only [mem_inter, mem_erase]
    tauto
  rw [h, card_erase_of_mem (mem_erase.mpr ⟨hvw.symm, hw⟩), card_erase_of_mem hv, hs]

/-- The boundary of a 4-simplex consists of all its five tetrahedra. -/
theorem bdryTets_simplex {s : Finset V} (hs : #s = 5) :
    (simplex s hs).bdryTets = s.powersetCard 4 := by
  have h : (simplex s hs).tets = s.powersetCard 4 := faces_simplex hs 3
  rw [bdryTets, h, filter_true_of_mem]
  intro t ht
  rw [mem_powersetCard] at ht
  rw [star, simplex, filter_singleton, ite_eq_left_of_eq_true _ _ (eq_true ht.1), card_singleton]

/-- The boundary of a 4-simplex is a closed 3-complex: each of its triangles lies in exactly two
of its tetrahedra. -/
theorem boundary_simplex_closed {s : Finset V} (hs : #s = 5) :
    ∀ f ∈ (simplex s hs).boundary.tris, #((simplex s hs).boundary.tets.filter (f ⊆ ·)) = 2 := by
  intro f hf
  obtain ⟨t, ht, hft, hf⟩ := Lightlike.PR.Complex3.mem_tris.mp hf
  have ht' : t ∈ s.powersetCard 4 := bdryTets_simplex hs ▸ ht
  have hfs : f ⊆ s := hft.trans (mem_powersetCard.mp ht').1
  show #((simplex s hs).bdryTets.filter (f ⊆ ·)) = 2
  rw [bdryTets_simplex hs]
  exact card_tets_through hf hs hfs

/-- The star of a tetrahedron `t ⊆ S` in the boundary of the 5-simplex `S` has two elements. -/
lemma card_star_sphere {S t : Finset V} (hS : #S = 6) (htS : t ⊆ S) (ht : #t = 4) :
    #((sphere S).star t) = 2 := by
  have := card_supersets htS
  rw [ht, hS] at this
  exact this

/-- The boundary of a 5-simplex is closed. -/
theorem isClosed4_sphere {S : Finset V} (hS : #S = 6) : (sphere S).IsClosed4 := by
  intro t ht
  rw [show (sphere S).tets = S.powersetCard 4 from faces_sphere hS (by norm_num),
    mem_powersetCard] at ht
  exact card_star_sphere hS ht.1 ht.2

end Complex4

end Lightlike.FourD
