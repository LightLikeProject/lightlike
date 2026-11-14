import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite pure 4-dimensional simplicial complexes

A 4-dimensional triangulation is described, as the 3-dimensional ones of `PonzanoRegge/`
(`Lightlike.PR.Complex3`), by its top-dimensional simplices: a `Complex4 V` is a finite set of
5-element vertex sets, the **4-simplices**. All lower faces are the subsets of the 4-simplices.
No manifold condition is imposed here; closedness and orientation are in
`Lightlike/FourD/Boundary.lean` and `Lightlike/FourD/Orientation.lean`, the Pachner moves in
`Lightlike/FourD/Pachner.lean`.

## Definitions

* `Complex4 V`: the 4-simplices, each with exactly five vertices.
* `faces K k`: the `k`-dimensional faces, i.e. the `(k+1)`-element subsets of 4-simplices.
  `verts`, `edges`, `tris`, `tets` are the vertices (as elements of `V`) and the faces of
  dimension 1, 2, 3.
* `allFaces K`: all nonempty faces, of every dimension.
* `euler4 K = f₀ - f₁ + f₂ - f₃ + f₄`: the Euler characteristic, with `fₖ = #(faces K k)`.
* `toPre K`: the same complex as an abstract simplicial complex in Mathlib's sense
  (`PreAbstractSimplicialComplex`), whose faces are exactly `allFaces K`.
* `simplex s`: the complex made of one 4-simplex `s`. `sphere S`: the boundary of a 5-simplex
  `S` (the six 5-element subsets of a 6-element set `S`), the smallest triangulation of the
  4-sphere.

## Main results

* `faces_four`, `faces_eq_empty`: the 4-dimensional faces are the 4-simplices, and there are no
  faces of dimension above 4. `card_faces_zero`: `f₀` is the number of vertices.
* `euler4_eq_sum`: `χ(K) = Σ_{f nonempty face} (-1)^(#f + 1)`, the form used for the invariance
  under Pachner moves.
* `mem_toPre`: the faces of `toPre K` are the nonempty faces of `K`.
* `card_faces_simplex`, `card_faces_sphere`: `fₖ = C(5, k+1)` for a 4-simplex and
  `fₖ = C(6, k+1)` for the boundary of a 5-simplex, so `(5, 10, 10, 5, 1)` and
  `(6, 15, 20, 15, 6)`; `euler4_simplex = 1`, `euler4_sphere = 2`.
-/

open Finset

namespace Lightlike.FourD

variable {V : Type*} [DecidableEq V]

/-- A finite pure 4-dimensional simplicial complex, given by its 4-simplices (5-element vertex
sets). -/
structure Complex4 (V : Type*) [DecidableEq V] where
  /-- The 4-simplices, as 5-element vertex sets. -/
  simps : Finset (Finset V)
  card_eq : ∀ s ∈ simps, #s = 5

namespace Complex4

/-- Two complexes with the same 4-simplices are equal. -/
@[ext] lemma ext {K K' : Complex4 V} (h : K.simps = K'.simps) : K = K' := by
  cases K; cases K'; subst h; rfl

/-- The `k`-dimensional faces: the `(k+1)`-element subsets of 4-simplices. -/
def faces (K : Complex4 V) (k : ℕ) : Finset (Finset V) := K.simps.biUnion (powersetCard (k + 1))

/-- The vertices: the elements of the 4-simplices. -/
def verts (K : Complex4 V) : Finset V := K.simps.biUnion id

/-- The edges: the 1-dimensional faces. -/
abbrev edges (K : Complex4 V) : Finset (Finset V) := K.faces 1

/-- The triangles: the 2-dimensional faces. -/
abbrev tris (K : Complex4 V) : Finset (Finset V) := K.faces 2

/-- The tetrahedra: the 3-dimensional faces. -/
abbrev tets (K : Complex4 V) : Finset (Finset V) := K.faces 3

/-- All nonempty faces of `K`, of every dimension. -/
def allFaces (K : Complex4 V) : Finset (Finset V) := K.simps.biUnion fun s => s.powerset.erase ∅

lemma mem_faces {K : Complex4 V} {k : ℕ} {f : Finset V} :
    f ∈ K.faces k ↔ ∃ s ∈ K.simps, f ⊆ s ∧ #f = k + 1 := by
  simp [faces, mem_powersetCard]

/-- A `k`-dimensional face has `k + 1` vertices. -/
lemma card_of_mem_faces {K : Complex4 V} {k : ℕ} {f : Finset V} (h : f ∈ K.faces k) :
    #f = k + 1 := by
  obtain ⟨_, _, _, hf⟩ := mem_faces.mp h
  exact hf

lemma mem_verts {K : Complex4 V} {v : V} : v ∈ K.verts ↔ ∃ s ∈ K.simps, v ∈ s := by
  simp [verts]

lemma mem_allFaces {K : Complex4 V} {f : Finset V} :
    f ∈ K.allFaces ↔ f.Nonempty ∧ ∃ s ∈ K.simps, f ⊆ s := by
  simp only [allFaces, mem_biUnion, mem_erase, mem_powerset, nonempty_iff_ne_empty]
  aesop

/-- Every face of `K` has at most five vertices. -/
lemma card_le_five {K : Complex4 V} {f s : Finset V} (hs : s ∈ K.simps) (hf : f ⊆ s) :
    #f ≤ 5 := K.card_eq s hs ▸ card_le_card hf

/-- The 4-dimensional faces are the 4-simplices. -/
theorem faces_four (K : Complex4 V) : K.faces 4 = K.simps := by
  ext f
  rw [mem_faces]
  constructor
  · rintro ⟨s, hs, hfs, hf⟩
    rwa [eq_of_subset_of_card_le hfs (by rw [K.card_eq s hs, hf])]
  · exact fun hf => ⟨f, hf, subset_refl _, K.card_eq f hf⟩

/-- There are no faces of dimension above 4. -/
theorem faces_eq_empty (K : Complex4 V) {k : ℕ} (hk : 4 < k) : K.faces k = ∅ := by
  ext f
  simp only [mem_faces, notMem_empty, iff_false, not_exists, not_and]
  intro s hs hfs hf
  have := card_le_five hs hfs
  omega

/-- The 0-dimensional faces are the singletons of the vertices. -/
lemma faces_zero (K : Complex4 V) : K.faces 0 = K.verts.image singleton := by
  ext f
  simp only [mem_faces, zero_add, card_eq_one, mem_image, mem_verts]
  constructor
  · rintro ⟨s, hs, hfs, a, rfl⟩
    exact ⟨a, ⟨s, hs, singleton_subset_iff.mp hfs⟩, rfl⟩
  · rintro ⟨a, ⟨s, hs, has⟩, rfl⟩
    exact ⟨s, hs, singleton_subset_iff.mpr has, a, rfl⟩

/-- `f₀` is the number of vertices. -/
theorem card_faces_zero (K : Complex4 V) : #(K.faces 0) = #K.verts := by
  rw [faces_zero, card_image_of_injective _ singleton_injective]

/-- The nonempty faces are the faces of dimensions `0, …, 4`. -/
lemma allFaces_eq (K : Complex4 V) : K.allFaces = (range 5).biUnion K.faces := by
  ext f
  simp only [mem_allFaces, mem_biUnion, mem_range, mem_faces]
  constructor
  · rintro ⟨hne, s, hs, hfs⟩
    have h1 := card_le_five hs hfs
    have h2 := hne.card_pos
    exact ⟨#f - 1, by omega, s, hs, hfs, by omega⟩
  · rintro ⟨k, -, s, hs, hfs, hf⟩
    exact ⟨card_pos.mp (by omega), s, hs, hfs⟩

/-- The Euler characteristic `f₀ - f₁ + f₂ - f₃ + f₄`. -/
def euler4 (K : Complex4 V) : ℤ := ∑ k ∈ range 5, (-1) ^ k * (#(K.faces k) : ℤ)

/-- The Euler characteristic as an alternating sum over all nonempty faces. -/
theorem euler4_eq_sum (K : Complex4 V) :
    K.euler4 = ∑ f ∈ K.allFaces, (-1 : ℤ) ^ (#f + 1) := by
  rw [allFaces_eq, sum_biUnion]
  · refine sum_congr rfl fun k _ => ?_
    have h : ∀ f ∈ K.faces k, (-1 : ℤ) ^ (#f + 1) = (-1) ^ k := fun f hf => by
      rw [card_of_mem_faces hf]; ring
    rw [sum_congr rfl h, sum_const, nsmul_eq_mul, mul_comm]
  · intro k _ l _ hkl
    refine disjoint_left.mpr fun f hk hl => hkl ?_
    have := card_of_mem_faces hk
    have := card_of_mem_faces hl
    omega

/-- The complex as an abstract simplicial complex in Mathlib's sense: its faces are the nonempty
subsets of 4-simplices. -/
def toPre (K : Complex4 V) : PreAbstractSimplicialComplex V where
  faces := {f | f.Nonempty ∧ ∃ s ∈ K.simps, f ⊆ s}
  isRelLowerSet_faces := by
    rintro f ⟨hne, s, hs, hfs⟩
    exact ⟨hne, fun g hgf hg => ⟨hg, s, hs, (hgf : g ⊆ f).trans hfs⟩⟩

/-- The faces of `toPre K` are exactly the nonempty faces of `K`. -/
theorem mem_toPre {K : Complex4 V} {f : Finset V} : f ∈ K.toPre ↔ f ∈ K.allFaces := by
  rw [mem_allFaces]
  rfl

/-! ## Examples: a 4-simplex and the boundary of a 5-simplex -/

/-- The complex consisting of the single 4-simplex `s`. -/
def simplex (s : Finset V) (hs : #s = 5) : Complex4 V where
  simps := {s}
  card_eq t ht := by rw [mem_singleton.mp ht]; exact hs

/-- The 5-element subsets of `S` as 4-simplices. For `#S = 6` (assumed by all results about it)
this is the boundary of the 5-simplex `S`, the smallest triangulation of the 4-sphere. -/
def sphere (S : Finset V) : Complex4 V where
  simps := S.powersetCard 5
  card_eq _ ht := (mem_powersetCard.mp ht).2

/-- The faces of a 4-simplex `s` are its subsets. -/
lemma faces_simplex {s : Finset V} (hs : #s = 5) (k : ℕ) :
    (simplex s hs).faces k = s.powersetCard (k + 1) := by
  simp [faces, simplex]

/-- The faces of the boundary of a 5-simplex `S` are the subsets of `S` with at most five
elements. -/
lemma faces_sphere {S : Finset V} (hS : #S = 6) {k : ℕ} (hk : k ≤ 4) :
    (sphere S).faces k = S.powersetCard (k + 1) := by
  ext f
  simp only [mem_faces, sphere, mem_powersetCard]
  constructor
  · rintro ⟨s, ⟨hsS, -⟩, hfs, hf⟩
    exact ⟨hfs.trans hsS, hf⟩
  · rintro ⟨hfS, hf⟩
    -- extend `f` to a 5-element subset of `S`
    obtain ⟨s, hfs, hsS, hs⟩ := exists_subsuperset_card_eq hfS (by omega) (by omega : 5 ≤ #S)
    exact ⟨s, ⟨hsS, hs⟩, hfs, hf⟩

/-- **Face counts of a 4-simplex**: `fₖ = C(5, k+1)`, i.e. `(5, 10, 10, 5, 1)`. -/
theorem card_faces_simplex {s : Finset V} (hs : #s = 5) (k : ℕ) :
    #((simplex s hs).faces k) = Nat.choose 5 (k + 1) := by
  rw [faces_simplex, card_powersetCard, hs]

/-- **Face counts of the boundary of a 5-simplex**: `fₖ = C(6, k+1)` for `k ≤ 4`, i.e.
`(6, 15, 20, 15, 6)`. -/
theorem card_faces_sphere {S : Finset V} (hS : #S = 6) {k : ℕ} (hk : k ≤ 4) :
    #((sphere S).faces k) = Nat.choose 6 (k + 1) := by
  rw [faces_sphere hS hk, card_powersetCard, hS]

/-- A 4-simplex has Euler characteristic `5 - 10 + 10 - 5 + 1 = 1`. -/
theorem euler4_simplex {s : Finset V} (hs : #s = 5) : (simplex s hs).euler4 = 1 := by
  simp only [euler4, sum_range_succ, sum_range_zero, card_faces_simplex]
  decide

/-- The boundary of a 5-simplex has Euler characteristic `6 - 15 + 20 - 15 + 6 = 2`, that of the
4-sphere. -/
theorem euler4_sphere {S : Finset V} (hS : #S = 6) : (sphere S).euler4 = 2 := by
  simp only [euler4, sum_range_succ, sum_range_zero]
  rw [card_faces_sphere hS (by norm_num), card_faces_sphere hS (by norm_num),
    card_faces_sphere hS (by norm_num), card_faces_sphere hS (by norm_num),
    card_faces_sphere hS (by norm_num)]
  decide

end Complex4

end Lightlike.FourD
