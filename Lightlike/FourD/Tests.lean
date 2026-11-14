import Lightlike.FourD.Orientation

/-!
# Trust checks for the 4D combinatorics

Every check below is a kernel computation (`decide`) on explicit complexes, independent of the
general theorems, or a deliberately wrong input shown to fail.

* **Known face counts.** The 4-simplex has `(f₀, …, f₄) = (5, 10, 10, 5, 1)`, its boundary is a
  closed 3-complex with 5 tetrahedra, 10 triangles, 10 edges; the boundary of the 5-simplex has
  `(6, 15, 20, 15, 6)`, Euler characteristic 2, and is closed.
* **All five Pachner moves on the 4-sphere.** Starting from the boundary of the 5-simplex: a 1-5
  move gives `(7, 20, 30, 25, 10)`, a 2-4 move then `(7, 21, 34, 30, 12)`, a 3-3 move keeps
  `(7, 21, 34, 30, 12)`; the 4-2, 5-1 and 3-3 moves undo them (equality of the complexes is
  computed, not taken from `move_move`). Every complex in the sequence is closed and has Euler
  characteristic 2.
* **Malformed moves fail.** The 2-4 formula applied where the new edge already exists (on the
  boundary of the 5-simplex) gives a complex with boundary and Euler characteristic 1 instead of 2;
  dropping one of the four new 4-simplices of a 2-4 move leaves a boundary; a 1-5 move onto an
  existing vertex leaves a boundary. In each case `IsMove` is shown to fail.
* **Orientation conventions.** The oriented simplices `[2, 0, 1]` and `[1, 0, 2]` are `+[012]`
  and `-[012]` (even and odd permutations); the boundary operator with all signs `+1` has
  `∂∂ ≠ 0`; the constant sign is not an orientation of the 4-sphere, while `s ↦ [S : s]` is
  (checked by computation); and the join of an edge with the six-vertex real projective plane
  is a pseudo-manifold that is **not** orientable.
* **Non-vacuity.** In `joinRP2`, which has a boundary, every triangle lies in an even number of
  boundary tetrahedra and some triangle in two; the induced orientation on the boundary of a
  4-simplex is the textbook `∂[01234] = [1234] - [0234] + [0134] - [0124] + [0123]`.
* **Junk values.** The 5-element subsets of a 7-element set do not form a pseudo-manifold, so the
  hypothesis `#S = 6` in the results on `sphere S` is needed; the empty complex is closed and
  orientable only vacuously, with Euler characteristic 0.
-/

open Finset

set_option maxRecDepth 100000

namespace Lightlike.FourD.Tests

open Complex4
open Finsupp (single)

/-- The face numbers `(f₀, f₁, f₂, f₃, f₄)` of a 4-complex. -/
def fvec {V : Type*} [DecidableEq V] (K : Complex4 V) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (#(K.faces 0), #(K.faces 1), #(K.faces 2), #(K.faces 3), #(K.faces 4))

/-- The formula of `Complex4.move` without its preconditions, for malformed moves. -/
def rawMove {V : Type*} [DecidableEq V] (K : Complex4 V) (σ τ : Finset V) : Finset (Finset V) :=
  K.simps.filter (fun s => ¬ σ ⊆ s) ∪ σ.image fun u => (σ ∪ τ).erase u

/-! ## Face counts of a 4-simplex and of the boundary of a 5-simplex -/

/-- The 4-simplex with vertices `0, …, 4`. -/
def delta4 : Complex4 (Fin 5) := simplex univ (by decide +kernel)

/-- **The face numbers of a 4-simplex** are `(5, 10, 10, 5, 1)`. -/
theorem fvec_delta4 : fvec delta4 = (5, 10, 10, 5, 1) := by decide +kernel

/-- A 4-simplex has Euler characteristic `1`. -/
theorem euler4_delta4 : delta4.euler4 = 1 := by decide +kernel

/-- **The boundary of a 4-simplex** has 5 tetrahedra, 10 triangles and 10 edges, and each of its
triangles lies in exactly two of its tetrahedra. -/
theorem boundary_delta4 :
    #delta4.boundary.tets = 5 ∧ #delta4.boundary.tris = 10 ∧ #delta4.boundary.edges = 10 ∧
      ∀ f ∈ delta4.boundary.tris, #(delta4.boundary.tets.filter (f ⊆ ·)) = 2 := by
  decide +kernel

/-- The boundary of the 5-simplex with vertices `0, …, 5`, the smallest triangulation of the
4-sphere. -/
def sphere6 : Complex4 (Fin 6) := sphere univ

/-- **The face numbers of the boundary of a 5-simplex** are `(6, 15, 20, 15, 6)`, its Euler
characteristic is `2`, and it is closed. -/
theorem sphere6_checks : fvec sphere6 = (6, 15, 20, 15, 6) ∧ sphere6.euler4 = 2 ∧
    sphere6.IsClosed4 := by
  unfold IsClosed4
  decide +kernel

/-! ## The five Pachner moves on the 4-sphere -/

/-- The boundary of the 5-simplex on `0, …, 5`, inside the vertex type `Fin 8`. -/
def K0 : Complex4 (Fin 8) := sphere {0, 1, 2, 3, 4, 5}

/-- A 1-5 move on `K0`: the 4-simplex `01234` is subdivided by the new vertex `6`. -/
theorem isMove15 : K0.IsMove {0, 1, 2, 3, 4} {6} :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The result of the 1-5 move. -/
def K1 : Complex4 (Fin 8) := K0.move isMove15

/-- A 2-4 move on `K1`: the two 4-simplices through the tetrahedron `0123` are replaced by four
around the new edge `56`. -/
theorem isMove24 : K1.IsMove {0, 1, 2, 3} {5, 6} :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The result of the 2-4 move. -/
def K2 : Complex4 (Fin 8) := K1.move isMove24

/-- A 3-3 move on `K2`: the three 4-simplices around the triangle `023` are replaced by three
around the new triangle `456`. -/
theorem isMove33 : K2.IsMove {0, 2, 3} {4, 5, 6} :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The result of the 3-3 move. -/
def K3 : Complex4 (Fin 8) := K2.move isMove33

/-- **Face numbers along the moves**: `(6, 15, 20, 15, 6) → (7, 20, 30, 25, 10) →
(7, 21, 34, 30, 12) → (7, 21, 34, 30, 12)`. -/
theorem fvec_moves : fvec K0 = (6, 15, 20, 15, 6) ∧ fvec K1 = (7, 20, 30, 25, 10) ∧
    fvec K2 = (7, 21, 34, 30, 12) ∧ fvec K3 = (7, 21, 34, 30, 12) := by
  decide +kernel

/-- **Euler characteristic and closedness along the moves**, computed directly. -/
theorem moves_closed_euler : K1.euler4 = 2 ∧ K2.euler4 = 2 ∧ K3.euler4 = 2 ∧
    K1.IsClosed4 ∧ K2.IsClosed4 ∧ K3.IsClosed4 := by
  unfold IsClosed4
  decide +kernel

/-- **The 4-2 move undoes the 2-4 move**, computed directly. -/
theorem move42_K2 : ∃ h : K2.IsMove {5, 6} {0, 1, 2, 3}, K2.move h = K1 :=
  ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    Complex4.ext (by decide +kernel)⟩

/-- **The 5-1 move undoes the 1-5 move**, computed directly. -/
theorem move51_K1 : ∃ h : K1.IsMove {6} {0, 1, 2, 3, 4}, K1.move h = K0 :=
  ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    Complex4.ext (by decide +kernel)⟩

/-- **The inverse 3-3 move undoes the 3-3 move**, computed directly. -/
theorem move33_K3 : ∃ h : K3.IsMove {4, 5, 6} {0, 2, 3}, K3.move h = K2 :=
  ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩,
    Complex4.ext (by decide +kernel)⟩

/-- The complexes along the moves are orientable (from the theorems). -/
theorem moves_orientable : K1.IsOrientable ∧ K2.IsOrientable ∧ K3.IsOrientable := by
  have h0 : K0.IsOrientable := ⟨_, isOrientation_sphere (by decide +kernel)⟩
  have h1 : K1.IsOrientable := (isOrientable_move_iff isMove15).mpr h0
  have h2 : K2.IsOrientable := (isOrientable_move_iff isMove24).mpr h1
  exact ⟨h1, h2, (isOrientable_move_iff isMove33).mpr h2⟩

/-! ## Malformed moves -/

/-- The 2-4 formula on `K0` with the tetrahedron `0123` and the edge `45`, which is already an
edge of `K0`. -/
def badFresh : Complex4 (Fin 8) where
  simps := rawMove K0 {0, 1, 2, 3} {4, 5}
  card_eq := by decide +kernel

/-- **A 2-4 move onto an existing edge is not a move**, and its formula gives a complex with
boundary whose Euler characteristic is `1` instead of `2`. -/
theorem badFresh_fails : ¬ K0.IsMove {0, 1, 2, 3} {4, 5} ∧ ¬ badFresh.IsClosed4 ∧
    badFresh.euler4 = 1 ∧ fvec badFresh = (6, 15, 20, 14, 4) := by
  refine ⟨fun h => absurd h.fresh (by decide +kernel), ?_⟩
  unfold IsClosed4
  decide +kernel

/-- The 2-4 move on `K1` with one of the four new 4-simplices (`12356`) left out. -/
def badDrop : Complex4 (Fin 8) where
  simps := (rawMove K1 {0, 1, 2, 3} {5, 6}).erase {1, 2, 3, 5, 6}
  card_eq := by decide +kernel

/-- **Leaving out a new 4-simplex leaves a boundary.** -/
theorem badDrop_fails : ¬ badDrop.IsClosed4 ∧ badDrop.bdryTets.Nonempty := by
  unfold IsClosed4
  decide +kernel

/-- The 1-5 formula on `K0` with the existing vertex `5` as the "new" vertex. -/
def badVertex : Complex4 (Fin 8) where
  simps := rawMove K0 {0, 1, 2, 3, 4} {5}
  card_eq := by decide +kernel

/-- **A 1-5 move onto an existing vertex is not a move** and leaves a boundary. -/
theorem badVertex_fails : ¬ K0.IsMove {0, 1, 2, 3, 4} {5} ∧ ¬ badVertex.IsClosed4 := by
  refine ⟨fun h => absurd h.fresh (by decide +kernel), ?_⟩
  unfold IsClosed4
  decide +kernel

/-! ## Orientation conventions -/

/-- The cone on a single simplex with the sign and the vertex set evaluated. -/
lemma cone_single_eval {V : Type*} [LinearOrder V] {a : V} {s t : Finset V} {c : ℤ} (ha : a ∉ s)
    (hc : inc s a = c) (ht : insert a s = t) : cone a (single s 1) = c • single t 1 := by
  rw [cone_single, one_smul, coneSimplex, ite_eq_right ha, hc, ht]

/-- **Oriented simplices for permuted vertices**: `[2, 0, 1] = +[012]` (an even permutation) and
`[1, 0, 2] = -[012]` (an odd one), computed from the definition by cones. -/
theorem osimp_perms :
    osimp ([2, 0, 1] : List (Fin 3)) = single {0, 1, 2} 1 ∧
      osimp ([1, 0, 2] : List (Fin 3)) = -single {0, 1, 2} 1 := by
  simp only [osimp]
  constructor
  · rw [cone_single_eval (t := {1}) (c := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel), one_smul,
      cone_single_eval (t := {0, 1}) (c := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel), one_smul,
      cone_single_eval (t := {0, 1, 2}) (c := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel), one_smul]
  · rw [cone_single_eval (t := {2}) (c := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel), one_smul,
      cone_single_eval (t := {0, 2}) (c := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel), one_smul,
      cone_single_eval (t := {0, 1, 2}) (c := -1) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      neg_one_smul]

/-- The boundary operator with every sign `+1`: a deliberately wrong convention. -/
noncomputable def bdPlus : Chain (Fin 3) →ₗ[ℤ] Chain (Fin 3) :=
  Finsupp.linearCombination ℤ fun s => ∑ v ∈ s, single (s.erase v) 1

/-- **With all signs `+1`, `∂∂ ≠ 0`**: the vertex `0` gets coefficient `2` in `∂∂[012]`, while
the correct boundary operator gives `0`. -/
theorem bdPlus_bdPlus :
    bdPlus (bdPlus (single {0, 1, 2} 1)) {0} = 2 ∧ bd (bd (single ({0, 1, 2} : Finset (Fin 3)) 1)) {0} = 0 := by
  refine ⟨?_, by rw [bd_bd]; rfl⟩
  simp only [bdPlus, Finsupp.linearCombination_single, one_smul, map_sum,
    Finsupp.finsetSum_apply, Finsupp.single_apply]
  decide +kernel

/-- **The orientation `s ↦ [S : s]` of the 4-sphere, checked by computation.** -/
theorem sphere6_orientation : sphere6.IsOrientation (relSign univ) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **The constant sign is not an orientation of the 4-sphere**: the 4-simplices `01234` and
`01235` induce the same orientation on `0123`. -/
theorem sphere6_const_not_orientation : ¬ sphere6.IsOrientation fun _ => 1 := fun ho =>
  absurd (ho.coherent {0, 1, 2, 3, 4} (by decide +kernel) {0, 1, 2, 3, 5} (by decide +kernel) (by decide +kernel)
    {0, 1, 2, 3} (by decide +kernel) (by decide +kernel) (by decide +kernel)) (by decide +kernel)

/-- The six-vertex real projective plane: ten triangles on the vertices `0, …, 5`. -/
def rp2 : Finset (Finset (Fin 8)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {0, 4, 5}, {0, 1, 5}, {1, 2, 4}, {2, 3, 5}, {1, 3, 4},
    {2, 4, 5}, {1, 3, 5}}

/-- The join of the edge `67` with the real projective plane `rp2`: ten 4-simplices. -/
def joinRP2 : Complex4 (Fin 8) where
  simps := rp2.image fun T => T ∪ {6, 7}
  card_eq := by decide +kernel

/-- `rp2` is a closed pseudo-surface, and `joinRP2` is a pseudo-manifold with boundary and
Euler characteristic 1 (it is a cone). -/
theorem joinRP2_checks : (∀ e ∈ rp2.biUnion (powersetCard 2), #(rp2.filter (e ⊆ ·)) = 2) ∧
    joinRP2.IsPseudo4 ∧ ¬ joinRP2.IsClosed4 ∧ joinRP2.euler4 = 1 := by
  unfold IsPseudo4 IsClosed4
  decide +kernel

/-- One coherence condition with the incidence numbers evaluated. -/
lemma coherent_eval {V : Type*} [LinearOrder V] {K : Complex4 V} {o : Finset V → ℤ}
    (ho : K.IsOrientation o) {s s' t : Finset V} {a b : ℤ} (hs : s ∈ K.simps)
    (hs' : s' ∈ K.simps) (hne : s ≠ s') (ht : t ∈ K.tets) (hts : t ⊆ s) (hts' : t ⊆ s')
    (ha : relSign s t = a) (hb : relSign s' t = b) : o s * a = -(o s' * b) :=
  ha ▸ hb ▸ ho.coherent s hs s' hs' hne t ht hts hts'

/-- **The join of an edge with the real projective plane is not orientable**: going around the
five 4-simplices `T ∪ {6, 7}` for the triangles `T = 012, 124, 134, 034, 023` (a Möbius band in
`rp2`) reverses the orientation. -/
theorem joinRP2_not_orientable : ¬ joinRP2.IsOrientable := by
  rintro ⟨o, ho⟩
  have h1 := coherent_eval ho (s := {0, 1, 2, 6, 7}) (s' := {1, 2, 4, 6, 7}) (t := {1, 2, 6, 7})
    (a := 1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h2 := coherent_eval ho (s := {1, 2, 4, 6, 7}) (s' := {1, 3, 4, 6, 7}) (t := {1, 4, 6, 7})
    (a := -1) (b := -1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h3 := coherent_eval ho (s := {0, 1, 2, 6, 7}) (s' := {0, 2, 3, 6, 7}) (t := {0, 2, 6, 7})
    (a := -1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h4 := coherent_eval ho (s := {0, 2, 3, 6, 7}) (s' := {0, 3, 4, 6, 7}) (t := {0, 3, 6, 7})
    (a := -1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have h5 := coherent_eval ho (s := {1, 3, 4, 6, 7}) (s' := {0, 3, 4, 6, 7}) (t := {3, 4, 6, 7})
    (a := 1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have hs := ho.sign {0, 1, 2, 6, 7} (by decide +kernel)
  omega

/-- **The boundary has no boundary (mod 2), on a complex with boundary**: in `joinRP2` every
triangle lies in an even number of boundary tetrahedra, and some triangle in two of them. -/
theorem joinRP2_even_bdry : (∀ f ∈ joinRP2.tris, Even #(joinRP2.bdryTets.filter (f ⊆ ·))) ∧
    #(joinRP2.bdryTets.filter (({0, 1, 6} : Finset (Fin 8)) ⊆ ·)) = 2 := by
  decide +kernel

/-- **The induced orientation of the boundary of a 4-simplex** is the textbook
`∂[01234] = [1234] - [0234] + [0134] - [0124] + [0123]`. -/
theorem delta4_bdryOrient :
    (delta4.bdryOrient 1 {1, 2, 3, 4}, delta4.bdryOrient 1 {0, 2, 3, 4},
      delta4.bdryOrient 1 {0, 1, 3, 4}, delta4.bdryOrient 1 {0, 1, 2, 4},
      delta4.bdryOrient 1 {0, 1, 2, 3}) = (1, -1, 1, -1, 1) := by
  decide +kernel

/-! ## Junk values -/

/-- **The hypothesis `#S = 6` is needed**: the 5-element subsets of a 7-element set are not a
pseudo-manifold (every tetrahedron lies in three of them). -/
theorem sphere7_not_pseudo : ¬ (sphere (univ : Finset (Fin 7))).IsPseudo4 := by
  unfold IsPseudo4
  decide +kernel

/-- The empty complex. -/
def empty4 : Complex4 (Fin 1) where
  simps := ∅
  card_eq := by decide +kernel

/-- **The empty complex is closed and orientable only vacuously**; its Euler characteristic `0`
tells it apart from the 4-sphere. -/
theorem empty4_checks : empty4.IsClosed4 ∧ empty4.IsOrientable ∧ empty4.euler4 = 0 := by
  refine ⟨fun t ht => by simp [empty4, faces] at ht,
    ⟨fun _ => 1, ⟨fun s hs => by simp [empty4] at hs, fun s hs => by simp [empty4] at hs⟩⟩,
    by decide +kernel⟩

end Lightlike.FourD.Tests
