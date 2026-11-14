import Lightlike.Regge.Dihedral
import Lightlike.PonzanoRegge.Amplitude

/-!
# Deficit angles and the Regge action of a triangulation

A **Regge geometry** on a 3-dimensional triangulation is an assignment of a length to every edge,
each tetrahedron being a flat Euclidean tetrahedron with those lengths. Curvature is concentrated
on the edges: around an interior edge `e` the dihedral angles `θ_t(e)` of the tetrahedra `t ∋ e`
add up to `2π` exactly when the geometry is flat there, and the **deficit angle**
`δ_e = 2π - Σ_{t ∋ e} θ_t(e)` measures the curvature (Regge, *Nuovo Cimento* 19 (1961) 558). The
**Regge action** is the discrete Einstein–Hilbert action `Σ_e ℓ_e δ_e`; for a triangulation with
boundary it is completed by the boundary term `Σ_{e ∈ ∂} ℓ_e (π - Σ_{t ∋ e} θ_t(e))`
(Hartle–Sorkin, *Gen. Rel. Grav.* 13 (1981) 541). Both are written without the factor `1/(8πG)`.

## Definitions

Triangulations are `Lightlike.PR.Complex3 V` (tetrahedra as 4-element vertex sets, as for the
Ponzano–Regge amplitude), and lengths are functions `ℓ : Finset V → ℝ` read on 2-element sets,
in the same way as the colourings of `PonzanoRegge/`.

* `ofDist d`: the lengths induced by a distance function on the vertices, e.g. by a placement of
  the vertices in Euclidean space.
* `angleAvg F ℓ t e`: an angle formula `F` in the six lengths, applied to the tetrahedron `t` at
  its edge `e` and averaged over the labellings of the vertices, so that no labelling is chosen.
* `dihedralAt ℓ t e = angleAvg dihedral ℓ t e`: the dihedral angle of `t` at `e`, by the length
  formula `Lightlike.PR.dihedral` (checked against Euclidean geometry in
  `Lightlike/Regge/Dihedral.lean`).
* `star K e`, `angleSum K ℓ e`: the tetrahedra containing `e`, and the sum of their dihedral
  angles at `e`.
* `deficit K ℓ e = 2π - angleSum`, `bdryAngle K ℓ e = π - angleSum`.
* `bdryTris K`: triangles in exactly one tetrahedron; `bdryEdges K`: edges of boundary triangles;
  `intEdges K`: the other edges. No manifold condition is imposed.
* `reggeAction K ℓ = Σ_{e interior} ℓ_e δ_e + Σ_{e boundary} ℓ_e (π - Σ θ)`.

## Main results

* `dihedralAt_eq`: for `t = {p, q, r, s}` and `e = {p, q}` the angle is the length formula with
  this labelling, whatever labelling of `e` and `t \ e` is used.
* `deficit_smul`, `reggeAction_smul`: deficit angles are scale invariant and the Regge action is
  homogeneous of degree one, `S(cℓ) = c S(ℓ)` for `c > 0`.
* `deficit_const`: with all lengths equal to `a`, an edge in `n` tetrahedra has
  `δ = 2π - n · dihedral a a a a a a`.
-/

open Real Finset

namespace Lightlike.Regge

open Lightlike.PR (Complex3 dihedral)

variable {V : Type*} [DecidableEq V]

/-! ## Lengths and dihedral angles -/

/-- The lengths induced by a distance function `d` on the vertices: a vertex set `e` gets
`(Σ_{a ∈ e} Σ_{b ∈ e} d a b) / 2`. For an edge `e = {a, b}` with `a ≠ b` and `d` symmetric and zero
on the diagonal this is `d a b` (`ofDist_pair`); only edges are ever evaluated. -/
noncomputable def ofDist (d : V → V → ℝ) (e : Finset V) : ℝ := (∑ a ∈ e, ∑ b ∈ e, d a b) / 2

/-- `ofDist d` gives an edge `{a, b}` the length `d a b`. -/
theorem ofDist_pair {d : V → V → ℝ} (hd : ∀ a, d a a = 0) (hs : ∀ a b, d a b = d b a)
    {a b : V} (h : a ≠ b) : ofDist d {a, b} = d a b := by
  simp only [ofDist, sum_pair h, hd, hs b a]
  ring

/-- The angle of the tetrahedron `t` at its edge `e` according to a formula `F` in the six
lengths, taken in the order `pq pr qr ps qs rs` of `Lightlike.PR.cosDihedral`, for `e = {p, q}` and
`t \ e = {r, s}`. The formula is averaged over the four orderings of `e` and of `t \ e`, so that
no labelling of the vertices has to be chosen (`angleAvg_eq`). With `F = Lightlike.PR.dihedral` this is
`dihedralAt`; `Lightlike/Regge/Tests.lean` uses other `F` to show that wrong angle formulas fail. -/
noncomputable def angleAvg (F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (ℓ : Finset V → ℝ)
    (t e : Finset V) : ℝ :=
  (∑ p ∈ e, ∑ q ∈ e.erase p, ∑ r ∈ t \ e, ∑ s ∈ (t \ e).erase r,
    F (ℓ {p, q}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {r, s})) / 4

/-- For the tetrahedron `{p, q, r, s}` and its edge `{p, q}` (distinct vertices), `angleAvg F` is
the average of `F` over the four labellings `pqrs`, `pqsr`, `qprs`, `qpsr`. -/
theorem angleAvg_eq (F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (ℓ : Finset V → ℝ) {p q r s : V}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    angleAvg F ℓ {p, q, r, s} {p, q} =
      (F (ℓ {p, q}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {r, s}) +
        F (ℓ {p, q}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {r, s}) +
        F (ℓ {p, q}) (ℓ {q, r}) (ℓ {p, r}) (ℓ {q, s}) (ℓ {p, s}) (ℓ {r, s}) +
        F (ℓ {p, q}) (ℓ {q, s}) (ℓ {p, s}) (ℓ {q, r}) (ℓ {p, r}) (ℓ {r, s})) / 4 := by
  have e1 : ({p, q, r, s} : Finset V) \ {p, q} = {r, s} := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · tauto
    · rintro (rfl | rfl) <;> simp_all [eq_comm]
  have ep : ({p, q} : Finset V).erase p = {q} := erase_insert (by simpa using hpq)
  have eq' : ({p, q} : Finset V).erase q = {p} := by
    rw [pair_comm]; exact erase_insert (by simpa using hpq.symm)
  have er : ({r, s} : Finset V).erase r = {s} := erase_insert (by simpa using hrs)
  have es : ({r, s} : Finset V).erase s = {r} := by
    rw [pair_comm]; exact erase_insert (by simpa using hrs.symm)
  simp only [angleAvg, e1, sum_pair hpq, ep, eq', sum_singleton, sum_pair hrs, er, es]
  rw [pair_comm q p, pair_comm s r]
  ring

/-- The interior dihedral angle of the tetrahedron `t` at its edge `e`, computed from the lengths
`ℓ` by `Lightlike.PR.dihedral`: `angleAvg dihedral`. For `t = {p, q, r, s}` and `e = {p, q}` it is
`dihedral ℓ{p,q} ℓ{p,r} ℓ{q,r} ℓ{p,s} ℓ{q,s} ℓ{r,s}` (`dihedralAt_eq`), since by
`cosDihedral_swap_pq` and `cosDihedral_swap_rs` the four averaged terms agree. -/
noncomputable def dihedralAt (ℓ : Finset V → ℝ) (t e : Finset V) : ℝ := angleAvg dihedral ℓ t e

/-- The dihedral angle of the tetrahedron `{p, q, r, s}` at its edge `{p, q}` is given by the
length formula with this labelling (for distinct vertices and a nonzero length of `pq`). -/
theorem dihedralAt_eq (ℓ : Finset V → ℝ) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (h : ℓ {p, q} ≠ 0) :
    dihedralAt ℓ {p, q, r, s} {p, q} =
      dihedral (ℓ {p, q}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {r, s}) := by
  rw [dihedralAt, angleAvg_eq _ _ hpq hpr hps hqr hqs hrs]
  have h2 := dihedral_swap_rs (ℓ {p, q}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {r, s})
  have h3 := dihedral_swap_pq h (ℓ {p, r}) (ℓ {q, r}) (ℓ {p, s}) (ℓ {q, s}) (ℓ {r, s})
  have h4 := dihedral_swap_pq h (ℓ {p, s}) (ℓ {q, s}) (ℓ {p, r}) (ℓ {q, r}) (ℓ {r, s})
  rw [← h4, ← h2, ← h3]
  ring

/-- Scaling all lengths by `c > 0` does not change any dihedral angle. -/
theorem dihedralAt_smul {c : ℝ} (hc : 0 < c) (ℓ : Finset V → ℝ) (t e : Finset V) :
    dihedralAt (fun f => c * ℓ f) t e = dihedralAt ℓ t e := by
  simp only [dihedralAt, angleAvg, dihedral_smul hc]

/-! ## Deficit angles and the Regge action -/

/-- The star of a vertex set `e` in `K`: the tetrahedra of `K` containing `e`. -/
def star (K : Complex3 V) (e : Finset V) : Finset (Finset V) := K.tets.filter (e ⊆ ·)

/-- The sum of the dihedral angles at `e` of the tetrahedra around it. -/
noncomputable def angleSum (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) : ℝ :=
  ∑ t ∈ star K e, dihedralAt ℓ t e

/-- The **deficit angle** `δ_e = 2π - Σ_{t ∋ e} θ_t(e)` at an edge `e`: zero where the geometry
around an interior edge is flat, positive for positive curvature. -/
noncomputable def deficit (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) : ℝ :=
  2 * π - angleSum K ℓ e

/-- The boundary angle `ψ_e = π - Σ_{t ∋ e} θ_t(e)` at a boundary edge `e`: the angle between the
outward normals of the two boundary triangles at `e`, zero where the boundary is flat. -/
noncomputable def bdryAngle (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) : ℝ :=
  π - angleSum K ℓ e

/-- The boundary triangles of `K`: triangles contained in exactly one tetrahedron. -/
def bdryTris (K : Complex3 V) : Finset (Finset V) := K.tris.filter (fun f => #(star K f) = 1)

/-- The boundary edges of `K`: edges of boundary triangles. -/
def bdryEdges (K : Complex3 V) : Finset (Finset V) :=
  K.edges.filter (fun e => ∃ f ∈ bdryTris K, e ⊆ f)

/-- The interior edges of `K`: edges contained in no boundary triangle. -/
def intEdges (K : Complex3 V) : Finset (Finset V) :=
  K.edges.filter (fun e => ¬ ∃ f ∈ bdryTris K, e ⊆ f)

/-- Every edge is either interior or on the boundary. -/
theorem intEdges_union_bdryEdges (K : Complex3 V) : intEdges K ∪ bdryEdges K = K.edges := by
  rw [union_comm]
  exact filter_union_filter_not_eq _ _

/-- No edge is both interior and on the boundary. -/
theorem disjoint_intEdges_bdryEdges (K : Complex3 V) : Disjoint (intEdges K) (bdryEdges K) :=
  (disjoint_filter_filter_not _ _ _).symm

/-- The **Regge action** of the lengths `ℓ` on `K` (without the factor `1/(8πG)`):
`Σ_{e interior} ℓ_e δ_e + Σ_{e boundary} ℓ_e ψ_e`, the interior term of Regge (1961) plus the
boundary term of Hartle and Sorkin (1981). For a closed triangulation only the first sum is
present (`reggeAction_of_bdryTris_eq_empty`). -/
noncomputable def reggeAction (K : Complex3 V) (ℓ : Finset V → ℝ) : ℝ :=
  ∑ e ∈ intEdges K, ℓ e * deficit K ℓ e + ∑ e ∈ bdryEdges K, ℓ e * bdryAngle K ℓ e

/-- Without boundary triangles every edge is interior. -/
theorem intEdges_of_bdryTris_eq_empty {K : Complex3 V} (h : bdryTris K = ∅) :
    intEdges K = K.edges := by
  simp [intEdges, h]

/-- For a closed triangulation (no boundary triangles) the Regge action is `Σ_e ℓ_e δ_e`. -/
theorem reggeAction_of_bdryTris_eq_empty {K : Complex3 V} (h : bdryTris K = ∅)
    (ℓ : Finset V → ℝ) : reggeAction K ℓ = ∑ e ∈ K.edges, ℓ e * deficit K ℓ e := by
  simp [reggeAction, intEdges, bdryEdges, h]

/-- Deficit angles are scale invariant. -/
theorem deficit_smul {c : ℝ} (hc : 0 < c) (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) :
    deficit K (fun f => c * ℓ f) e = deficit K ℓ e := by
  simp only [deficit, angleSum, dihedralAt_smul hc]

/-- Boundary angles are scale invariant. -/
theorem bdryAngle_smul {c : ℝ} (hc : 0 < c) (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) :
    bdryAngle K (fun f => c * ℓ f) e = bdryAngle K ℓ e := by
  simp only [bdryAngle, angleSum, dihedralAt_smul hc]

/-- The Regge action is homogeneous of degree one in the lengths: `S(cℓ) = c S(ℓ)` for `c > 0`. -/
theorem reggeAction_smul {c : ℝ} (hc : 0 < c) (K : Complex3 V) (ℓ : Finset V → ℝ) :
    reggeAction K (fun f => c * ℓ f) = c * reggeAction K ℓ := by
  simp only [reggeAction, deficit_smul hc, bdryAngle_smul hc, mul_add, mul_sum, mul_assoc]

/-! ## Equal lengths -/

/-- The average of a constant formula is that constant, for an edge `e` (two vertices) of a
tetrahedron `t` (two further vertices). -/
theorem angleAvg_const (c : ℝ) (ℓ : Finset V → ℝ) {t e : Finset V} (he : #e = 2)
    (ht : #(t \ e) = 2) : angleAvg (fun _ _ _ _ _ _ => c) ℓ t e = c := by
  have inner : ∀ x ∈ t \ e, ∑ _s ∈ (t \ e).erase x, c = c := by
    intro x hx
    rw [sum_const, card_erase_of_mem hx, ht]
    simp
  have mid : ∀ x ∈ e, ∑ _q ∈ e.erase x, ∑ r ∈ t \ e, ∑ _s ∈ (t \ e).erase r, c = 2 * c := by
    intro x hx
    rw [sum_congr rfl fun _ _ => sum_congr rfl inner, sum_const, sum_const, card_erase_of_mem hx,
      he, ht]
    simp only [nsmul_eq_mul]
    norm_num
  simp only [angleAvg]
  rw [sum_congr rfl mid, sum_const, he]
  simp only [nsmul_eq_mul]
  ring

/-- `angleAvg` is linear in the formula: the average of `F - G` is the difference of averages. -/
theorem angleAvg_sub (F G : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (ℓ : Finset V → ℝ) (t e : Finset V) :
    angleAvg (fun a b c d f g => F a b c d f g - G a b c d f g) ℓ t e =
      angleAvg F ℓ t e - angleAvg G ℓ t e := by
  simp only [angleAvg, sum_sub_distrib, sub_div]

/-- With all lengths equal to `a`, every dihedral angle of a tetrahedron is `dihedral a a a a a a`
(for `a > 0` this is `arccos (1/3)`, `Lightlike.PR.cos_dihedral_regular`). -/
theorem dihedralAt_const (a : ℝ) {t e : Finset V} (he : #e = 2) (ht : #(t \ e) = 2) :
    dihedralAt (fun _ => a) t e = dihedral a a a a a a :=
  angleAvg_const (dihedral a a a a a a) (fun _ => a) he ht

/-- With all lengths equal to `a`, the deficit at an edge `e` of `K` lying in `n` tetrahedra is
`2π - n · dihedral a a a a a a`. -/
theorem deficit_const (K : Complex3 V) (a : ℝ) {e : Finset V} (he : #e = 2) :
    deficit K (fun _ => a) e = 2 * π - #(star K e) * dihedral a a a a a a := by
  have : ∀ t ∈ star K e, dihedralAt (fun _ => a) t e = dihedral a a a a a a := by
    intro t ht
    simp only [star, mem_filter] at ht
    apply dihedralAt_const a he
    rw [card_sdiff_of_subset ht.2, K.card_eq t ht.1, he]
  rw [deficit, angleSum, sum_congr rfl this, sum_const, nsmul_eq_mul]

/-- The vertices of a tetrahedron of `K` can be labelled `p, q, r, s`. -/
theorem exists_label {K : Complex3 V} {t : Finset V} (ht : t ∈ K.tets) :
    ∃ p q r s, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧ t = {p, q, r, s} := by
  obtain ⟨p, t', hp, rfl, h3⟩ := card_eq_succ.mp (K.card_eq t ht)
  obtain ⟨q, r, s, hqr, hqs, hrs, rfl⟩ := card_eq_three.mp h3
  simp only [mem_insert, mem_singleton, not_or] at hp
  exact ⟨p, q, r, s, hp.1, hp.2.1, hp.2.2, hqr, hqs, hrs, rfl⟩

end Lightlike.Regge
