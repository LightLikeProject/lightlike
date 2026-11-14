import Lightlike.PonzanoRegge.Asymptotics

/-!
# Dihedral angles of a Euclidean tetrahedron from its edge lengths

Regge calculus describes a curved 3-geometry by a triangulation with a length on every edge. The
curvature sits on the edges and is measured by dihedral angles. The library already has a length
formula for the dihedral angle (`Lightlike.PR.cosDihedral`, `Lightlike.PR.dihedral` in
`Lightlike/PonzanoRegge/Asymptotics.lean`), checked there only on the regular tetrahedron. This file
checks it against Euclidean geometry for every tetrahedron and proves the properties that the
triangulation-level definitions in `Lightlike/Regge/Complex.lean` rely on.

## Main results

* `dihedral_dist`: for four points `p q r s` of a real inner product space with `p ≠ q`, the length
  formula applied to their six distances equals the angle between the components of `r - p` and
  `s - p` orthogonal to the edge direction `q - p`. That angle is the dihedral angle of the
  tetrahedron `pqrs` at its edge `pq` in the usual sense (`InnerProductGeometry.angle`).
* `cosDihedral_swap_rs`, `cosDihedral_swap_pq`: the formula does not depend on the order of the
  two opposite vertices, nor (for `pq ≠ 0`) on the order of the two edge vertices.
* `dihedral_smul`: dihedral angles are unchanged when all six lengths are scaled by `c > 0`.

The argument order is the one of `Lightlike.PR.cosDihedral`: `pq pr qr ps qs rs`.
-/

open Real InnerProductGeometry InnerProductSpace

namespace Lightlike.Regge

open Lightlike.PR (cosDihedral dihedral)

/-! ## Symmetries and scaling of the length formula -/

/-- The length formula is symmetric under exchanging the two vertices `r, s` opposite the edge. -/
theorem cosDihedral_swap_rs (pq pr qr ps qs rs : ℝ) :
    cosDihedral pq pr qr ps qs rs = cosDihedral pq ps qs pr qr rs := by
  simp only [cosDihedral]
  ring_nf

/-- The length formula is symmetric under exchanging the two vertices `p, q` of the edge, provided
the edge length is nonzero. (For `pq = 0` the formula divides by zero and the symmetry fails.) -/
theorem cosDihedral_swap_pq {pq : ℝ} (h : pq ≠ 0) (pr qr ps qs rs : ℝ) :
    cosDihedral pq pr qr ps qs rs = cosDihedral pq qr pr qs ps rs := by
  simp only [cosDihedral]
  congr 1
  · field_simp
    ring
  · congr 1
    field_simp
    ring

/-- The dihedral angle is symmetric under exchanging the two vertices opposite the edge. -/
theorem dihedral_swap_rs (pq pr qr ps qs rs : ℝ) :
    dihedral pq pr qr ps qs rs = dihedral pq ps qs pr qr rs := by
  rw [dihedral, cosDihedral_swap_rs, dihedral]

/-- The dihedral angle is symmetric under exchanging the two vertices of the edge, for a nonzero
edge length. -/
theorem dihedral_swap_pq {pq : ℝ} (h : pq ≠ 0) (pr qr ps qs rs : ℝ) :
    dihedral pq pr qr ps qs rs = dihedral pq qr pr qs ps rs := by
  rw [dihedral, cosDihedral_swap_pq h, dihedral]

/-- Scaling all six lengths by `c > 0` does not change the cosine of the dihedral angle. -/
theorem cosDihedral_smul {c : ℝ} (hc : 0 < c) (pq pr qr ps qs rs : ℝ) :
    cosDihedral (c * pq) (c * pr) (c * qr) (c * ps) (c * qs) (c * rs) =
      cosDihedral pq pr qr ps qs rs := by
  have key : ∀ x y : ℝ, ((c * x) ^ 2 + (c * pq) ^ 2 - (c * y) ^ 2) / (2 * (c * pq)) =
      c * ((x ^ 2 + pq ^ 2 - y ^ 2) / (2 * pq)) := by
    intro x y
    rw [show (c * x) ^ 2 + (c * pq) ^ 2 - (c * y) ^ 2 = c * (c * (x ^ 2 + pq ^ 2 - y ^ 2)) by ring,
      show 2 * (c * pq) = c * (2 * pq) by ring, mul_div_mul_left _ _ hc.ne', mul_div_assoc]
  simp only [cosDihedral, key]
  generalize (pr ^ 2 + pq ^ 2 - qr ^ 2) / (2 * pq) = ru
  generalize (ps ^ 2 + pq ^ 2 - qs ^ 2) / (2 * pq) = su
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc.ne'
  rw [show ((c * pr) ^ 2 + (c * ps) ^ 2 - (c * rs) ^ 2) / 2 - c * ru * (c * su) =
      c ^ 2 * ((pr ^ 2 + ps ^ 2 - rs ^ 2) / 2 - ru * su) by ring,
    show ((c * pr) ^ 2 - (c * ru) ^ 2) * ((c * ps) ^ 2 - (c * su) ^ 2) =
      (c ^ 2) ^ 2 * ((pr ^ 2 - ru ^ 2) * (ps ^ 2 - su ^ 2)) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_div_mul_left _ _ hc2]

/-- Dihedral angles are scale invariant: scaling all six lengths by `c > 0` does not change them. -/
theorem dihedral_smul {c : ℝ} (hc : 0 < c) (pq pr qr ps qs rs : ℝ) :
    dihedral (c * pq) (c * pr) (c * qr) (c * ps) (c * qs) (c * rs) =
      dihedral pq pr qr ps qs rs := by
  rw [dihedral, cosDihedral_smul hc, dihedral]

/-- The dihedral angle lies in `[0, π]` (it is an `arccos`). -/
theorem dihedral_mem_Icc (pq pr qr ps qs rs : ℝ) :
    dihedral pq pr qr ps qs rs ∈ Set.Icc 0 π :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-! ## The length formula agrees with Euclidean geometry -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component of `a` orthogonal to `v`, namely `a - (⟪a, v⟫ / ‖v‖²) • v`. For `v = q - p` and
`a = r - p` it is the perpendicular dropped from `r` onto the line `pq`, so the dihedral angle at
the edge `pq` of the tetrahedron `pqrs` is the angle between `perp (q - p) (r - p)` and
`perp (q - p) (s - p)`. -/
noncomputable def perp (v a : E) : E := a - (⟪a, v⟫_ℝ / ‖v‖ ^ 2) • v

/-- `perp v a` is orthogonal to `v`. -/
theorem inner_perp_self (v a : E) : ⟪perp v a, v⟫_ℝ = 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  simp only [perp, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- Inner product of two perpendicular components: `⟪a, b⟫ - ⟪a, v⟫ ⟪b, v⟫ / ‖v‖²`. -/
theorem inner_perp_perp {v : E} (hv : v ≠ 0) (a b : E) :
    ⟪perp v a, perp v b⟫_ℝ = ⟪a, b⟫_ℝ - ⟪a, v⟫_ℝ * ⟪b, v⟫_ℝ / ‖v‖ ^ 2 := by
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  simp only [perp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm b v]
  field_simp
  ring

/-- **The length formula is Euclidean.** For points `p ≠ q`, `r`, `s` of a real inner product
space, `Lightlike.PR.cosDihedral` of the six distances is the cosine of the angle between the
perpendiculars dropped from `r` and from `s` onto the line `pq`. -/
theorem cosDihedral_dist {p q r s : E} (hpq : p ≠ q) :
    cosDihedral (dist p q) (dist p r) (dist q r) (dist p s) (dist q s) (dist r s) =
      ⟪perp (q - p) (r - p), perp (q - p) (s - p)⟫_ℝ /
        (‖perp (q - p) (r - p)‖ * ‖perp (q - p) (s - p)‖) := by
  have hv : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have h1 : dist p q = ‖q - p‖ := by rw [dist_comm, dist_eq_norm]
  have h2 : dist p r = ‖r - p‖ := by rw [dist_comm, dist_eq_norm]
  have h3 : dist q r = ‖(r - p) - (q - p)‖ := by
    rw [dist_comm, dist_eq_norm, sub_sub_sub_cancel_right]
  have h4 : dist p s = ‖s - p‖ := by rw [dist_comm, dist_eq_norm]
  have h5 : dist q s = ‖(s - p) - (q - p)‖ := by
    rw [dist_comm, dist_eq_norm, sub_sub_sub_cancel_right]
  have h6 : dist r s = ‖(r - p) - (s - p)‖ := by rw [dist_eq_norm, sub_sub_sub_cancel_right]
  rw [h1, h2, h3, h4, h5, h6]
  generalize q - p = v at hv ⊢
  generalize r - p = a
  generalize s - p = b
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hru : ∀ x : E, (‖x‖ ^ 2 + ‖v‖ ^ 2 - ‖x - v‖ ^ 2) / (2 * ‖v‖) = ⟪x, v⟫_ℝ / ‖v‖ := by
    intro x
    rw [norm_sub_sq_real]
    field_simp
    ring
  have hperp : ∀ x : E, ‖perp v x‖ ^ 2 = ‖x‖ ^ 2 - (⟪x, v⟫_ℝ / ‖v‖) ^ 2 := by
    intro x
    rw [← real_inner_self_eq_norm_sq, inner_perp_perp hv, real_inner_self_eq_norm_sq]
    field_simp
  simp only [cosDihedral, hru]
  rw [← hperp a, ← hperp b, ← mul_pow, Real.sqrt_sq (by positivity), inner_perp_perp hv,
    norm_sub_sq_real a b]
  congr 1
  field_simp
  ring

/-- **The dihedral angle from lengths is the Euclidean dihedral angle.** For points `p ≠ q`, `r`,
`s` of a real inner product space, `Lightlike.PR.dihedral` of the six distances is the angle
(`InnerProductGeometry.angle`) between the perpendiculars dropped from `r` and `s` onto the line
`pq`. -/
theorem dihedral_dist {p q r s : E} (hpq : p ≠ q) :
    dihedral (dist p q) (dist p r) (dist q r) (dist p s) (dist q s) (dist r s) =
      angle (perp (q - p) (r - p)) (perp (q - p) (s - p)) := by
  rw [dihedral, cosDihedral_dist hpq, angle]

end Euclidean

end Lightlike.Regge
