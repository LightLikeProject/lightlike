import Lightlike.Regge.Complex

/-!
# Flat geometry has zero deficit angles

If the vertices of a triangulation are placed in Euclidean space and the edge lengths are the
distances, the geometry is flat, and the deficit angle at every interior edge must vanish. This file
proves that for an edge `ab` whose tetrahedra wind once around it.

Cylindrical coordinates around the edge describe the situation. Take an orthonormal triple
`e₀, e₁, e₂` with `x b = x a + L • e₀` (`L > 0`), and write the other vertices of the tetrahedra
around `ab` as

  `x (w i) = x a + z_i • e₀ + ρ_i • (cos α_i • e₁ + sin α_i • e₂)`,  `ρ_i > 0`,

where the tetrahedra around `ab` are `{a, b, w i, w (i+1)}` for `i < n`. Every point of a 3-space
off the line `ab` has this form. The hypotheses are that the angles `α_i` increase, by at most `π`
at each step, and make exactly one full turn: `α_n = α_0 + 2π`. This says that the tetrahedra
around the edge follow each other in order and fill the full angle around it once, as they do in
a triangulation of a region of space.

## Main results

* `dihedral_eq_of_cyl`: the dihedral angle at `ab` of the tetrahedron with link vertices at angles
  `α ≤ α' ≤ α + π` is `α' - α`.
* `sum_dihedral_cyl_eq_two_pi`: the dihedral angles around the edge add up to `2π`.
* `deficit_eq_zero_of_cyl`: for a triangulation placed in space this way, the deficit angle of
  the edge `ab` is zero. More generally, if the angles turn by `T` in total, the deficit is
  `2π - T` (`deficit_eq_of_cyl`).

The winding hypothesis is derived from geometry (non-degenerate tetrahedra with disjoint interiors)
in `Lightlike/Regge/Embedded.lean`.

The hypotheses are not vacuous: `Lightlike/Regge/Tests.lean` applies the last theorem to an
octahedron split into four tetrahedra around an axis.
-/

open Real Finset InnerProductGeometry InnerProductSpace

namespace Lightlike.Regge

open Lightlike.PR (Complex3 dihedral)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The six conditions contained in `Orthonormal ℝ ![e₀, e₁, e₂]`. -/
theorem orthonormal_three {e₀ e₁ e₂ : E} (h : Orthonormal ℝ ![e₀, e₁, e₂]) :
    ‖e₀‖ = 1 ∧ ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ ⟪e₁, e₀⟫_ℝ = 0 ∧ ⟪e₂, e₀⟫_ℝ = 0 ∧ ⟪e₁, e₂⟫_ℝ = 0 :=
  ⟨by simpa using h.1 0, by simpa using h.1 1, by simpa using h.1 2,
    by simpa using h.2 (show (1 : Fin 3) ≠ 0 by decide),
    by simpa using h.2 (show (2 : Fin 3) ≠ 0 by decide),
    by simpa using h.2 (show (1 : Fin 3) ≠ 2 by decide)⟩

/-- The angle between the unit vectors `cos α • e₁ + sin α • e₂` and `cos β • e₁ + sin β • e₂` of
the plane spanned by orthonormal `e₁, e₂` is `arccos (cos (β - α))`, for all `α, β`. -/
theorem angle_planeDir_eq_arccos {e₁ e₂ : E} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0) (α β : ℝ) :
    angle (cos α • e₁ + sin α • e₂) (cos β • e₁ + sin β • e₂) = arccos (cos (β - α)) := by
  have hin : ∀ γ δ : ℝ,
      ⟪cos γ • e₁ + sin γ • e₂, cos δ • e₁ + sin δ • e₂⟫_ℝ = cos (δ - γ) := by
    intro γ δ
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, h₁, h₂, h₁₂, real_inner_comm e₁ e₂, cos_sub]
    ring
  have hn : ∀ γ : ℝ, ‖cos γ • e₁ + sin γ • e₂‖ = 1 := by
    intro γ
    have h2 : ‖cos γ • e₁ + sin γ • e₂‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hin, sub_self, cos_zero]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  rw [angle, hin, hn, hn, mul_one, div_one]

/-- The unit vectors `cos α • e₁ + sin α • e₂` of the plane spanned by orthonormal `e₁, e₂` at
angles `α ≤ β ≤ α + π` enclose the angle `β - α`. -/
theorem angle_planeDir {e₁ e₂ : E} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (h₁₂ : ⟪e₁, e₂⟫_ℝ = 0)
    {α β : ℝ} (h : α ≤ β) (h' : β ≤ α + π) :
    angle (cos α • e₁ + sin α • e₂) (cos β • e₁ + sin β • e₂) = β - α := by
  rw [angle_planeDir_eq_arccos h₁ h₂ h₁₂, arccos_cos (by linarith) (by linarith)]

/-- The component orthogonal to the edge direction `L • e₀` of a point given in cylindrical
coordinates `z • e₀ + ρ • (cos α • e₁ + sin α • e₂)` is its radial part. -/
theorem perp_cyl {e₀ e₁ e₂ : E} (h₀ : ‖e₀‖ = 1) (h₁₀ : ⟪e₁, e₀⟫_ℝ = 0) (h₂₀ : ⟪e₂, e₀⟫_ℝ = 0)
    {L : ℝ} (hL : L ≠ 0) (z ρ α : ℝ) :
    perp (L • e₀) (z • e₀ + ρ • (cos α • e₁ + sin α • e₂)) = ρ • (cos α • e₁ + sin α • e₂) := by
  have hin : ⟪z • e₀ + ρ • (cos α • e₁ + sin α • e₂), L • e₀⟫_ℝ = L * z := by
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, h₀, h₁₀, h₂₀]
    ring
  have hn : ‖L • e₀‖ ^ 2 = L ^ 2 := by rw [norm_smul, h₀, mul_one, Real.norm_eq_abs, sq_abs]
  rw [perp, hin, hn, smul_smul, show L * z / L ^ 2 * L = z by field_simp, add_sub_cancel_left]

/-- **Dihedral angle in cylindrical coordinates.** Let `q = p + L • e₀` and let `r, s` have
cylindrical coordinates `(z, ρ, α)` and `(z', ρ', α')` around the line `pq`. Then the dihedral
angle at the edge `pq` of the tetrahedron `pqrs`, computed from the six distances, is
`arccos (cos (α' - α))`. -/
theorem dihedral_cyl_eq_arccos {p q r s e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂])
    {L z ρ α z' ρ' α' : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hρ' : 0 < ρ') (hq : q = p + L • e₀)
    (hr : r = p + z • e₀ + ρ • (cos α • e₁ + sin α • e₂))
    (hs : s = p + z' • e₀ + ρ' • (cos α' • e₁ + sin α' • e₂)) :
    dihedral (dist p q) (dist p r) (dist q r) (dist p s) (dist q s) (dist r s) =
      arccos (cos (α' - α)) := by
  obtain ⟨h₀, h₁, h₂, h₁₀, h₂₀, h₁₂⟩ := orthonormal_three horth
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    simp at h₀
  have hpq : p ≠ q := by
    rw [hq]
    intro hc
    simp [hL.ne', he₀] at hc
  rw [dihedral_dist hpq]
  subst hq hr hs
  simp only [add_assoc, add_sub_cancel_left]
  rw [perp_cyl h₀ h₁₀ h₂₀ hL.ne', perp_cyl h₀ h₁₀ h₂₀ hL.ne', angle_smul_left_of_pos _ _ hρ,
    angle_smul_right_of_pos _ _ hρ', angle_planeDir_eq_arccos h₁ h₂ h₁₂]

/-- **Dihedral angle in cylindrical coordinates, ordered link.** As
`dihedral_cyl_eq_arccos`, with `α ≤ α' ≤ α + π`: the dihedral angle is `α' - α`. -/
theorem dihedral_eq_of_cyl {p q r s e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂])
    {L z ρ α z' ρ' α' : ℝ} (hL : 0 < L) (hρ : 0 < ρ) (hρ' : 0 < ρ') (hq : q = p + L • e₀)
    (hr : r = p + z • e₀ + ρ • (cos α • e₁ + sin α • e₂))
    (hs : s = p + z' • e₀ + ρ' • (cos α' • e₁ + sin α' • e₂)) (h : α ≤ α') (h' : α' ≤ α + π) :
    dihedral (dist p q) (dist p r) (dist q r) (dist p s) (dist q s) (dist r s) = α' - α := by
  rw [dihedral_cyl_eq_arccos horth hL hρ hρ' hq hr hs, arccos_cos (by linarith) (by linarith)]

/-- **Dihedral angles around an edge, summed.** Let `q = p + L • e₀` and let `r 0, …, r n` have
cylindrical coordinates `(z i, ρ i, α i)` around the line `pq`, the angles increasing by at most
`π` at each step, with total turn `α n - α 0 = T`. Then the dihedral angles at `pq` of the
tetrahedra `p q (r i) (r (i+1))`, `i < n`, add up to `T`. -/
theorem sum_dihedral_cyl_eq {p q e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂])
    {L : ℝ} (hL : 0 < L) (hq : q = p + L • e₀) (n : ℕ) (r : ℕ → E) (z ρ α : ℕ → ℝ)
    (hρ : ∀ i ≤ n, 0 < ρ i)
    (hr : ∀ i ≤ n, r i = p + z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂))
    (hstep : ∀ i < n, α i ≤ α (i + 1) ∧ α (i + 1) ≤ α i + π) {T : ℝ} (hturn : α n = α 0 + T) :
    ∑ i ∈ range n, dihedral (dist p q) (dist p (r i)) (dist q (r i)) (dist p (r (i + 1)))
      (dist q (r (i + 1))) (dist (r i) (r (i + 1))) = T := by
  have hterm : ∀ i ∈ range n, dihedral (dist p q) (dist p (r i)) (dist q (r i))
      (dist p (r (i + 1))) (dist q (r (i + 1))) (dist (r i) (r (i + 1))) = α (i + 1) - α i := by
    intro i hi
    have hi' := mem_range.mp hi
    exact dihedral_eq_of_cyl horth hL (hρ i hi'.le) (hρ (i + 1) hi') hq (hr i hi'.le)
      (hr (i + 1) hi') (hstep i hi').1 (hstep i hi').2
  rw [sum_congr rfl hterm, sum_range_sub, hturn]
  ring

/-- **The dihedral angles around an edge of flat space add up to `2π`.** Let `q = p + L • e₀` and
let `r 0, …, r n` have cylindrical coordinates `(z i, ρ i, α i)` around the line `pq`, the angles
increasing by at most `π` at each step and making one full turn, `α n = α 0 + 2π`. Then the
dihedral angles at `pq` of the tetrahedra `p q (r i) (r (i+1))`, `i < n`, add up to `2π`. -/
theorem sum_dihedral_cyl_eq_two_pi {p q e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂])
    {L : ℝ} (hL : 0 < L) (hq : q = p + L • e₀) (n : ℕ) (r : ℕ → E) (z ρ α : ℕ → ℝ)
    (hρ : ∀ i ≤ n, 0 < ρ i)
    (hr : ∀ i ≤ n, r i = p + z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂))
    (hstep : ∀ i < n, α i ≤ α (i + 1) ∧ α (i + 1) ≤ α i + π) (hturn : α n = α 0 + 2 * π) :
    ∑ i ∈ range n, dihedral (dist p q) (dist p (r i)) (dist q (r i)) (dist p (r (i + 1)))
      (dist q (r (i + 1))) (dist (r i) (r (i + 1))) = 2 * π :=
  sum_dihedral_cyl_eq horth hL hq n r z ρ α hρ hr hstep hturn

variable {V : Type*} [DecidableEq V]

/-- **Deficit of a placement winding by `T`.** Let the vertices of `K` be placed in a real inner
product space by `x`, with the induced edge lengths. Suppose the tetrahedra of `K` around the edge
`ab` are exactly the `n` distinct tetrahedra `{a, b, w i, w (i+1)}`, `i < n`, and that in
cylindrical coordinates around the line through `x a` and `x b = x a + L • e₀` the link vertices
`w 0, …, w n` have angles increasing by at most `π` at each step, with total turn `T`. Then the
deficit angle at `ab` is `2π - T`. -/
theorem deficit_eq_of_cyl (K : Complex3 V) (x : V → E) {a b : V} (n : ℕ) (w : ℕ → V)
    (hstar : star K {a, b} = (range n).image fun i => {a, b, w i, w (i + 1)})
    (hinj : Set.InjOn (fun i => ({a, b, w i, w (i + 1)} : Finset V)) (range n))
    (hdist : ∀ i < n, a ≠ w i ∧ a ≠ w (i + 1) ∧ b ≠ w i ∧ b ≠ w (i + 1) ∧ w i ≠ w (i + 1))
    {e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂]) {L : ℝ} (hL : 0 < L)
    (hb : x b = x a + L • e₀) (z ρ α : ℕ → ℝ) (hρ : ∀ i ≤ n, 0 < ρ i)
    (hx : ∀ i ≤ n, x (w i) = x a + z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂))
    (hstep : ∀ i < n, α i ≤ α (i + 1) ∧ α (i + 1) ≤ α i + π) {T : ℝ} (hturn : α n = α 0 + T) :
    deficit K (ofDist fun u v => dist (x u) (x v)) {a, b} = 2 * π - T := by
  have hℓ : ∀ u v, u ≠ v → ofDist (fun u v => dist (x u) (x v)) {u, v} = dist (x u) (x v) :=
    fun u v h => ofDist_pair (d := fun u v => dist (x u) (x v)) (fun u => dist_self (x u))
      (fun u v => dist_comm (x u) (x v)) h
  have he₀ : e₀ ≠ 0 := by
    have h₀ := (orthonormal_three horth).1
    rintro rfl
    simp at h₀
  have hxab : x a ≠ x b := by
    rw [hb]
    intro hc
    simp [hL.ne', he₀] at hc
  have hab : a ≠ b := fun h => hxab (by rw [h])
  have hterm : ∀ i ∈ range n,
      dihedralAt (ofDist fun u v => dist (x u) (x v)) {a, b, w i, w (i + 1)} {a, b} =
        dihedral (dist (x a) (x b)) (dist (x a) (x (w i))) (dist (x b) (x (w i)))
          (dist (x a) (x (w (i + 1)))) (dist (x b) (x (w (i + 1))))
          (dist (x (w i)) (x (w (i + 1)))) := by
    intro i hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hdist i (mem_range.mp hi)
    rw [dihedralAt_eq _ hab h₁ h₂ h₃ h₄ h₅ (by rw [hℓ a b hab]; exact dist_ne_zero.mpr hxab),
      hℓ _ _ hab, hℓ _ _ h₁, hℓ _ _ h₃, hℓ _ _ h₂, hℓ _ _ h₄, hℓ _ _ h₅]
  rw [deficit, angleSum, hstar, sum_image hinj, sum_congr rfl hterm,
    sum_dihedral_cyl_eq horth hL hb n (fun i => x (w i)) z ρ α hρ hx hstep hturn]

/-- **Flat placements have zero deficit.** Let the vertices of `K` be placed in a real inner
product space by `x`, with the induced edge lengths. Suppose the tetrahedra of `K` around the edge
`ab` are exactly the `n` distinct tetrahedra `{a, b, w i, w (i+1)}`, `i < n`, and that in
cylindrical coordinates around the line through `x a` and `x b = x a + L • e₀` the link vertices
`w 0, …, w n` have angles increasing by at most `π` at each step and making one full turn. Then the
deficit angle at `ab` is zero. -/
theorem deficit_eq_zero_of_cyl (K : Complex3 V) (x : V → E) {a b : V} (n : ℕ) (w : ℕ → V)
    (hstar : star K {a, b} = (range n).image fun i => {a, b, w i, w (i + 1)})
    (hinj : Set.InjOn (fun i => ({a, b, w i, w (i + 1)} : Finset V)) (range n))
    (hdist : ∀ i < n, a ≠ w i ∧ a ≠ w (i + 1) ∧ b ≠ w i ∧ b ≠ w (i + 1) ∧ w i ≠ w (i + 1))
    {e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂]) {L : ℝ} (hL : 0 < L)
    (hb : x b = x a + L • e₀) (z ρ α : ℕ → ℝ) (hρ : ∀ i ≤ n, 0 < ρ i)
    (hx : ∀ i ≤ n, x (w i) = x a + z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂))
    (hstep : ∀ i < n, α i ≤ α (i + 1) ∧ α (i + 1) ≤ α i + π) (hturn : α n = α 0 + 2 * π) :
    deficit K (ofDist fun u v => dist (x u) (x v)) {a, b} = 0 := by
  rw [deficit_eq_of_cyl K x n w hstar hinj hdist horth hL hb z ρ α hρ hx hstep hturn, sub_self]

end Lightlike.Regge
