import Lightlike.Regge.Flat
import Lightlike.Regge.Manifold
import Lightlike.Regge.Winding

/-!
# Triangulations of a region of space have zero deficit angles

`deficit_eq_zero_of_cyl` (`Lightlike/Regge/Flat.lean`) assumes that the tetrahedra around an edge
wind once around it. This file derives that from geometry: in a 3-dimensional Euclidean space, if
the tetrahedra around an interior edge are non-degenerate and their interiors are pairwise disjoint,
the deficit angle of the edge is zero.

The interior of the tetrahedron `pqrs` is handled as `openTet p q r s`, the points whose four
barycentric coordinates are all positive; for a non-degenerate tetrahedron in a 3-dimensional space
this is exactly the topological interior of its convex hull (`openTet_eq_interior`), which is how
`IsGeometric` states disjointness.

## Main results

* `deficit_eq_zero_of_embedded`: let `E` be a real inner product space of dimension 3 and `x` a
  placement of the vertices of `K` in `E`, with the induced edge lengths. Let the link of the edge
  `ab` be a cycle (`IsCycleLink`), each tetrahedron `{a, b, w i, w (i+1)}` around it non-degenerate,
  and their interiors pairwise disjoint. Then the deficit angle at `ab` is zero.

## Implementation notes

Put an orthonormal frame `e₀, e₁, e₂` with `x b - x a = L • e₀` (`exists_frame`) and write the link
vertices in cylindrical coordinates around the line `ab` (`cyl_repr`). The dihedral angle of the
tetrahedron `i` at `ab` is the angle between the directions `α i` and `α (i+1)`
(`dihedral_cyl_eq_arccos`). Points just off the middle of the edge in a direction strictly inside
that angle lie inside the tetrahedron (`mem_openTet_near`). So disjoint interiors make the wedges
between consecutive directions disjoint, and `sum_arccos_cos_eq_two_pi`
(`Lightlike/Regge/Winding.lean`) gives the angle sum `2π`.
-/

open Real Finset InnerProductGeometry InnerProductSpace Module

namespace Lightlike.Regge

open Lightlike.PR (Complex3 dihedral)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The open tetrahedron with vertices `p q r s`: the points `c₀ p + c₁ q + c₂ r + c₃ s` with all
four barycentric coordinates `cᵢ` positive. For a non-degenerate tetrahedron in a 3-dimensional
space this is its interior. -/
def openTet (p q r s : E) : Set E :=
  {y | ∃ c₀ c₁ c₂ c₃ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ c₀ + c₁ + c₂ + c₃ = 1 ∧
    y = c₀ • p + c₁ • q + c₂ • r + c₃ • s}

/-- **The open tetrahedron is the interior.** For four affinely independent points of a
3-dimensional real inner product space, `openTet` (the points with positive barycentric
coordinates) is the topological interior of their convex hull. -/
theorem openTet_eq_interior [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3) {p q r s : E}
    (h : AffineIndependent ℝ ![p, q, r, s]) :
    openTet p q r s = interior (convexHull ℝ {p, q, r, s}) := by
  have hspan : affineSpan ℝ (Set.range ![p, q, r, s]) = ⊤ :=
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hE])
  let b : AffineBasis (Fin 4) ℝ E := AffineBasis.mk _ h hspan
  have hb : ⇑b = ![p, q, r, s] := rfl
  have hrange : Set.range ![p, q, r, s] = ({p, q, r, s} : Set E) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
  rw [← hrange, ← hb, b.interior_convexHull]
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c₀, c₁, c₂, c₃, h₀, h₁, h₂, h₃, hsum, rfl⟩ i
    have hw : (Finset.univ : Finset (Fin 4)).sum ![c₀, c₁, c₂, c₃] = 1 := by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      linarith
    have key := b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, hb] at key
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at key
    rw [key]
    fin_cases i <;> simpa
  · intro hy
    refine ⟨b.coord 0 y, b.coord 1 y, b.coord 2 y, b.coord 3 y, hy 0, hy 1, hy 2, hy 3, ?_, ?_⟩
    · have := b.sum_coord_apply_eq_one y
      rw [Fin.sum_univ_four] at this
      exact this
    · have := b.affineCombination_coord_eq_self y
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (b.sum_coord_apply_eq_one y), hb,
        Fin.sum_univ_four] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this
      exact this.symm

/-- **Points just off the middle of an edge lie inside the tetrahedron.** Write
`r = a + ζ (b - a) + u` and `s = a + ζ' (b - a) + u'`. For `l, m > 0` and all small `ε > 0`, the
point `a + ½ (b - a) + ε (l u + m u')` lies in the open tetrahedron `abrs`. -/
theorem mem_openTet_near {a b r s u u' : E} {ζ ζ' l m : ℝ} (hr : r = a + ζ • (b - a) + u)
    (hs : s = a + ζ' • (b - a) + u') (hl : 0 < l) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      a + (1 / 2 : ℝ) • (b - a) + ε • (l • u + m • u') ∈ openTet a b r s := by
  have hM2 : 0 < 2 * (|l * ζ + m * ζ'| + l + m + 1) := by
    linarith [abs_nonneg (l * ζ + m * ζ')]
  refine ⟨1 / (2 * (|l * ζ + m * ζ'| + l + m + 1)), div_pos one_pos hM2, fun ε hε hεδ => ?_⟩
  rw [lt_div_iff₀ hM2] at hεδ
  have h1 : ε * (-|l * ζ + m * ζ'|) ≤ ε * (l * ζ + m * ζ') :=
    mul_le_mul_of_nonneg_left (neg_abs_le _) hε.le
  have h2 : ε * (l * ζ + m * ζ') ≤ ε * |l * ζ + m * ζ'| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
  refine ⟨1 / 2 + ε * (l * ζ + m * ζ' - l - m), 1 / 2 - ε * (l * ζ + m * ζ'), ε * l, ε * m,
    by nlinarith, by nlinarith, by positivity, by positivity, by ring, ?_⟩
  rw [hr, hs]
  module

/-- **An orthonormal frame along a direction.** In a 3-dimensional real inner product space, for
`v ≠ 0` there is an orthonormal triple `e₀, e₁, e₂` with `v = ‖v‖ • e₀` that spans the space. -/
theorem exists_frame [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3) {v : E} (hv : v ≠ 0) :
    ∃ e₀ e₁ e₂ : E, Orthonormal ℝ ![e₀, e₁, e₂] ∧ v = ‖v‖ • e₀ ∧
      ∀ y : E, y = ⟪y, e₀⟫_ℝ • e₀ + ⟪y, e₁⟫_ℝ • e₁ + ⟪y, e₂⟫_ℝ • e₂ := by
  have hn : ‖‖v‖⁻¹ • v‖ = 1 := norm_smul_inv_norm hv
  have ho : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict fun _ : Fin 3 => ‖v‖⁻¹ • v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi hj
    rw [real_inner_self_eq_norm_sq, Set.domRestrict_apply, hn, ite_eq_left rfl]
    norm_num
  obtain ⟨B, hB⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp [hE])
  have hB0 : B 0 = ‖v‖⁻¹ • v := hB 0 rfl
  refine ⟨B 0, B 1, B 2, ?_, ?_, ?_⟩
  · have : ![B 0, B 1, B 2] = ⇑B := by
      ext i
      fin_cases i <;> rfl
    rw [this]
    exact B.orthonormal
  · rw [hB0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  · intro y
    have := B.sum_repr' y
    rw [Fin.sum_univ_three] at this
    rw [real_inner_comm (B 0) y, real_inner_comm (B 1) y, real_inner_comm (B 2) y]
    exact this.symm

/-- **Cylindrical coordinates.** In a frame `e₀, e₁, e₂` spanning the space, every vector is
`z • e₀ + ρ • (cos α • e₁ + sin α • e₂)` with `z = ⟪y, e₀⟫`, and `ρ, α` the modulus and argument of
the complex number `⟪y, e₁⟫ + i ⟪y, e₂⟫`. -/
theorem cyl_repr {e₀ e₁ e₂ : E}
    (hexp : ∀ y : E, y = ⟪y, e₀⟫_ℝ • e₀ + ⟪y, e₁⟫_ℝ • e₁ + ⟪y, e₂⟫_ℝ • e₂) (y : E) :
    y = ⟪y, e₀⟫_ℝ • e₀ + ‖(⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩ : ℂ)‖ •
      (cos (Complex.arg ⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩) • e₁ +
        sin (Complex.arg ⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩) • e₂) := by
  have h1 : ‖(⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩ : ℂ)‖ * cos (Complex.arg ⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩) =
      ⟪y, e₁⟫_ℝ := Complex.norm_mul_cos_arg _
  have h2 : ‖(⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩ : ℂ)‖ * sin (Complex.arg ⟨⟪y, e₁⟫_ℝ, ⟪y, e₂⟫_ℝ⟩) =
      ⟪y, e₂⟫_ℝ := Complex.norm_mul_sin_arg _
  rw [smul_add, smul_smul, smul_smul, h1, h2, ← add_assoc]
  exact hexp y

/-- **Non-degenerate tetrahedra in cylindrical coordinates.** If the edge vectors
`v₁ = L e₀`, `v₂ = z e₀ + ρ (cos α e₁ + sin α e₂)`, `v₃ = z' e₀ + ρ' (cos α' e₁ + sin α' e₂)` of a
tetrahedron are linearly independent, then `ρ ≠ 0`, `ρ' ≠ 0` (the two vertices are off the line
of the edge) and `sin (α' - α) ≠ 0` (the two faces at the edge are not coplanar). -/
theorem cyl_nondeg {v₁ v₂ v₃ e₀ e₁ e₂ : E} {L z ρ α z' ρ' α' : ℝ} (hL : 0 < L)
    (h1 : v₁ = L • e₀) (h2 : v₂ = z • e₀ + ρ • (cos α • e₁ + sin α • e₂))
    (h3 : v₃ = z' • e₀ + ρ' • (cos α' • e₁ + sin α' • e₂))
    (hli : LinearIndependent ℝ ![v₁, v₂, v₃]) : ρ ≠ 0 ∧ ρ' ≠ 0 ∧ sin (α' - α) ≠ 0 := by
  have key := Fintype.linearIndependent_iff.mp hli
  have hρ : ρ ≠ 0 := by
    intro h0
    have := key ![z, -L, 0] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [h1, h2, h0]
      module) 1
    simp at this
    linarith
  have hρ' : ρ' ≠ 0 := by
    intro h0
    have := key ![z', 0, -L] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [h1, h3, h0]
      module) 2
    simp at this
    linarith
  refine ⟨hρ, hρ', fun hs => ?_⟩
  have hc' : cos α' = cos α * cos (α' - α) := by
    rw [show α' = α + (α' - α) by ring, cos_add, show α + (α' - α) - α = α' - α by ring, hs]
    ring
  have hs' : sin α' = sin α * cos (α' - α) := by
    rw [show α' = α + (α' - α) by ring, sin_add, show α + (α' - α) - α = α' - α by ring, hs]
    ring
  have := key ![-(ρ * z' - ρ' * cos (α' - α) * z), -(L * ρ' * cos (α' - α)), L * ρ] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [h1, h2, h3, hc', hs']
    module) 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, mul_eq_zero] at this
  rcases this with h | h
  · exact hL.ne' h
  · exact hρ h

/-- The converse of `cyl_nondeg`: in an orthonormal frame, the edge vectors
`L e₀`, `z e₀ + ρ (cos α e₁ + sin α e₂)`, `z' e₀ + ρ' (cos α' e₁ + sin α' e₂)` are linearly
independent when `L, ρ, ρ' ≠ 0` and `sin (α' - α) ≠ 0`. -/
theorem cyl_linIndep {v₁ v₂ v₃ e₀ e₁ e₂ : E} (horth : Orthonormal ℝ ![e₀, e₁, e₂])
    {L z ρ α z' ρ' α' : ℝ} (hL : L ≠ 0) (hρ : ρ ≠ 0) (hρ' : ρ' ≠ 0) (hs : sin (α' - α) ≠ 0)
    (h1 : v₁ = L • e₀) (h2 : v₂ = z • e₀ + ρ • (cos α • e₁ + sin α • e₂))
    (h3 : v₃ = z' • e₀ + ρ' • (cos α' • e₁ + sin α' • e₂)) :
    LinearIndependent ℝ ![v₁, v₂, v₃] := by
  obtain ⟨h₀, h₁, h₂, h₁₀, h₂₀, h₁₂⟩ := orthonormal_three horth
  have i00 : ⟪e₀, e₀⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h₀]; norm_num
  have i11 : ⟪e₁, e₁⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have i22 : ⟪e₂, e₂⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, h₂]; norm_num
  have i01 : ⟪e₀, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact h₁₀
  have i02 : ⟪e₀, e₂⟫_ℝ = 0 := by rw [real_inner_comm]; exact h₂₀
  have i21 : ⟪e₂, e₁⟫_ℝ = 0 := by rw [real_inner_comm]; exact h₁₂
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  rw [h1, h2, h3] at hg
  have c0 := congrArg (fun y => ⟪y, e₀⟫_ℝ) hg
  have c1 := congrArg (fun y => ⟪y, e₁⟫_ℝ) hg
  have c2 := congrArg (fun y => ⟪y, e₂⟫_ℝ) hg
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left, i00, i11, i22, i01, i02, i21,
    h₁₀, h₂₀, h₁₂] at c0 c1 c2
  have hg1 : g 1 * (ρ * ρ' * sin (α' - α)) = 0 := by
    rw [sin_sub]
    linear_combination (ρ' * sin α') * c1 - (ρ' * cos α') * c2
  have hg2 : g 2 * (ρ * ρ' * sin (α' - α)) = 0 := by
    rw [sin_sub]
    linear_combination (-(ρ * sin α)) * c1 + (ρ * cos α) * c2
  have hne : ρ * ρ' * sin (α' - α) ≠ 0 := mul_ne_zero (mul_ne_zero hρ hρ') hs
  have e1 : g 1 = 0 := (mul_eq_zero.mp hg1).resolve_right hne
  have e2 : g 2 = 0 := (mul_eq_zero.mp hg2).resolve_right hne
  have e0 : g 0 = 0 := by
    rw [e1, e2] at c0
    have : g 0 * L = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hL
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

variable {V : Type*} [DecidableEq V]

/-- **Triangulations of a region of space have zero deficit.** Let `E` be a real inner product
space of dimension 3 and `x` a placement of the vertices of `K` in `E`, with the induced edge
lengths. Suppose the link of the edge `ab` is a cycle `w 0, …, w (n-1)` (`IsCycleLink`), each
tetrahedron `{a, b, w i, w (i+1)}` around it is non-degenerate (its edge vectors from `a` are
linearly independent), and the interiors of these tetrahedra are pairwise disjoint. Then the
deficit angle at `ab` is zero. -/
theorem deficit_eq_zero_of_embedded [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3)
    (K : Complex3 V) (x : V → E) {a b : V} {n : ℕ} {w : ℕ → V} (hc : IsCycleLink K a b n w)
    (hnd : ∀ i < n, LinearIndependent ℝ ![x b - x a, x (w i) - x a, x (w (i + 1)) - x a])
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (openTet (x a) (x b) (x (w i)) (x (w (i + 1))))
        (openTet (x a) (x b) (x (w j)) (x (w (j + 1))))) :
    deficit K (ofDist fun u v => dist (x u) (x v)) {a, b} = 0 := by
  have h3 := hc.three_le
  have hn : 0 < n := by omega
  have hv : x b - x a ≠ 0 := by simpa using (hnd 0 hn).ne_zero 0
  obtain ⟨e₀, e₁, e₂, horth, hve, hexp⟩ := exists_frame hE hv
  obtain ⟨L, hLe⟩ : ∃ L, ‖x b - x a‖ = L := ⟨_, rfl⟩
  rw [hLe] at hve
  have hL : 0 < L := hLe ▸ norm_pos_iff.mpr hv
  have hb : x b = x a + L • e₀ := by rw [← hve]; abel
  -- cylindrical coordinates of the link vertices around the line `ab`
  obtain ⟨z, ρ, α, hcyl, hρ0, hρn, hαn⟩ : ∃ z ρ α : ℕ → ℝ,
      (∀ i, x (w i) - x a = z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂)) ∧
      (∀ i, 0 ≤ ρ i) ∧ ρ n = ρ 0 ∧ α n = α 0 :=
    ⟨fun i => ⟪x (w i) - x a, e₀⟫_ℝ, fun i => ‖(⟨⟪x (w i) - x a, e₁⟫_ℝ, ⟪x (w i) - x a, e₂⟫_ℝ⟩ : ℂ)‖,
      fun i => Complex.arg ⟨⟪x (w i) - x a, e₁⟫_ℝ, ⟪x (w i) - x a, e₂⟫_ℝ⟩,
      fun i => cyl_repr hexp _, fun _ => norm_nonneg _, by simp only [hc.closed],
      by simp only [hc.closed]⟩
  have hx : ∀ i, x (w i) = x a + z i • e₀ + ρ i • (cos (α i) • e₁ + sin (α i) • e₂) := by
    intro i
    rw [add_assoc, ← hcyl i]
    abel
  -- non-degeneracy: the link vertices are off the axis, consecutive faces are not coplanar
  have hnd' := fun i hi => cyl_nondeg hL hve (hcyl i) (hcyl (i + 1)) (hnd i hi)
  have hρpos : ∀ i ≤ n, 0 < ρ i := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact lt_of_le_of_ne (hρ0 i) (hnd' i h).1.symm
    · rw [h, hρn]
      exact lt_of_le_of_ne (hρ0 0) (hnd' 0 hn).1.symm
  -- disjoint interiors make the wedges between consecutive directions disjoint
  have hW : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ := by
    intro i hi j hj hij τ h1 h2
    obtain ⟨l, m, hl, hm, hcl, hsl⟩ := h1
    obtain ⟨l', m', hl', hm', hcl', hsl'⟩ := h2
    have hr : ∀ k, x (w k) = x a + (z k / L) • (x b - x a) +
        ρ k • (cos (α k) • e₁ + sin (α k) • e₂) := by
      intro k
      rw [hve, smul_smul, div_mul_cancel₀ _ hL.ne']
      exact hx k
    obtain ⟨δ₁, hδ₁, H₁⟩ := mem_openTet_near (hr i) (hr (i + 1))
      (div_pos hl (hρpos i hi.le)) (div_pos hm (hρpos (i + 1) hi))
    obtain ⟨δ₂, hδ₂, H₂⟩ := mem_openTet_near (hr j) (hr (j + 1))
      (div_pos hl' (hρpos j hj.le)) (div_pos hm' (hρpos (j + 1) hj))
    have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hε : 0 < min δ₁ δ₂ / 2 := half_pos hmin
    have P₁ := H₁ (min δ₁ δ₂ / 2) hε (by linarith [min_le_left δ₁ δ₂])
    have P₂ := H₂ (min δ₁ δ₂ / 2) hε (by linarith [min_le_right δ₁ δ₂])
    have dir : ∀ (k : ℕ) (l m : ℝ), 0 < ρ k → 0 < ρ (k + 1) →
        (l / ρ k) • (ρ k • (cos (α k) • e₁ + sin (α k) • e₂)) +
          (m / ρ (k + 1)) • (ρ (k + 1) • (cos (α (k + 1)) • e₁ + sin (α (k + 1)) • e₂)) =
        (l * cos (α k) + m * cos (α (k + 1))) • e₁ + (l * sin (α k) + m * sin (α (k + 1))) • e₂ :=
      by
      intro k l m h h'
      rw [smul_smul, smul_smul, div_mul_cancel₀ _ h.ne', div_mul_cancel₀ _ h'.ne']
      module
    rw [dir i l m (hρpos i hi.le) (hρpos (i + 1) hi), ← hcl, ← hsl] at P₁
    rw [dir j l' m' (hρpos j hj.le) (hρpos (j + 1) hj), ← hcl', ← hsl'] at P₂
    exact Set.disjoint_left.mp (hdisj i hi j hj hij) P₁ P₂
  -- the dihedral angles around `ab` add up to `2π`
  have hsum := sum_arccos_cos_eq_two_pi hn α (fun i hi => (hnd' i hi).2.2)
    ⟨by rw [hαn], by rw [hαn]⟩ hW
  have hℓ : ∀ u v, u ≠ v → ofDist (fun u v => dist (x u) (x v)) {u, v} = dist (x u) (x v) :=
    fun u v h => ofDist_pair (d := fun u v => dist (x u) (x v)) (fun u => dist_self (x u))
      (fun u v => dist_comm (x u) (x v)) h
  have hxab : x a ≠ x b := fun h => hv (by rw [h, sub_self])
  have hab := hc.ne
  have hterm : ∀ i ∈ range n,
      dihedralAt (ofDist fun u v => dist (x u) (x v)) {a, b, w i, w (i + 1)} {a, b} =
        arccos (cos (α (i + 1) - α i)) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hc.tet_distinct hi'
    rw [dihedralAt_eq _ hab h₁ h₂ h₃ h₄ h₅ (by rw [hℓ a b hab]; exact dist_ne_zero.mpr hxab),
      hℓ _ _ hab, hℓ _ _ h₁, hℓ _ _ h₃, hℓ _ _ h₂, hℓ _ _ h₄, hℓ _ _ h₅]
    exact dihedral_cyl_eq_arccos horth hL (hρpos i hi'.le) (hρpos (i + 1) hi') hb (hx i)
      (hx (i + 1))
  rw [deficit, hc.angleSum_eq, sum_congr rfl hterm, hsum, sub_self]

/-! ## Geometric triangulations -/

/-- The open simplex spanned by the vertex set `t` under the placement `x`: the points
`Σ_{v ∈ t} c v • x v` with all `c v > 0` and `Σ_{v ∈ t} c v = 1`. It does not depend on a labelling
of the vertices; for `t = {p, q, r, s}` it contains `openTet (x p) (x q) (x r) (x s)`
(`openTet_subset_openHull`). -/
def openHull (x : V → E) (t : Finset V) : Set E :=
  {y | ∃ c : V → ℝ, (∀ v ∈ t, 0 < c v) ∧ ∑ v ∈ t, c v = 1 ∧ y = ∑ v ∈ t, c v • x v}

/-- The open tetrahedron of a labelling lies in the open simplex of its vertex set. -/
theorem openTet_subset_openHull (x : V → E) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    openTet (x p) (x q) (x r) (x s) ⊆ openHull x {p, q, r, s} := by
  rintro y ⟨c₀, c₁, c₂, c₃, h₀, h₁, h₂, h₃, hsum, rfl⟩
  refine ⟨fun v => if v = p then c₀ else if v = q then c₁ else if v = r then c₂ else c₃, ?_, ?_, ?_⟩
  · intro v hv
    simp only [mem_insert, mem_singleton] at hv
    have := hpq.symm; have := hpr.symm; have := hps.symm
    have := hqr.symm; have := hqs.symm; have := hrs.symm
    rcases hv with rfl | rfl | rfl | rfl <;> simp_all
  · rw [sum_insert (by simp [hpq, hpr, hps]), sum_insert (by simp [hqr, hqs]),
      sum_insert (by simp [hrs]), sum_singleton]
    simp [hpq.symm, hpr.symm, hps.symm, hqr.symm, hqs.symm, hrs.symm]
    linarith
  · rw [sum_insert (by simp [hpq, hpr, hps]), sum_insert (by simp [hqr, hqs]),
      sum_insert (by simp [hrs]), sum_singleton]
    simp [hpq.symm, hpr.symm, hps.symm, hqr.symm, hqs.symm, hrs.symm, add_assoc]

/-- The four labelled points of a tetrahedron, as a family indexed by `Fin 4`, are affinely
independent iff the three edge vectors from the first are linearly independent. -/
theorem affIndep_four_iff (P₀ P₁ P₂ P₃ : E) :
    AffineIndependent ℝ ![P₀, P₁, P₂, P₃] ↔ LinearIndependent ℝ ![P₁ - P₀, P₂ - P₀, P₃ - P₀] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 4),
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 4))]
  have : ((fun i : {x : Fin 4 // x ≠ 0} => ![P₀, P₁, P₂, P₃] ↑i -ᵥ ![P₀, P₁, P₂, P₃] 0) ∘
      finSuccAboveEquiv (0 : Fin 4)) = ![P₁ - P₀, P₂ - P₀, P₃ - P₀] := by
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv, vsub_eq_sub]
  rw [this]

/-- Affine independence of the vertex set of a tetrahedron gives affine independence of the four
points in any labelling. -/
theorem affIndep_four_of_subtype (x : V → E) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : AffineIndependent ℝ fun v : ({p, q, r, s} : Finset V) => x v) :
    AffineIndependent ℝ ![x p, x q, x r, x s] := by
  let f : Fin 4 → ({p, q, r, s} : Finset V) :=
    ![⟨p, by simp⟩, ⟨q, by simp⟩, ⟨r, by simp⟩, ⟨s, by simp⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Subtype.ext_iff, hpq.symm, hpr.symm, hps.symm, hqr.symm, hqs.symm, hrs.symm]
  have := h.comp_embedding ⟨f, hf⟩
  convert this using 1
  ext i
  fin_cases i <;> rfl

/-- Affine independence of the vertex set of a tetrahedron gives linear independence of the edge
vectors for any labelling. -/
theorem linIndep_of_affIndep (x : V → E) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : AffineIndependent ℝ fun v : ({p, q, r, s} : Finset V) => x v) :
    LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p] :=
  (affIndep_four_iff _ _ _ _).mp (affIndep_four_of_subtype x hpq hpr hps hqr hqs hrs h)

/-- Conversely, linear independence of the edge vectors of one labelling gives affine independence
of the vertex set. -/
theorem affIndep_of_linIndep (x : V → E) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p]) :
    AffineIndependent ℝ fun v : ({p, q, r, s} : Finset V) => x v := by
  have h4 := (affIndep_four_iff _ _ _ _).mpr h
  have hinj := h4.injective
  have hrange : Set.range (fun v : ({p, q, r, s} : Finset V) => x v) =
      Set.range ![x p, x q, x r, x s] := by
    ext y
    simp only [Set.mem_range, Subtype.exists, mem_insert, mem_singleton]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i
      exacts [⟨p, by simp, rfl⟩, ⟨q, by simp, rfl⟩, ⟨r, by simp, rfl⟩, ⟨s, by simp, rfl⟩]
  refine AffineIndependent.of_set_of_injective ?_ ?_
  · rw [hrange]
    exact h4.range
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    simp only at huv
    simp only [mem_insert, mem_singleton] at hu hv
    have ne : ∀ i j : Fin 4, i ≠ j → ![x p, x q, x r, x s] i ≠ ![x p, x q, x r, x s] j :=
      fun i j h => hinj.ne h
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact absurd huv (by simpa using ne 0 1 (by decide))
      | exact absurd huv (by simpa using ne 0 2 (by decide))
      | exact absurd huv (by simpa using ne 0 3 (by decide))
      | exact absurd huv (by simpa using ne 1 0 (by decide))
      | exact absurd huv (by simpa using ne 1 2 (by decide))
      | exact absurd huv (by simpa using ne 1 3 (by decide))
      | exact absurd huv (by simpa using ne 2 0 (by decide))
      | exact absurd huv (by simpa using ne 2 1 (by decide))
      | exact absurd huv (by simpa using ne 2 3 (by decide))
      | exact absurd huv (by simpa using ne 3 0 (by decide))
      | exact absurd huv (by simpa using ne 3 1 (by decide))
      | exact absurd huv (by simpa using ne 3 2 (by decide))

/-- The open simplex of the vertex set `{p, q, r, s}` is the open tetrahedron of the labelling. -/
theorem openHull_eq_openTet (x : V → E) {p q r s : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    openHull x {p, q, r, s} = openTet (x p) (x q) (x r) (x s) := by
  refine Set.Subset.antisymm ?_ (openTet_subset_openHull x hpq hpr hps hqr hqs hrs)
  rintro y ⟨c, hc, hsum, rfl⟩
  rw [sum_insert (by simp [hpq, hpr, hps]), sum_insert (by simp [hqr, hqs]),
    sum_insert (by simp [hrs]), sum_singleton] at hsum ⊢
  exact ⟨c p, c q, c r, c s, hc p (by simp), hc q (by simp), hc r (by simp), hc s (by simp),
    by linarith, by abel⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The image of a vertex set `{p, q, r, s}` under a placement. -/
theorem image_four (x : V → E) (p q r s : V) :
    x '' ↑({p, q, r, s} : Finset V) = ({x p, x q, x r, x s} : Set E) := by
  simp [Set.image_insert_eq]

/-- **The open simplex of a tetrahedron is the interior of its convex hull**, for a
non-degenerate tetrahedron placed in a 3-dimensional real inner product space. -/
theorem openHull_eq_interior [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3) (x : V → E)
    {K : Complex3 V} {t : Finset V} (ht : t ∈ K.tets) (h : AffineIndependent ℝ fun v : t => x v) :
    openHull x t = interior (convexHull ℝ (x '' ↑t)) := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := exists_label ht
  rw [openHull_eq_openTet x hpq hpr hps hqr hqs hrs, image_four,
    openTet_eq_interior hE (affIndep_four_of_subtype x hpq hpr hps hqr hqs hrs h)]

/-- A placement `x` of the vertices of `K` in `E` is a **geometric triangulation** (of the region
covered by its tetrahedra): every tetrahedron is non-degenerate (its four vertices are affinely
independent), and distinct tetrahedra have disjoint interiors, the topological interiors of their
convex hulls. -/
structure IsGeometric (K : Complex3 V) (x : V → E) : Prop where
  nondeg : ∀ t ∈ K.tets, AffineIndependent ℝ fun v : t => x v
  disjoint : ∀ t ∈ K.tets, ∀ t' ∈ K.tets, t ≠ t' →
    Disjoint (interior (convexHull ℝ (x '' ↑t))) (interior (convexHull ℝ (x '' ↑t')))

/-- **In a geometric triangulation of a region of 3-space, an edge whose link is a cycle has zero
deficit.** -/
theorem IsGeometric.deficit_eq_zero_of_cycleLink [FiniteDimensional ℝ E]
    (hE : finrank ℝ E = 3) {K : Complex3 V} {x : V → E} (hK : IsGeometric K x) {a b : V}
    {n : ℕ} {w : ℕ → V} (hc : IsCycleLink K a b n w) :
    deficit K (ofDist fun u v => dist (x u) (x v)) {a, b} = 0 := by
  apply deficit_eq_zero_of_embedded hE K x hc
  · intro i hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hc.tet_distinct hi
    exact linIndep_of_affIndep x hc.ne h₁ h₂ h₃ h₄ h₅ (hK.nondeg _ (hc.tet_mem hi))
  · intro i hi j hj hij
    have hne : ({a, b, w i, w (i + 1)} : Finset V) ≠ {a, b, w j, w (j + 1)} := fun h =>
      hij (hc.injOn_tet (by simpa using hi) (by simpa using hj) h)
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hc.tet_distinct hi
    obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := hc.tet_distinct hj
    have hd := hK.disjoint _ (hc.tet_mem hi) _ (hc.tet_mem hj) hne
    rw [← openHull_eq_interior hE x (hc.tet_mem hi) (hK.nondeg _ (hc.tet_mem hi)),
      ← openHull_eq_interior hE x (hc.tet_mem hj) (hK.nondeg _ (hc.tet_mem hj)),
      openHull_eq_openTet x hc.ne h₁ h₂ h₃ h₄ h₅, openHull_eq_openTet x hc.ne k₁ k₂ k₃ k₄ k₅] at hd
    exact hd

/-- **Flat space has zero curvature: every interior edge of a geometric triangulation of a region
of 3-space has deficit angle zero.** Here `K` is an edge-manifold placed in a 3-dimensional real
inner product space by a geometric triangulation `x`, with the induced edge lengths. -/
theorem IsGeometric.deficit_eq_zero [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3)
    {K : Complex3 V} {x : V → E} (hK : IsGeometric K x) (hM : IsEdgeManifold K)
    {e : Finset V} (he : e ∈ intEdges K) :
    deficit K (ofDist fun u v => dist (x u) (x v)) e = 0 := by
  obtain ⟨a, b, n, w, rfl, hc⟩ := hM.mem_intEdges_iff.mp he
  exact hK.deficit_eq_zero_of_cycleLink hE hc

/-- **The Regge action of a flat region is a pure boundary term**: for a geometric triangulation
of a region of 3-space, `S = Σ_{boundary edges} ℓ_e (π - Σ θ)`. -/
theorem IsGeometric.reggeAction_eq [FiniteDimensional ℝ E] (hE : finrank ℝ E = 3)
    {K : Complex3 V} {x : V → E} (hK : IsGeometric K x) (hM : IsEdgeManifold K) :
    reggeAction K (ofDist fun u v => dist (x u) (x v)) =
      ∑ e ∈ bdryEdges K, ofDist (fun u v => dist (x u) (x v)) e *
        bdryAngle K (ofDist fun u v => dist (x u) (x v)) e := by
  rw [reggeAction, sum_eq_zero fun e he => by rw [hK.deficit_eq_zero hE hM he, mul_zero],
    zero_add]

end Lightlike.Regge
