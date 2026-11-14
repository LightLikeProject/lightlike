import Lightlike.Regge.D4.Complex
import Lightlike.Regge.ReggeEquations

/-!
# The Schläfli identity for a Euclidean 4-simplex

For a 4-simplex with triangle areas `A_t` and dihedral angles `θ_t`, **Schläfli's identity** says
`Σ_t A_t dθ_t = 0` for every variation of the ten edge lengths. It is the lemma behind Regge's
equations in 4D (`Lightlike/Regge/D4/ReggeEquations.lean`).

## Method

As in 3D (`Lightlike/Regge/Schlaefli.lean`) everything reduces to polynomials in the squared
lengths. At the triangle `pqr` with opposite vertices `s, u`, write `M = mixed`,
`G_s = gram3(pqrs)`, `G_u = gram3(pqru)`. Then `cos θ = M / √(G_s G_u)` and, by Desnanot–Jacobi,
`G_s G_u - M² = gram2 · gram4`. Differentiating along a line of lengths,

  `A dθ = -(dM - (M/2)(dG_s/G_s + dG_u/G_u)) / (2 √gram4)`,

the area `A = √gram2 / 2` cancelling (`hasDerivAt_dihedral4_line`). Summed over the ten triangles
and regrouped by the five tetrahedral facets, two polynomial identities finish the proof:

* `facet_identity`: on each facet `F`, the four mixed determinants of its triangles add up to
  `gram3(F)`;
* hence the ten mixed determinants add up to half the sum of the five `gram3(F)`.

The first identity turns `Σ_t M_t (dG/G + dG/G)` into `Σ_F dG_F`, the second turns `Σ_t dM_t` into
`½ Σ_F dG_F`, and the two cancel. Both identities, and Schläfli's identity at random rational
lengths with a failing control, are checked in `scripts/regge/regge4_check.py`.

## Main results

* `facet_identity`, `sum_mixed_eq`: the polynomial identities.
* `hasDerivAt_dihedral4_line`: the derivative of a dihedral angle along a line of lengths.
* `schlaefli4`: Schläfli's identity for a labelled 4-simplex; `schlaefli4_finset`: the same,
  labelling-free, as a sum over the triangles of a 4-simplex.
-/

open Real Finset

namespace Lightlike.Regge4

variable {V : Type*} [DecidableEq V]

/-! ## Polynomial identities -/

/-- **The facet identity**: on the tetrahedron `F = pqrs` of the 4-simplex `pqrsu`, the mixed
determinants of its four triangles (each with the opposite vertex of `F`, and `u`) add up to
`gram3(F)`. -/
theorem facet_identity (ℓ : Finset V → ℝ) (p q r s u : V) :
    mixed ℓ p q r s u + mixed ℓ p q s r u + mixed ℓ p r s q u + mixed ℓ q r s p u =
      gram3 ℓ p q r s := by sq_ring

/-- `gram3` rotated in its last three points. -/
theorem gram3_rot3 (ℓ : Finset V → ℝ) (p q r s : V) : gram3 ℓ p r s q = gram3 ℓ p q r s := by
  sq_ring

/-- `gram3` rotated in all four points. -/
theorem gram3_rot4 (ℓ : Finset V → ℝ) (p q r s : V) : gram3 ℓ q r s p = gram3 ℓ p q r s := by
  sq_ring

/-- The ten mixed determinants of a 4-simplex, one for each triangle (listed with its opposite
pair), in the labelling `p, q, r, s, u`. -/
noncomputable def mixedSum (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  mixed ℓ p q r s u + mixed ℓ p q s r u + mixed ℓ p q u r s + mixed ℓ p r s q u +
    mixed ℓ p r u q s + mixed ℓ p s u q r + mixed ℓ q r s p u + mixed ℓ q r u p s +
    mixed ℓ q s u p r + mixed ℓ r s u p q

/-- The five `gram3` of the tetrahedral facets of a 4-simplex. -/
noncomputable def gram3Sum (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  gram3 ℓ p q r s + gram3 ℓ p q r u + gram3 ℓ p q s u + gram3 ℓ p r s u + gram3 ℓ q r s u

/-- **The triangle sum**: the ten mixed determinants of a 4-simplex add up to half the sum of the
`gram3` of its five facets (each triangle lies in two facets). -/
theorem sum_mixed_eq (ℓ : Finset V → ℝ) (p q r s u : V) :
    mixedSum ℓ p q r s u = gram3Sum ℓ p q r s u / 2 := by
  have fu := facet_identity ℓ p q r s u
  have fs := facet_identity ℓ p q r u s
  have fr := facet_identity ℓ p q s u r
  have fq := facet_identity ℓ p r s u q
  have fp := facet_identity ℓ q r s u p
  simp only [mixed_swap_su ℓ p q r s u, mixed_swap_su ℓ p q s r u, mixed_swap_su ℓ p q u r s,
    mixed_swap_su ℓ p r s q u, mixed_swap_su ℓ p r u q s, mixed_swap_su ℓ p s u q r,
    mixed_swap_su ℓ q r s p u, mixed_swap_su ℓ q r u p s, mixed_swap_su ℓ q s u p r,
    mixed_swap_su ℓ r s u p q] at fs fr fq fp
  unfold mixedSum gram3Sum
  linarith

/-! ## Derivatives along a line of lengths -/

/-- The line of lengths `ℓ + τ v`. -/
def lineL (ℓ v : Finset V → ℝ) (τ : ℝ) : Finset V → ℝ := fun e => ℓ e + τ * v e

omit [DecidableEq V] in
@[simp] theorem lineL_zero (ℓ v : Finset V → ℝ) : lineL ℓ v 0 = ℓ := by
  funext e
  simp [lineL]

/-- Squared lengths are differentiable along a line of lengths. -/
@[fun_prop] theorem differentiable_sq_lineL (ℓ v : Finset V → ℝ) (a b : V) :
    Differentiable ℝ fun τ => sq (lineL ℓ v τ) a b := by
  by_cases h : a = b
  · subst h
    simp only [sq_self]
    fun_prop
  · simp only [sq_of_ne _ h, lineL]
    fun_prop

/-- The mixed determinant is differentiable along a line of lengths. -/
theorem differentiable_mixed_lineL (ℓ v : Finset V → ℝ) (p q r s u : V) :
    Differentiable ℝ fun τ => mixed (lineL ℓ v τ) p q r s u := by
  unfold mixed det3 ip
  fun_prop

/-- `gram3` is differentiable along a line of lengths. -/
theorem differentiable_gram3_lineL (ℓ v : Finset V → ℝ) (p q r s : V) :
    Differentiable ℝ fun τ => gram3 (lineL ℓ v τ) p q r s := by
  unfold gram3 det3 ip
  fun_prop

/-- **The derivative of a dihedral angle along a line of lengths.** At a non-degenerate 4-simplex
(`gram3 > 0` for the two tetrahedra at the triangle, `gram2 > 0`, `gram4 > 0`), the dihedral angle
at the triangle `pqr`, along `ℓ + τ v`, has derivative
`-(dM - M (dG_s/G_s + dG_u/G_u)/2) / √(gram2 · gram4)` at `τ = 0`. -/
theorem hasDerivAt_dihedral4_line (ℓ v : Finset V → ℝ) (p q r s u : V)
    (hs : 0 < gram3 ℓ p q r s) (hu : 0 < gram3 ℓ p q r u) (h2 : 0 < gram2 ℓ p q r)
    (h4 : 0 < gram4 ℓ p q r s u) :
    HasDerivAt (fun τ => dihedral4 (lineL ℓ v τ) p q r s u)
      (-(deriv (fun τ => mixed (lineL ℓ v τ) p q r s u) 0 - mixed ℓ p q r s u *
          (deriv (fun τ => gram3 (lineL ℓ v τ) p q r s) 0 / gram3 ℓ p q r s +
            deriv (fun τ => gram3 (lineL ℓ v τ) p q r u) 0 / gram3 ℓ p q r u) / 2) /
        √(gram2 ℓ p q r * gram4 ℓ p q r s u)) 0 := by
  have hM := (differentiable_mixed_lineL ℓ v p q r s u 0).hasDerivAt
  have hGs := (differentiable_gram3_lineL ℓ v p q r s 0).hasDerivAt
  have hGu := (differentiable_gram3_lineL ℓ v p q r u 0).hasDerivAt
  set M' := deriv (fun τ => mixed (lineL ℓ v τ) p q r s u) 0
  set Gs' := deriv (fun τ => gram3 (lineL ℓ v τ) p q r s) 0
  set Gu' := deriv (fun τ => gram3 (lineL ℓ v τ) p q r u) 0
  have hP0 : 0 < gram3 ℓ p q r s * gram3 ℓ p q r u := mul_pos hs hu
  have hP := hGs.mul hGu
  have hS := hP.sqrt (by simpa [Pi.mul_apply] using hP0.ne')
  have hsP : √(gram3 ℓ p q r s * gram3 ℓ p q r u) ≠ 0 := (Real.sqrt_pos.mpr hP0).ne'
  have hC := hM.div hS (by simpa [Pi.mul_apply] using hsP)
  -- `|cos θ| < 1`, by Desnanot–Jacobi
  have hdj := desnanot_jacobi ℓ p q r s u
  have hgap : 0 < gram2 ℓ p q r * gram4 ℓ p q r s u := mul_pos h2 h4
  have hsq : (mixed ℓ p q r s u / √(gram3 ℓ p q r s * gram3 ℓ p q r u)) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hP0.le, div_lt_one hP0]
    linarith
  have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq)
  have hA := (Real.hasDerivAt_arccos (by simpa using hbd.1.ne') (by simpa using hbd.2.ne)).comp 0 hC
  simp only [lineL_zero, Pi.mul_apply, Pi.div_apply] at hA
  refine hA.congr_deriv ?_
  -- simplify the derivative
  have hsin : √(1 - (mixed ℓ p q r s u / √(gram3 ℓ p q r s * gram3 ℓ p q r u)) ^ 2) =
      √(gram2 ℓ p q r * gram4 ℓ p q r s u) / √(gram3 ℓ p q r s * gram3 ℓ p q r u) := by
    rw [div_pow, Real.sq_sqrt hP0.le,
      show 1 - mixed ℓ p q r s u ^ 2 / (gram3 ℓ p q r s * gram3 ℓ p q r u) =
        gram2 ℓ p q r * gram4 ℓ p q r s u / (gram3 ℓ p q r s * gram3 ℓ p q r u) by
        field_simp
        linarith,
      Real.sqrt_div hgap.le]
  rw [hsin]
  have hg : √(gram2 ℓ p q r * gram4 ℓ p q r s u) ≠ 0 := (Real.sqrt_pos.mpr hgap).ne'
  have hss : √(gram3 ℓ p q r s * gram3 ℓ p q r u) ^ 2 = gram3 ℓ p q r s * gram3 ℓ p q r u :=
    Real.sq_sqrt hP0.le
  field_simp
  rw [hss]

/-! ## Schläfli's identity for a 4-simplex -/

/-- `gram4` does not depend on the labelling (the labellings of the ten triangles used below). -/
theorem gram4_perm (ℓ : Finset V → ℝ) (p q r s u : V) :
    gram4 ℓ p q s r u = gram4 ℓ p q r s u ∧ gram4 ℓ p q u r s = gram4 ℓ p q r s u ∧
      gram4 ℓ p r s q u = gram4 ℓ p q r s u ∧ gram4 ℓ p r u q s = gram4 ℓ p q r s u ∧
      gram4 ℓ p s u q r = gram4 ℓ p q r s u ∧ gram4 ℓ q r s p u = gram4 ℓ p q r s u ∧
      gram4 ℓ q r u p s = gram4 ℓ p q r s u ∧ gram4 ℓ q s u p r = gram4 ℓ p q r s u ∧
      gram4 ℓ r s u p q = gram4 ℓ p q r s u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sq_ring

/-- A labelled 4-simplex is **non-degenerate**: its ten triangles, five tetrahedral facets and the
4-simplex itself have positive Gram determinants (positive area, volume and 4-volume). -/
structure Nondeg4 (ℓ : Finset V → ℝ) (p q r s u : V) : Prop where
  /-- Triangle `pqr`. -/
  t₁ : 0 < gram2 ℓ p q r
  /-- Triangle `pqs`. -/
  t₂ : 0 < gram2 ℓ p q s
  /-- Triangle `pqu`. -/
  t₃ : 0 < gram2 ℓ p q u
  /-- Triangle `prs`. -/
  t₄ : 0 < gram2 ℓ p r s
  /-- Triangle `pru`. -/
  t₅ : 0 < gram2 ℓ p r u
  /-- Triangle `psu`. -/
  t₆ : 0 < gram2 ℓ p s u
  /-- Triangle `qrs`. -/
  t₇ : 0 < gram2 ℓ q r s
  /-- Triangle `qru`. -/
  t₈ : 0 < gram2 ℓ q r u
  /-- Triangle `qsu`. -/
  t₉ : 0 < gram2 ℓ q s u
  /-- Triangle `rsu`. -/
  t₁₀ : 0 < gram2 ℓ r s u
  /-- Facet `pqrs`. -/
  f_u : 0 < gram3 ℓ p q r s
  /-- Facet `pqru`. -/
  f_s : 0 < gram3 ℓ p q r u
  /-- Facet `pqsu`. -/
  f_r : 0 < gram3 ℓ p q s u
  /-- Facet `prsu`. -/
  f_q : 0 < gram3 ℓ p r s u
  /-- Facet `qrsu`. -/
  f_p : 0 < gram3 ℓ q r s u
  /-- The 4-simplex. -/
  g4 : 0 < gram4 ℓ p q r s u

/-- The area-weighted sum of the dihedral angles of the labelled 4-simplex `pqrsu`, along the line
of lengths `ℓ + τ v`, with the areas `√gram2 / 2` held at `ℓ`. -/
noncomputable def areaAngleSum (ℓ v : Finset V → ℝ) (p q r s u : V) (τ : ℝ) : ℝ :=
  √(gram2 ℓ p q r) / 2 * dihedral4 (lineL ℓ v τ) p q r s u +
    √(gram2 ℓ p q s) / 2 * dihedral4 (lineL ℓ v τ) p q s r u +
    √(gram2 ℓ p q u) / 2 * dihedral4 (lineL ℓ v τ) p q u r s +
    √(gram2 ℓ p r s) / 2 * dihedral4 (lineL ℓ v τ) p r s q u +
    √(gram2 ℓ p r u) / 2 * dihedral4 (lineL ℓ v τ) p r u q s +
    √(gram2 ℓ p s u) / 2 * dihedral4 (lineL ℓ v τ) p s u q r +
    √(gram2 ℓ q r s) / 2 * dihedral4 (lineL ℓ v τ) q r s p u +
    √(gram2 ℓ q r u) / 2 * dihedral4 (lineL ℓ v τ) q r u p s +
    √(gram2 ℓ q s u) / 2 * dihedral4 (lineL ℓ v τ) q s u p r +
    √(gram2 ℓ r s u) / 2 * dihedral4 (lineL ℓ v τ) r s u p q

/-- **Schläfli's identity for a 4-simplex.** At a non-degenerate labelled 4-simplex, for every
direction `v` of change of the edge lengths, `Σ_t A_t dθ_t = 0`: the derivative at `τ = 0` of the
area-weighted angle sum (areas held fixed, angles varying) vanishes. -/
theorem schlaefli4 (ℓ v : Finset V → ℝ) {p q r s u : V} (h : Nondeg4 ℓ p q r s u) :
    HasDerivAt (areaAngleSum ℓ v p q r s u) 0 0 := by
  obtain ⟨g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀⟩ := gram4_perm ℓ p q r s u
  have d₁ := (hasDerivAt_dihedral4_line ℓ v p q r s u h.f_u h.f_s h.t₁ h.g4).const_mul
    (√(gram2 ℓ p q r) / 2)
  have d₂ := (hasDerivAt_dihedral4_line ℓ v p q s r u (by rw [gram3_swap_rs]; exact h.f_u) h.f_r
    h.t₂ (by rw [g₂]; exact h.g4)).const_mul (√(gram2 ℓ p q s) / 2)
  have d₃ := (hasDerivAt_dihedral4_line ℓ v p q u r s (by rw [gram3_swap_rs]; exact h.f_s)
    (by rw [gram3_swap_rs]; exact h.f_r) h.t₃ (by rw [g₃]; exact h.g4)).const_mul
    (√(gram2 ℓ p q u) / 2)
  have d₄ := (hasDerivAt_dihedral4_line ℓ v p r s q u (by rw [gram3_rot3]; exact h.f_u) h.f_q
    h.t₄ (by rw [g₄]; exact h.g4)).const_mul (√(gram2 ℓ p r s) / 2)
  have d₅ := (hasDerivAt_dihedral4_line ℓ v p r u q s (by rw [gram3_rot3]; exact h.f_s)
    (by rw [gram3_swap_rs]; exact h.f_q) h.t₅ (by rw [g₅]; exact h.g4)).const_mul
    (√(gram2 ℓ p r u) / 2)
  have d₆ := (hasDerivAt_dihedral4_line ℓ v p s u q r (by rw [gram3_rot3]; exact h.f_r)
    (by rw [gram3_rot3]; exact h.f_q) h.t₆ (by rw [g₆]; exact h.g4)).const_mul
    (√(gram2 ℓ p s u) / 2)
  have d₇ := (hasDerivAt_dihedral4_line ℓ v q r s p u (by rw [gram3_rot4]; exact h.f_u) h.f_p
    h.t₇ (by rw [g₇]; exact h.g4)).const_mul (√(gram2 ℓ q r s) / 2)
  have d₈ := (hasDerivAt_dihedral4_line ℓ v q r u p s (by rw [gram3_rot4]; exact h.f_s)
    (by rw [gram3_swap_rs]; exact h.f_p) h.t₈ (by rw [g₈]; exact h.g4)).const_mul
    (√(gram2 ℓ q r u) / 2)
  have d₉ := (hasDerivAt_dihedral4_line ℓ v q s u p r (by rw [gram3_rot4]; exact h.f_r)
    (by rw [gram3_rot3]; exact h.f_p) h.t₉ (by rw [g₉]; exact h.g4)).const_mul
    (√(gram2 ℓ q s u) / 2)
  have d₁₀ := (hasDerivAt_dihedral4_line ℓ v r s u p q (by rw [gram3_rot4]; exact h.f_q)
    (by rw [gram3_rot4]; exact h.f_p) h.t₁₀ (by rw [g₁₀]; exact h.g4)).const_mul
    (√(gram2 ℓ r s u) / 2)
  have hsum := (((((((((d₁.add d₂).add d₃).add d₄).add d₅).add d₆).add d₇).add d₈).add d₉).add d₁₀)
  convert hsum using 1
  · funext τ
    simp only [areaAngleSum, Pi.add_apply]
  -- the derivative: `Σ_t A_t θ_t' = 0`
  -- labelled facets are the canonical facets
  simp only [gram3_swap_rs _ p q r s, gram3_swap_rs _ p q r u, gram3_swap_rs _ p q s u,
    gram3_swap_rs _ p r s u, gram3_swap_rs _ q r s u, gram3_rot3 _ p q r s, gram3_rot3 _ p q r u,
    gram3_rot3 _ p q s u, gram3_rot3 _ p r s u, gram3_rot3 _ q r s u, gram3_rot4 _ p q r s,
    gram3_rot4 _ p q r u, gram3_rot4 _ p q s u, gram3_rot4 _ p r s u, gram3_rot4 _ q r s u,
    g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀]
  -- each term is `-B_t / (2 √gram4)`
  have key : ∀ (g2 B : ℝ), 0 < g2 →
      √g2 / 2 * (-B / √(g2 * gram4 ℓ p q r s u)) = -B / (2 * √(gram4 ℓ p q r s u)) := by
    intro g2 B hg
    rw [Real.sqrt_mul hg.le]
    have : √g2 ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
    field_simp
  rw [key _ _ h.t₁, key _ _ h.t₂, key _ _ h.t₃, key _ _ h.t₄, key _ _ h.t₅, key _ _ h.t₆,
    key _ _ h.t₇, key _ _ h.t₈, key _ _ h.t₉, key _ _ h.t₁₀]
  -- the derivative of the triangle sum
  have dm := fun a b c x y => (differentiable_mixed_lineL ℓ v a b c x y 0).hasDerivAt
  have dg := fun a b c x => (differentiable_gram3_lineL ℓ v a b c x 0).hasDerivAt
  have hL := (((((((((dm p q r s u).add (dm p q s r u)).add (dm p q u r s)).add
    (dm p r s q u)).add (dm p r u q s)).add (dm p s u q r)).add (dm q r s p u)).add
    (dm q r u p s)).add (dm q s u p r)).add (dm r s u p q)
  have hR := (((((dg p q r s).add (dg p q r u)).add (dg p q s u)).add (dg p r s u)).add
    (dg q r s u)).div_const 2
  have hfun : (fun τ => mixedSum (lineL ℓ v τ) p q r s u) =
      fun τ => gram3Sum (lineL ℓ v τ) p q r s u / 2 :=
    funext fun τ => sum_mixed_eq _ _ _ _ _ _
  have hdM := (show HasDerivAt (fun τ => mixedSum (lineL ℓ v τ) p q r s u) _ 0 from hL).unique
    (by rw [hfun]; exact hR)
  -- the facet identities at `ℓ`
  have fu := facet_identity ℓ p q r s u
  have fs := facet_identity ℓ p q r u s
  have fr := facet_identity ℓ p q s u r
  have fq := facet_identity ℓ p r s u q
  have fp := facet_identity ℓ q r s u p
  simp only [mixed_swap_su ℓ p q r s u, mixed_swap_su ℓ p q s r u, mixed_swap_su ℓ p q u r s,
    mixed_swap_su ℓ p r s q u, mixed_swap_su ℓ p r u q s, mixed_swap_su ℓ p s u q r,
    mixed_swap_su ℓ q r s p u, mixed_swap_su ℓ q r u p s, mixed_swap_su ℓ q s u p r,
    mixed_swap_su ℓ r s u p q] at fs fr fq fp
  -- logarithmic derivatives of the facets
  set Gu' := deriv (fun τ => gram3 (lineL ℓ v τ) p q r s) 0
  set Gs' := deriv (fun τ => gram3 (lineL ℓ v τ) p q r u) 0
  set Gr' := deriv (fun τ => gram3 (lineL ℓ v τ) p q s u) 0
  set Gq' := deriv (fun τ => gram3 (lineL ℓ v τ) p r s u) 0
  set Gp' := deriv (fun τ => gram3 (lineL ℓ v τ) q r s u) 0
  have eu : Gu' / gram3 ℓ p q r s * gram3 ℓ p q r s = Gu' := div_mul_cancel₀ _ h.f_u.ne'
  have es : Gs' / gram3 ℓ p q r u * gram3 ℓ p q r u = Gs' := div_mul_cancel₀ _ h.f_s.ne'
  have er : Gr' / gram3 ℓ p q s u * gram3 ℓ p q s u = Gr' := div_mul_cancel₀ _ h.f_r.ne'
  have eq : Gq' / gram3 ℓ p r s u * gram3 ℓ p r s u = Gq' := div_mul_cancel₀ _ h.f_q.ne'
  have ep : Gp' / gram3 ℓ q r s u * gram3 ℓ q r s u = Gp' := div_mul_cancel₀ _ h.f_p.ne'
  have hg4 : √(gram4 ℓ p q r s u) ≠ 0 := (Real.sqrt_pos.mpr h.g4).ne'
  linear_combination (1 / (2 * √(gram4 ℓ p q r s u))) * (hdM -
    (1 / 2 : ℝ) * (Gu' / gram3 ℓ p q r s * fu + Gs' / gram3 ℓ p q r u * fs +
      Gr' / gram3 ℓ p q s u * fr + Gq' / gram3 ℓ p r s u * fq + Gp' / gram3 ℓ q r s u * fp) -
    (1 / 2 : ℝ) * (eu + es + er + eq + ep))

/-! ## Labelling-free form -/

/-- The sum over the ten triangles of the 4-simplex `{p, q, r, s, u}`. -/
theorem sum_powersetCard_three_five {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u)
    (hsu : s ≠ u) (f : Finset V → ℝ) :
    ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3, f t =
      f {p, q, r} + f {p, q, s} + f {p, q, u} + f {p, r, s} + f {p, r, u} + f {p, s, u} +
        f {q, r, s} + f {q, r, u} + f {q, s, u} + f {r, s, u} := by
  rw [Lightlike.Regge.sum_powersetCard_succ_insert (by simp [hpq, hpr, hps, hpu]) 2,
    Lightlike.Regge.sum_powersetCard_three_four hqr hqs hqu hrs hru hsu,
    Lightlike.Regge.sum_powersetCard_two_four hqr hqs hqu hrs hru hsu, pair_comm s q]
  ring

/-- The dihedral angle at a triangle of a 4-simplex given as a set: if `σ = {a, b, c, x, y}`, the
angle at `{a, b, c}` is the length formula in this labelling. -/
theorem dihedralAt4_of_eq (ℓ : Finset V → ℝ) {σ : Finset V} {a b c x y : V}
    (hσ : σ = {a, b, c, x, y}) (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x) (hay : a ≠ y)
    (hbc : b ≠ c) (hbx : b ≠ x) (hby : b ≠ y) (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y) :
    dihedralAt4 ℓ σ {a, b, c} = dihedral4 ℓ a b c x y := by
  subst hσ
  exact dihedralAt4_eq ℓ hab hac hax hay hbc hbx hby hcx hcy hxy

/-- The area-weighted angle sum of a labelled 4-simplex is the labelling-free sum over its
triangles. -/
theorem sum_area_dihedralAt4 (ℓ v : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) (τ : ℝ) :
    ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
        area4 ℓ t * dihedralAt4 (lineL ℓ v τ) {p, q, r, s, u} t =
      areaAngleSum ℓ v p q r s u τ := by
  have e : ∀ {a b c x y : V}, ({p, q, r, s, u} : Finset V) = {a, b, c, x, y} → a ≠ b → a ≠ c →
      a ≠ x → a ≠ y → b ≠ c → b ≠ x → b ≠ y → c ≠ x → c ≠ y → x ≠ y →
      area4 ℓ {a, b, c} * dihedralAt4 (lineL ℓ v τ) {p, q, r, s, u} {a, b, c} =
        √(gram2 ℓ a b c) / 2 * dihedral4 (lineL ℓ v τ) a b c x y :=
    fun hσ hab hac hax hay hbc hbx hby hcx hcy hxy => by
      rw [area4_eq ℓ hab hac hbc, dihedralAt4_of_eq _ hσ hab hac hax hay hbc hbx hby hcx hcy hxy]
  rw [sum_powersetCard_three_five hpq hpr hps hpu hqr hqs hqu hrs hru hsu, areaAngleSum,
    e rfl hpq hpr hps hpu hqr hqs hqu hrs hru hsu,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hpq hps hpr hpu hqs hqr hqu
      hrs.symm hsu hru,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hpq hpu hpr hps hqu hqr hqs
      hru.symm hsu.symm hrs,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hpr hps hpq hpu hrs hqr.symm hru
      hqs.symm hsu hqu,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hpr hpu hpq hps hru hqr.symm hrs
      hqu.symm hsu.symm hqs,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hps hpu hpq hpr hsu hqs.symm
      hrs.symm hqu.symm hru.symm hqr,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hqr hqs hpq.symm hqu hrs
      hpr.symm hru hps.symm hsu hpu,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hqr hqu hpq.symm hqs hru
      hpr.symm hrs hpu.symm hsu.symm hps,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hqs hqu hpq.symm hqr hsu
      hps.symm hrs.symm hpu.symm hru.symm hpr,
    e (by ext z; simp only [mem_insert, mem_singleton]; tauto) hrs hru hpr.symm hqr.symm hsu
      hps.symm hqs.symm hpu.symm hqu.symm hpq]

/-- **Schläfli's identity, labelling-free.** For a non-degenerate 4-simplex `σ = {p, q, r, s, u}`
and every direction `v`, the derivative at `τ = 0` of `Σ_{t ⊂ σ} A_t θ_σ(t)` with the areas held
at `ℓ` and the angles taken at `ℓ + τ v` vanishes. -/
theorem schlaefli4_finset (ℓ v : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) (h : Nondeg4 ℓ p q r s u) :
    HasDerivAt (fun τ => ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
      area4 ℓ t * dihedralAt4 (lineL ℓ v τ) {p, q, r, s, u} t) 0 0 := by
  have : (fun τ => ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
      area4 ℓ t * dihedralAt4 (lineL ℓ v τ) {p, q, r, s, u} t) = areaAngleSum ℓ v p q r s u :=
    funext (sum_area_dihedralAt4 ℓ v hpq hpr hps hpu hqr hqs hqu hrs hru hsu)
  rw [this]
  exact schlaefli4 ℓ v h

end Lightlike.Regge4
