import Lightlike.Regge.Lorentzian.Complex
import Lightlike.Regge.D4.Schlaefli

/-!
# The Schläfli identity for a Lorentzian 4-simplex

For a Lorentzian 4-simplex with triangle areas `A_t` and Sorkin's complex dihedral angles `θ_t`
(`Lightlike/Regge/Lorentzian/Dihedral.lean`), **Schläfli's identity** says `Σ_t A_t dθ_t = 0` for every
variation of the ten signed squared edge lengths. Sorkin (1975) used it to derive the Lorentzian
Regge equations, as `Lightlike/Regge/Lorentzian/ReggeEquations.lean` does here.

## Method

The proof follows the Euclidean one (`Lightlike/Regge/D4/Schlaefli.lean`) with signed squared lengths. At
the triangle `pqr` with opposite vertices `s, u`, write `M = mixedL`, `G_s = gram3L(pqrs)`,
`G_u = gram3L(pqru)`. By Desnanot–Jacobi `G_s G_u − M² = gram2L · gram4L`, and `gram4L < 0` for a
Lorentzian 4-simplex. The angle is

* at a spacelike hinge (`gram2L > 0`, Lorentzian normal plane): Sorkin's angle
  `sorkinAngle G_s G_u M`, whose real part is `± arcosh (|M| / √(G_s G_u))` or
  `arsinh (M / √(−G_s G_u))` (a boost) and whose imaginary part is `−i π/2` times the number of
  light rays in the wedge;
* at a timelike hinge (`gram2L < 0`, Euclidean normal plane): `arccos (−M / √(G_s G_u))`.

In every branch the derivative along a line of lengths is real and equal to
`B / √|gram2L · gram4L|` with `B = dM − M (dG_s/G_s + dG_u/G_u)/2` (`hasDerivAt_lorDihedral4_line`).
The imaginary part is locally constant because the number of light rays in the wedge is
(`eventually_lightRays`); this needs the hinge and both tetrahedra to be non-null. With the area
`A = √|gram2L| / 2`, each term `A dθ` is `B / (2 √(−gram4L))`, and the facet identities
(`facet_identityL`, `sum_mixedL_eq`, the signed versions of the Euclidean ones) make the ten `B_t`
add up to zero. Schläfli's identity at random rational Lorentzian lengths, with a failing control,
is checked in `scripts/regge/lorentzian_check.py`.

## Main results

* `facet_identityL`, `sum_mixedL_eq`: the polynomial identities in signed squared lengths.
* `hasDerivAt_arcosh_ratio`, `hasDerivAt_neg_arcosh_ratio`, `hasDerivAt_arsinh_ratio`,
  `hasDerivAt_arccos_neg_ratio`, `hasDerivAt_sorkinAngle`: the derivative of each branch of the
  angle along a curve of Gram data.
* `hasDerivAt_lorDihedral4_line`: the derivative of a Lorentzian dihedral angle along a line of
  squared lengths, for both causal types of the hinge.
* `LorNondeg4`: a Lorentzian 4-simplex with no null triangle and no null tetrahedron.
* `lorSchlaefli4`: Schläfli's identity for a labelled Lorentzian 4-simplex;
  `lorSchlaefli4_finset`: the same, labelling-free, as a sum over the triangles of a 4-simplex.
-/

open Real Finset Filter Topology

namespace Lightlike.ReggeLor

open Lightlike.Regge4 (lineL lineL_zero det3)

variable {V : Type*} [DecidableEq V]

/-! ## Polynomial identities -/

/-- **The facet identity** in signed squared lengths: on the tetrahedron `pqrs` of the 4-simplex
`pqrsu`, the mixed determinants of its four triangles add up to `gram3L(pqrs)`. -/
theorem facet_identityL (L : Finset V → ℝ) (p q r s u : V) :
    mixedL L p q r s u + mixedL L p q s r u + mixedL L p r s q u + mixedL L q r s p u =
      gram3L L p q r s := by sqL_ring

/-- `gram3L` rotated in its last three points. -/
theorem gram3L_rot3 (L : Finset V → ℝ) (p q r s : V) : gram3L L p r s q = gram3L L p q r s := by
  sqL_ring

/-- `gram3L` rotated in all four points. -/
theorem gram3L_rot4 (L : Finset V → ℝ) (p q r s : V) : gram3L L q r s p = gram3L L p q r s := by
  sqL_ring

/-- The ten mixed determinants of a 4-simplex, one for each triangle. -/
noncomputable def mixedSumL (L : Finset V → ℝ) (p q r s u : V) : ℝ :=
  mixedL L p q r s u + mixedL L p q s r u + mixedL L p q u r s + mixedL L p r s q u +
    mixedL L p r u q s + mixedL L p s u q r + mixedL L q r s p u + mixedL L q r u p s +
    mixedL L q s u p r + mixedL L r s u p q

/-- The five `gram3L` of the tetrahedral facets of a 4-simplex. -/
noncomputable def gram3SumL (L : Finset V → ℝ) (p q r s u : V) : ℝ :=
  gram3L L p q r s + gram3L L p q r u + gram3L L p q s u + gram3L L p r s u + gram3L L q r s u

/-- **The triangle sum**: the ten mixed determinants add up to half the sum of the five facet
determinants. -/
theorem sum_mixedL_eq (L : Finset V → ℝ) (p q r s u : V) :
    mixedSumL L p q r s u = gram3SumL L p q r s u / 2 := by
  have fu := facet_identityL L p q r s u
  have fs := facet_identityL L p q r u s
  have fr := facet_identityL L p q s u r
  have fq := facet_identityL L p r s u q
  have fp := facet_identityL L q r s u p
  simp only [mixedL_swap_su L p q r s u, mixedL_swap_su L p q s r u, mixedL_swap_su L p q u r s,
    mixedL_swap_su L p r s q u, mixedL_swap_su L p r u q s, mixedL_swap_su L p s u q r,
    mixedL_swap_su L q r s p u, mixedL_swap_su L q r u p s, mixedL_swap_su L q s u p r,
    mixedL_swap_su L r s u p q] at fs fr fq fp
  unfold mixedSumL gram3SumL
  linarith

/-- `gram4L` does not depend on the labelling (the labellings of the ten triangles used below). -/
theorem gram4L_perm (L : Finset V → ℝ) (p q r s u : V) :
    gram4L L p q s r u = gram4L L p q r s u ∧ gram4L L p q u r s = gram4L L p q r s u ∧
      gram4L L p r s q u = gram4L L p q r s u ∧ gram4L L p r u q s = gram4L L p q r s u ∧
      gram4L L p s u q r = gram4L L p q r s u ∧ gram4L L q r s p u = gram4L L p q r s u ∧
      gram4L L q r u p s = gram4L L p q r s u ∧ gram4L L q s u p r = gram4L L p q r s u ∧
      gram4L L r s u p q = gram4L L p q r s u := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> sqL_ring

/-! ## Derivatives of the angle formulas

Along a curve `τ ↦ (a τ, b τ, m τ)` of Gram data, with `B = m' − m (a'/a + b'/b) / 2` at `τ = 0`,
every branch of the Lorentzian angle has derivative `B / √|m² − a b|`. -/

section Calculus

variable {a b m : ℝ → ℝ} {a' b' m' : ℝ}

/-- The derivative of the ratio `m / √(c a b)`. -/
theorem hasDerivAt_ratio (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) {c : ℝ} (hc : 0 < c * (a 0 * b 0)) :
    HasDerivAt (fun τ => m τ / √(c * (a τ * b τ)))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(c * (a 0 * b 0))) 0 := by
  have hP : HasDerivAt (fun τ => c * (a τ * b τ)) (c * (a' * b 0 + a 0 * b')) 0 :=
    (ha.mul hb).const_mul c
  have hS := hP.sqrt hc.ne'
  have hs : √(c * (a 0 * b 0)) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  refine (hm.div hS hs).congr_deriv ?_
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have ha0 : a 0 ≠ 0 := by rintro h; simp [h] at hc
  have hb0 : b 0 ≠ 0 := by rintro h; simp [h] at hc
  have hss : √(c * (a 0 * b 0)) ^ 2 = c * (a 0 * b 0) := Real.sq_sqrt hc.le
  rw [hss]
  field_simp
  rw [show c * a 0 * b 0 = c * (a 0 * b 0) by ring, hss]
  ring

/-- The `arcosh` branch (`0 < a b < m²`, `m > 0`). -/
theorem hasDerivAt_arcosh_ratio (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hP : 0 < a 0 * b 0) (hm0 : 0 < m 0) (hgap : a 0 * b 0 < m 0 ^ 2) :
    HasDerivAt (fun τ => arcosh (m τ / √(a τ * b τ)))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(m 0 ^ 2 - a 0 * b 0)) 0 := by
  have hK := hasDerivAt_ratio ha hb hm (c := 1) (by simpa using hP)
  simp only [one_mul] at hK
  have hsP : 0 < √(a 0 * b 0) := Real.sqrt_pos.mpr hP
  have hκ : 1 < m 0 / √(a 0 * b 0) := by
    rw [one_lt_div hsP, Real.sqrt_lt' hm0]
    exact hgap
  refine ((hasDerivAt_arcosh hκ).comp 0 hK).congr_deriv ?_
  have hsq : (m 0 / √(a 0 * b 0)) ^ 2 - 1 = (m 0 ^ 2 - a 0 * b 0) / (a 0 * b 0) := by
    rw [div_pow, Real.sq_sqrt hP.le, div_sub_one hP.ne']
  have hg : 0 < m 0 ^ 2 - a 0 * b 0 := by linarith
  have hsg : √(m 0 ^ 2 - a 0 * b 0) ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  rw [hsq, Real.sqrt_div hg.le]
  field_simp

/-- The `−arcosh(−·)` branch (`0 < a b < m²`, `m < 0`). -/
theorem hasDerivAt_neg_arcosh_ratio (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hP : 0 < a 0 * b 0) (hm0 : m 0 < 0) (hgap : a 0 * b 0 < m 0 ^ 2) :
    HasDerivAt (fun τ => -arcosh (-m τ / √(a τ * b τ)))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(m 0 ^ 2 - a 0 * b 0)) 0 := by
  have hm' : HasDerivAt (fun τ => -m τ) (-m') 0 := hm.neg
  have h := (hasDerivAt_arcosh_ratio ha hb hm' hP (by simpa using hm0)
    (by simpa [neg_sq] using hgap)).neg
  refine h.congr_deriv ?_
  rw [neg_sq]
  ring

/-- The `arsinh` branch (`a b < 0`). -/
theorem hasDerivAt_arsinh_ratio (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hP : a 0 * b 0 < 0) :
    HasDerivAt (fun τ => arsinh (m τ / √(-(a τ * b τ))))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(m 0 ^ 2 - a 0 * b 0)) 0 := by
  have hK := hasDerivAt_ratio ha hb hm (c := -1) (by linarith)
  simp only [neg_one_mul] at hK
  refine hK.arsinh.congr_deriv ?_
  have hP' : 0 < -(a 0 * b 0) := by linarith
  have hsq : 1 + (m 0 / √(-(a 0 * b 0))) ^ 2 = (m 0 ^ 2 - a 0 * b 0) / -(a 0 * b 0) := by
    rw [div_pow, Real.sq_sqrt hP'.le, eq_div_iff hP'.ne', add_mul, div_mul_cancel₀ _ hP'.ne']
    ring
  have hg : 0 < m 0 ^ 2 - a 0 * b 0 := by nlinarith
  have hsg : √(m 0 ^ 2 - a 0 * b 0) ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  have hsP : √(-(a 0 * b 0)) ≠ 0 := (Real.sqrt_pos.mpr hP').ne'
  rw [hsq, Real.sqrt_div hg.le, smul_eq_mul]
  field_simp

/-- The `arccos(−·)` branch (`m² < a b`). -/
theorem hasDerivAt_arccos_neg_ratio (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hgap : m 0 ^ 2 < a 0 * b 0) :
    HasDerivAt (fun τ => arccos (-m τ / √(a τ * b τ)))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(a 0 * b 0 - m 0 ^ 2)) 0 := by
  have hP : 0 < a 0 * b 0 := lt_of_le_of_lt (sq_nonneg _) hgap
  have hm' : HasDerivAt (fun τ => -m τ) (-m') 0 := hm.neg
  have hK := hasDerivAt_ratio ha hb hm' (c := 1) (by simpa using hP)
  simp only [one_mul] at hK
  have hsP : 0 < √(a 0 * b 0) := Real.sqrt_pos.mpr hP
  have hsq1 : (-m 0 / √(a 0 * b 0)) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hP.le, div_lt_one hP, neg_sq]
    exact hgap
  have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq1)
  refine ((Real.hasDerivAt_arccos hbd.1.ne' hbd.2.ne).comp 0 hK).congr_deriv ?_
  have hsq : 1 - (-m 0 / √(a 0 * b 0)) ^ 2 = (a 0 * b 0 - m 0 ^ 2) / (a 0 * b 0) := by
    rw [div_pow, Real.sq_sqrt hP.le, neg_sq, sub_div, div_self hP.ne']
  have hg : 0 < a 0 * b 0 - m 0 ^ 2 := by linarith
  have hsg : √(a 0 * b 0 - m 0 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  rw [hsq, Real.sqrt_div hg.le]
  field_simp
  ring

/-- The boost part along a curve of Gram data with `a b ≠ 0` and `a b < m²` (the Gram data of a
spacelike hinge in a Lorentzian 4-simplex): derivative `B / √(m² − a b)`. -/
theorem hasDerivAt_boostPart (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hP : a 0 * b 0 ≠ 0) (hgap : a 0 * b 0 < m 0 ^ 2) :
    HasDerivAt (fun τ => boostPart (a τ) (b τ) (m τ))
      ((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(m 0 ^ 2 - a 0 * b 0)) 0 := by
  have hc : ContinuousAt (fun τ => a τ * b τ) 0 := ha.continuousAt.mul hb.continuousAt
  rcases hP.lt_or_gt with hn | hp
  · refine (hasDerivAt_arsinh_ratio ha hb hm hn).congr_of_eventuallyEq ?_
    filter_upwards [hc.eventually (gt_mem_nhds hn)] with τ h1
    have h1' : a τ * b τ < 0 := h1
    simp only [boostPart, not_lt.mpr h1'.le, h1', ↓reduceIte]
  · have hm0 : m 0 ≠ 0 := fun h => by
      have := hp.trans hgap
      simp [h] at this
    rcases hm0.lt_or_gt with hmn | hmp
    · refine (hasDerivAt_neg_arcosh_ratio ha hb hm hp hmn hgap).congr_of_eventuallyEq ?_
      filter_upwards [hc.eventually (lt_mem_nhds hp),
        hm.continuousAt.eventually (gt_mem_nhds hmn)] with τ h1 h2
      have h1' : 0 < a τ * b τ := h1
      simp only [boostPart, h1', not_lt.mpr h2.le, ↓reduceIte]
    · refine (hasDerivAt_arcosh_ratio ha hb hm hp hmp hgap).congr_of_eventuallyEq ?_
      filter_upwards [hc.eventually (lt_mem_nhds hp),
        hm.continuousAt.eventually (lt_mem_nhds hmp)] with τ h1 h2
      have h1' : 0 < a τ * b τ := h1
      simp only [boostPart, h1', h2, ↓reduceIte]

/-- The number of light rays in the wedge is locally constant along a continuous curve of Gram
data of two non-null vectors (`a b ≠ 0`) that are not orthogonal when of the same causal type. -/
theorem eventually_lightRays (ha : ContinuousAt a 0) (hb : ContinuousAt b 0)
    (hm : ContinuousAt m 0) (hP : a 0 * b 0 ≠ 0) (hm0 : 0 < a 0 * b 0 → m 0 ≠ 0) :
    ∀ᶠ τ in 𝓝 0, lightRays (a τ) (b τ) (m τ) = lightRays (a 0) (b 0) (m 0) := by
  have hc : ContinuousAt (fun τ => a τ * b τ) 0 := ha.mul hb
  have hd : ContinuousAt (fun τ => a τ * m τ) 0 := ha.mul hm
  rcases hP.lt_or_gt with hn | hp
  · filter_upwards [hc.eventually (gt_mem_nhds hn)] with τ h1
    have h1' : a τ * b τ < 0 := h1
    simp only [lightRays, h1', hn, not_lt.mpr h1'.le, not_lt.mpr hn.le, ↓reduceIte]
  · have hd0 : a 0 * m 0 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul hp.ne') (hm0 hp)
    rcases hd0.lt_or_gt with hdn | hdp
    · filter_upwards [hc.eventually (lt_mem_nhds hp), hd.eventually (gt_mem_nhds hdn)]
        with τ h1 h2
      have h1' : 0 < a τ * b τ := h1
      have h2' : a τ * m τ < 0 := h2
      simp only [lightRays, h1', hp, not_lt.mpr h2'.le, not_lt.mpr hdn.le, ↓reduceIte]
    · filter_upwards [hc.eventually (lt_mem_nhds hp), hd.eventually (lt_mem_nhds hdp)]
        with τ h1 h2
      have h1' : 0 < a τ * b τ := h1
      have h2' : 0 < a τ * m τ := h2
      simp only [lightRays, h1', hp, h2', hdp, ↓reduceIte]

/-- **The derivative of Sorkin's angle** along a curve of Gram data with `a b ≠ 0` and `a b < m²`:
the imaginary part is locally constant, and the real part has derivative `B / √(m² − a b)`. -/
theorem hasDerivAt_sorkinAngle (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0)
    (hm : HasDerivAt m m' 0) (hP : a 0 * b 0 ≠ 0) (hgap : a 0 * b 0 < m 0 ^ 2) :
    HasDerivAt (fun τ => sorkinAngle (a τ) (b τ) (m τ))
      (((m' - m 0 * (a' / a 0 + b' / b 0) / 2) / √(m 0 ^ 2 - a 0 * b 0) : ℝ) : ℂ) 0 := by
  have hm0 : 0 < a 0 * b 0 → m 0 ≠ 0 := fun hp h => by
    have := hp.trans hgap
    simp [h] at this
  have hL := eventually_lightRays ha.continuousAt hb.continuousAt hm.continuousAt hP hm0
  refine ((hasDerivAt_boostPart ha hb hm hP hgap).ofReal_comp.sub_const
    (((π / 2 * (lightRays (a 0) (b 0) (m 0) : ℝ) : ℝ) : ℂ) * Complex.I)).congr_of_eventuallyEq ?_
  filter_upwards [hL] with τ hτ
  simp only [sorkinAngle, hτ]

end Calculus

/-! ## The dihedral angle along a line of squared lengths -/

/-- Signed squared lengths are differentiable along a line. -/
@[fun_prop] theorem differentiable_sqL_lineL (L v : Finset V → ℝ) (a b : V) :
    Differentiable ℝ fun τ => sqL (lineL L v τ) a b := by
  by_cases h : a = b
  · subst h
    simp only [sqL_self]
    fun_prop
  · simp only [sqL_of_ne _ h, lineL]
    fun_prop

/-- The mixed determinant is differentiable along a line of squared lengths. -/
theorem differentiable_mixedL_lineL (L v : Finset V → ℝ) (p q r s u : V) :
    Differentiable ℝ fun τ => mixedL (lineL L v τ) p q r s u := by
  unfold mixedL det3 ipL
  fun_prop

/-- `gram3L` is differentiable along a line of squared lengths. -/
theorem differentiable_gram3L_lineL (L v : Finset V → ℝ) (p q r s : V) :
    Differentiable ℝ fun τ => gram3L (lineL L v τ) p q r s := by
  unfold gram3L det3 ipL
  fun_prop

/-- `gram2L` is differentiable along a line of squared lengths. -/
theorem differentiable_gram2L_lineL (L v : Finset V → ℝ) (p q r : V) :
    Differentiable ℝ fun τ => gram2L (lineL L v τ) p q r := by
  unfold gram2L ipL
  fun_prop

/-- **The derivative of a Lorentzian dihedral angle along a line of squared lengths.** At a
Lorentzian 4-simplex (`gram4L < 0`) with a non-null hinge `pqr` (`gram2L ≠ 0`) and non-null
tetrahedra `pqrs`, `pqru` (`gram3L ≠ 0`), the angle at `pqr` along `L + τ v` has the real
derivative `(dM − M (dG_s/G_s + dG_u/G_u)/2) / √|gram2L · gram4L|` at `τ = 0`, for both causal
types of the hinge. (For a spacelike hinge the imaginary part of Sorkin's angle is locally
constant.) -/
theorem hasDerivAt_lorDihedral4_line (L v : Finset V → ℝ) (p q r s u : V)
    (hs : gram3L L p q r s ≠ 0) (hu : gram3L L p q r u ≠ 0) (h2 : gram2L L p q r ≠ 0)
    (h4 : gram4L L p q r s u < 0) :
    HasDerivAt (fun τ => lorDihedral4 (lineL L v τ) p q r s u)
      (((deriv (fun τ => mixedL (lineL L v τ) p q r s u) 0 - mixedL L p q r s u *
          (deriv (fun τ => gram3L (lineL L v τ) p q r s) 0 / gram3L L p q r s +
            deriv (fun τ => gram3L (lineL L v τ) p q r u) 0 / gram3L L p q r u) / 2) /
        √|gram2L L p q r * gram4L L p q r s u| : ℝ) : ℂ) 0 := by
  have hM := (differentiable_mixedL_lineL L v p q r s u 0).hasDerivAt
  have hGs := (differentiable_gram3L_lineL L v p q r s 0).hasDerivAt
  have hGu := (differentiable_gram3L_lineL L v p q r u 0).hasDerivAt
  have hc : ContinuousAt (fun τ => gram2L (lineL L v τ) p q r) 0 :=
    (differentiable_gram2L_lineL L v p q r).continuous.continuousAt
  have hdj := desnanot_jacobiL L p q r s u
  rcases h2.lt_or_gt with h2n | h2p
  · -- a timelike hinge: the Euclidean angle `arccos (−M / √(G_s G_u))`
    have hpos := mul_pos_of_neg_of_neg h2n h4
    have hA := hasDerivAt_arccos_neg_ratio hGs hGu hM (by simp only [lineL_zero]; linarith)
    simp only [lineL_zero] at hA
    refine (hA.ofReal_comp.congr_of_eventuallyEq ?_).congr_deriv ?_
    · have h2n' : gram2L (lineL L v 0) p q r < 0 := by simpa using h2n
      filter_upwards [hc.eventually (gt_mem_nhds h2n')] with τ hτ
      have hτ' : gram2L (lineL L v τ) p q r < 0 := hτ
      simp only [lorDihedral4, hτ', not_lt.mpr hτ'.le, ↓reduceIte]
    · rw [abs_of_pos hpos, ← hdj]
  · -- a spacelike hinge: Sorkin's angle
    have hneg := mul_neg_of_pos_of_neg h2p h4
    have hS := hasDerivAt_sorkinAngle hGs hGu hM
      (by simp only [lineL_zero]; exact mul_ne_zero hs hu) (by simp only [lineL_zero]; linarith)
    simp only [lineL_zero] at hS
    refine (hS.congr_of_eventuallyEq ?_).congr_deriv ?_
    · have h2p' : 0 < gram2L (lineL L v 0) p q r := by simpa using h2p
      filter_upwards [hc.eventually (lt_mem_nhds h2p')] with τ hτ
      have hτ' : 0 < gram2L (lineL L v τ) p q r := hτ
      simp only [lorDihedral4, hτ', ↓reduceIte]
    · have he : mixedL L p q r s u ^ 2 - gram3L L p q r s * gram3L L p q r u =
          -(gram2L L p q r * gram4L L p q r s u) := by linarith
      rw [abs_of_neg hneg, ← he]

/-! ## Schläfli's identity for a Lorentzian 4-simplex -/

/-- A labelled 4-simplex is **Lorentzian and non-degenerate**: its ten triangles and five
tetrahedral facets are non-null (non-zero Gram determinants) and the 4-simplex itself is
Lorentzian (negative Gram determinant). -/
structure LorNondeg4 (L : Finset V → ℝ) (p q r s u : V) : Prop where
  /-- Triangle `pqr`. -/
  t₁ : gram2L L p q r ≠ 0
  /-- Triangle `pqs`. -/
  t₂ : gram2L L p q s ≠ 0
  /-- Triangle `pqu`. -/
  t₃ : gram2L L p q u ≠ 0
  /-- Triangle `prs`. -/
  t₄ : gram2L L p r s ≠ 0
  /-- Triangle `pru`. -/
  t₅ : gram2L L p r u ≠ 0
  /-- Triangle `psu`. -/
  t₆ : gram2L L p s u ≠ 0
  /-- Triangle `qrs`. -/
  t₇ : gram2L L q r s ≠ 0
  /-- Triangle `qru`. -/
  t₈ : gram2L L q r u ≠ 0
  /-- Triangle `qsu`. -/
  t₉ : gram2L L q s u ≠ 0
  /-- Triangle `rsu`. -/
  t₁₀ : gram2L L r s u ≠ 0
  /-- Facet `pqrs`. -/
  f_u : gram3L L p q r s ≠ 0
  /-- Facet `pqru`. -/
  f_s : gram3L L p q r u ≠ 0
  /-- Facet `pqsu`. -/
  f_r : gram3L L p q s u ≠ 0
  /-- Facet `prsu`. -/
  f_q : gram3L L p r s u ≠ 0
  /-- Facet `qrsu`. -/
  f_p : gram3L L q r s u ≠ 0
  /-- The 4-simplex is Lorentzian. -/
  g4 : gram4L L p q r s u < 0

/-- The area-weighted sum of the Lorentzian dihedral angles of the labelled 4-simplex `pqrsu`,
along the line of squared lengths `L + τ v`, with the areas `√|gram2L| / 2` held at `L`. -/
noncomputable def lorAreaAngleSum (L v : Finset V → ℝ) (p q r s u : V) (τ : ℝ) : ℂ :=
  ((√|gram2L L p q r| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p q r s u +
    ((√|gram2L L p q s| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p q s r u +
    ((√|gram2L L p q u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p q u r s +
    ((√|gram2L L p r s| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p r s q u +
    ((√|gram2L L p r u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p r u q s +
    ((√|gram2L L p s u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) p s u q r +
    ((√|gram2L L q r s| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) q r s p u +
    ((√|gram2L L q r u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) q r u p s +
    ((√|gram2L L q s u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) q s u p r +
    ((√|gram2L L r s u| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) r s u p q

/-- **Schläfli's identity for a Lorentzian 4-simplex.** At a non-degenerate Lorentzian labelled
4-simplex, for every direction `v` of change of the signed squared edge lengths,
`Σ_t A_t dθ_t = 0`: the derivative at `τ = 0` of the area-weighted sum of the complex dihedral
angles (areas held fixed) vanishes. Each term `A_t dθ_t` is `B_t / (2 √(−gram4L))`, real, and the
`B_t` add up to zero by the facet identities. -/
theorem lorSchlaefli4 (L v : Finset V → ℝ) {p q r s u : V} (h : LorNondeg4 L p q r s u) :
    HasDerivAt (lorAreaAngleSum L v p q r s u) 0 0 := by
  obtain ⟨g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀⟩ := gram4L_perm L p q r s u
  have d₁ := (hasDerivAt_lorDihedral4_line L v p q r s u h.f_u h.f_s h.t₁ h.g4).const_mul
    ((√|gram2L L p q r| / 2 : ℝ) : ℂ)
  have d₂ := (hasDerivAt_lorDihedral4_line L v p q s r u (by rw [gram3L_swap_rs]; exact h.f_u)
    h.f_r h.t₂ (by rw [g₂]; exact h.g4)).const_mul ((√|gram2L L p q s| / 2 : ℝ) : ℂ)
  have d₃ := (hasDerivAt_lorDihedral4_line L v p q u r s (by rw [gram3L_swap_rs]; exact h.f_s)
    (by rw [gram3L_swap_rs]; exact h.f_r) h.t₃ (by rw [g₃]; exact h.g4)).const_mul
    ((√|gram2L L p q u| / 2 : ℝ) : ℂ)
  have d₄ := (hasDerivAt_lorDihedral4_line L v p r s q u (by rw [gram3L_rot3]; exact h.f_u)
    h.f_q h.t₄ (by rw [g₄]; exact h.g4)).const_mul ((√|gram2L L p r s| / 2 : ℝ) : ℂ)
  have d₅ := (hasDerivAt_lorDihedral4_line L v p r u q s (by rw [gram3L_rot3]; exact h.f_s)
    (by rw [gram3L_swap_rs]; exact h.f_q) h.t₅ (by rw [g₅]; exact h.g4)).const_mul
    ((√|gram2L L p r u| / 2 : ℝ) : ℂ)
  have d₆ := (hasDerivAt_lorDihedral4_line L v p s u q r (by rw [gram3L_rot3]; exact h.f_r)
    (by rw [gram3L_rot3]; exact h.f_q) h.t₆ (by rw [g₆]; exact h.g4)).const_mul
    ((√|gram2L L p s u| / 2 : ℝ) : ℂ)
  have d₇ := (hasDerivAt_lorDihedral4_line L v q r s p u (by rw [gram3L_rot4]; exact h.f_u)
    h.f_p h.t₇ (by rw [g₇]; exact h.g4)).const_mul ((√|gram2L L q r s| / 2 : ℝ) : ℂ)
  have d₈ := (hasDerivAt_lorDihedral4_line L v q r u p s (by rw [gram3L_rot4]; exact h.f_s)
    (by rw [gram3L_swap_rs]; exact h.f_p) h.t₈ (by rw [g₈]; exact h.g4)).const_mul
    ((√|gram2L L q r u| / 2 : ℝ) : ℂ)
  have d₉ := (hasDerivAt_lorDihedral4_line L v q s u p r (by rw [gram3L_rot4]; exact h.f_r)
    (by rw [gram3L_rot3]; exact h.f_p) h.t₉ (by rw [g₉]; exact h.g4)).const_mul
    ((√|gram2L L q s u| / 2 : ℝ) : ℂ)
  have d₁₀ := (hasDerivAt_lorDihedral4_line L v r s u p q (by rw [gram3L_rot4]; exact h.f_q)
    (by rw [gram3L_rot4]; exact h.f_p) h.t₁₀ (by rw [g₁₀]; exact h.g4)).const_mul
    ((√|gram2L L r s u| / 2 : ℝ) : ℂ)
  have hsum := (((((((((d₁.add d₂).add d₃).add d₄).add d₅).add d₆).add d₇).add d₈).add d₉).add d₁₀)
  convert hsum using 1
  · funext τ
    simp only [lorAreaAngleSum, Pi.add_apply]
  -- the derivative is real
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add]
  rw [← Complex.ofReal_zero, Complex.ofReal_inj]
  -- labelled facets are the canonical facets
  simp only [gram3L_swap_rs _ p q r s, gram3L_swap_rs _ p q r u, gram3L_swap_rs _ p q s u,
    gram3L_swap_rs _ p r s u, gram3L_swap_rs _ q r s u, gram3L_rot3 _ p q r s,
    gram3L_rot3 _ p q r u, gram3L_rot3 _ p q s u, gram3L_rot3 _ p r s u, gram3L_rot3 _ q r s u,
    gram3L_rot4 _ p q r s, gram3L_rot4 _ p q r u, gram3L_rot4 _ p q s u, gram3L_rot4 _ p r s u,
    gram3L_rot4 _ q r s u, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀]
  -- each term is `B_t / (2 √(−gram4L))`
  have hG : √(-gram4L L p q r s u) ≠ 0 := (Real.sqrt_pos.mpr (neg_pos.mpr h.g4)).ne'
  have key : ∀ (g2 B : ℝ), g2 ≠ 0 →
      √|g2| / 2 * (B / √|g2 * gram4L L p q r s u|) = B / (2 * √(-gram4L L p q r s u)) := by
    intro g2 B hg
    rw [abs_mul, abs_of_neg h.g4, Real.sqrt_mul (abs_nonneg _)]
    have : √|g2| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr hg)).ne'
    field_simp
  rw [key _ _ h.t₁, key _ _ h.t₂, key _ _ h.t₃, key _ _ h.t₄, key _ _ h.t₅, key _ _ h.t₆,
    key _ _ h.t₇, key _ _ h.t₈, key _ _ h.t₉, key _ _ h.t₁₀]
  -- the derivative of the triangle sum
  have dm := fun a b c x y => (differentiable_mixedL_lineL L v a b c x y 0).hasDerivAt
  have dg := fun a b c x => (differentiable_gram3L_lineL L v a b c x 0).hasDerivAt
  have hL := (((((((((dm p q r s u).add (dm p q s r u)).add (dm p q u r s)).add
    (dm p r s q u)).add (dm p r u q s)).add (dm p s u q r)).add (dm q r s p u)).add
    (dm q r u p s)).add (dm q s u p r)).add (dm r s u p q)
  have hR := (((((dg p q r s).add (dg p q r u)).add (dg p q s u)).add (dg p r s u)).add
    (dg q r s u)).div_const 2
  have hfun : (fun τ => mixedSumL (lineL L v τ) p q r s u) =
      fun τ => gram3SumL (lineL L v τ) p q r s u / 2 :=
    funext fun τ => sum_mixedL_eq _ _ _ _ _ _
  have hdM := (show HasDerivAt (fun τ => mixedSumL (lineL L v τ) p q r s u) _ 0 from hL).unique
    (by rw [hfun]; exact hR)
  -- the facet identities at `L`
  have fu := facet_identityL L p q r s u
  have fs := facet_identityL L p q r u s
  have fr := facet_identityL L p q s u r
  have fq := facet_identityL L p r s u q
  have fp := facet_identityL L q r s u p
  simp only [mixedL_swap_su L p q r s u, mixedL_swap_su L p q s r u, mixedL_swap_su L p q u r s,
    mixedL_swap_su L p r s q u, mixedL_swap_su L p r u q s, mixedL_swap_su L p s u q r,
    mixedL_swap_su L q r s p u, mixedL_swap_su L q r u p s, mixedL_swap_su L q s u p r,
    mixedL_swap_su L r s u p q] at fs fr fq fp
  -- logarithmic derivatives of the facets
  set Gu' := deriv (fun τ => gram3L (lineL L v τ) p q r s) 0
  set Gs' := deriv (fun τ => gram3L (lineL L v τ) p q r u) 0
  set Gr' := deriv (fun τ => gram3L (lineL L v τ) p q s u) 0
  set Gq' := deriv (fun τ => gram3L (lineL L v τ) p r s u) 0
  set Gp' := deriv (fun τ => gram3L (lineL L v τ) q r s u) 0
  have eu : Gu' / gram3L L p q r s * gram3L L p q r s = Gu' := div_mul_cancel₀ _ h.f_u
  have es : Gs' / gram3L L p q r u * gram3L L p q r u = Gs' := div_mul_cancel₀ _ h.f_s
  have er : Gr' / gram3L L p q s u * gram3L L p q s u = Gr' := div_mul_cancel₀ _ h.f_r
  have eq : Gq' / gram3L L p r s u * gram3L L p r s u = Gq' := div_mul_cancel₀ _ h.f_q
  have ep : Gp' / gram3L L q r s u * gram3L L q r s u = Gp' := div_mul_cancel₀ _ h.f_p
  linear_combination (-1 / (2 * √(-gram4L L p q r s u))) * (hdM -
    (1 / 2 : ℝ) * (Gu' / gram3L L p q r s * fu + Gs' / gram3L L p q r u * fs +
      Gr' / gram3L L p q s u * fr + Gq' / gram3L L p r s u * fq + Gp' / gram3L L q r s u * fp) -
    (1 / 2 : ℝ) * (eu + es + er + eq + ep))

/-! ## Labelling-free form -/

/-- The sum over the ten triangles of the 4-simplex `{p, q, r, s, u}`, for complex values. -/
theorem sum_powersetCard_three_five_complex {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) (f : Finset V → ℂ) :
    ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3, f t =
      f {p, q, r} + f {p, q, s} + f {p, q, u} + f {p, r, s} + f {p, r, u} + f {p, s, u} +
        f {q, r, s} + f {q, r, u} + f {q, s, u} + f {r, s, u} := by
  apply Complex.ext <;> simp only [Complex.re_sum, Complex.im_sum, Complex.add_re, Complex.add_im]
  · exact Lightlike.Regge4.sum_powersetCard_three_five hpq hpr hps hpu hqr hqs hqu hrs hru hsu
      (fun t => (f t).re)
  · exact Lightlike.Regge4.sum_powersetCard_three_five hpq hpr hps hpu hqr hqs hqu hrs hru hsu
      (fun t => (f t).im)

/-- The Lorentzian dihedral angle at a triangle of a 4-simplex given as a set: if
`σ = {a, b, c, x, y}`, the angle at `{a, b, c}` is the length formula in this labelling. -/
theorem lorDihedralAt_of_eq (L : Finset V → ℝ) {σ : Finset V} {a b c x y : V}
    (hσ : σ = {a, b, c, x, y}) (hab : a ≠ b) (hac : a ≠ c) (hax : a ≠ x) (hay : a ≠ y)
    (hbc : b ≠ c) (hbx : b ≠ x) (hby : b ≠ y) (hcx : c ≠ x) (hcy : c ≠ y) (hxy : x ≠ y) :
    lorDihedralAt L σ {a, b, c} = lorDihedral4 L a b c x y := by
  subst hσ
  exact lorDihedralAt_eq L hab hac hax hay hbc hbx hby hcx hcy hxy

/-- The area-weighted Lorentzian angle sum of a labelled 4-simplex is the labelling-free sum over
its triangles. -/
theorem sum_area_lorDihedralAt (L v : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) (τ : ℝ) :
    ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
        (lorArea L t : ℂ) * lorDihedralAt (lineL L v τ) {p, q, r, s, u} t =
      lorAreaAngleSum L v p q r s u τ := by
  have e : ∀ {a b c x y : V}, ({p, q, r, s, u} : Finset V) = {a, b, c, x, y} → a ≠ b → a ≠ c →
      a ≠ x → a ≠ y → b ≠ c → b ≠ x → b ≠ y → c ≠ x → c ≠ y → x ≠ y →
      (lorArea L {a, b, c} : ℂ) * lorDihedralAt (lineL L v τ) {p, q, r, s, u} {a, b, c} =
        ((√|gram2L L a b c| / 2 : ℝ) : ℂ) * lorDihedral4 (lineL L v τ) a b c x y :=
    fun hσ hab hac hax hay hbc hbx hby hcx hcy hxy => by
      rw [lorArea_eq L hab hac hbc,
        lorDihedralAt_of_eq _ hσ hab hac hax hay hbc hbx hby hcx hcy hxy]
  rw [sum_powersetCard_three_five_complex hpq hpr hps hpu hqr hqs hqu hrs hru hsu,
    lorAreaAngleSum,
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

/-- **Lorentzian Schläfli identity, labelling-free.** For a non-degenerate Lorentzian 4-simplex
`σ = {p, q, r, s, u}` and every direction `v`, the derivative at `τ = 0` of
`Σ_{t ⊂ σ} A_t θ_σ(t)`, with the areas held at `L` and the complex angles taken at `L + τ v`,
vanishes. -/
theorem lorSchlaefli4_finset (L v : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) (h : LorNondeg4 L p q r s u) :
    HasDerivAt (fun τ => ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
      (lorArea L t : ℂ) * lorDihedralAt (lineL L v τ) {p, q, r, s, u} t) 0 0 := by
  have : (fun τ => ∑ t ∈ ({p, q, r, s, u} : Finset V).powersetCard 3,
      (lorArea L t : ℂ) * lorDihedralAt (lineL L v τ) {p, q, r, s, u} t) =
        lorAreaAngleSum L v p q r s u :=
    funext (sum_area_lorDihedralAt L v hpq hpr hps hpu hqr hqs hqu hrs hru hsu)
  rw [this]
  exact lorSchlaefli4 L v h

end Lightlike.ReggeLor
