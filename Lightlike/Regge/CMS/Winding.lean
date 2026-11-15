import Mathlib
import Lightlike.Regge.CMS.Fat

/-!
# The angles around a star are invariant under orientation preserving linear maps (RC6b, step 4a)

Around a vertex `v` the comparison of Regge's deficit with the continuum uses the angles measured
with the metric `g(v)` frozen at `v`. These are the Euclidean angles of the image of the star
under a linear map `A` with `g(v) = Aᵀ A`. The star winds once around `v`, so its angles add up to
`2π`, and this file shows that this does not change under `A` when `A` preserves orientation.

The plane is `ℂ`. A star around `0` is a cyclic list `u i` of nonzero vectors with each
consecutive pair positively oriented, `Im (u (i + 1) * conj (u i)) > 0`. An orientation preserving
real linear map of `ℂ` is `z ↦ α z + β z̄` with `|β| < |α|`. The proof deforms it to `z ↦ α z`
through the maps `z ↦ α z + t β z̄`, which stay orientation preserving: the sum of the angles is
continuous in `t` and always a multiple of `2π`, so it is constant.

## Main results

* `IsPosStar u`: the positive orientation condition.
* `sum_angle_linear`: for `|β| < |α|` and `IsPosStar u`, the sum of the angles
  `∠ (A u i) (A u (i + 1))` equals the sum of `∠ (u i) (u (i + 1))`, where `A z = α z + β z̄`.
* `axisStar_isPosStar`, `axisStar_angle_sum`: the four vectors `1, i, -1, -i` form a positively
  oriented star with angle sum `2π`, so the hypotheses are met.
-/

open Real Complex

namespace Lightlike.CMS

variable {n : ℕ} [NeZero n]

/-- A cyclic list `u` of vectors of the plane `ℂ` is a **positively oriented star** if every
consecutive pair is positively oriented: `Im (u (i + 1) * conj (u i)) > 0`. -/
def IsPosStar (u : ZMod n → ℂ) : Prop := ∀ i, 0 < (u (i + 1) * (starRingEnd ℂ) (u i)).im

theorem prod_succ_div {f : ZMod n → ℂ} (hf : ∀ i, f i ≠ 0) : ∏ i, f (i + 1) / f i = 1 := by
  rw [Finset.prod_div_distrib]
  have : ∏ i, f (i + 1) = ∏ i, f i :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ fun _ => rfl
  rw [this]
  exact div_self (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)

/-- A cyclic product equal to `1` of nonzero complex numbers has arguments adding up to a multiple
of `2π`. -/
theorem sum_arg_mem {q : ZMod n → ℂ} (hq : ∀ i, q i ≠ 0) (hp : ∏ i, q i = 1) :
    ∃ k : ℤ, ∑ i, arg (q i) = 2 * π * k := by
  have h1 : exp ((∑ i, arg (q i) : ℝ) * I) = 1 := by
    have hnorm : ∏ i, ‖q i‖ = 1 := by
      rw [← norm_prod, hp, norm_one]
    have hexp : ∀ i, exp (arg (q i) * I) = q i / ‖q i‖ := by
      intro i
      have := Complex.norm_mul_exp_arg_mul_I (q i)
      have hn : (‖q i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hq i)
      field_simp
      rw [mul_comm]; exact this
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, Finset.prod_congr rfl fun i _ => hexp i,
      Finset.prod_div_distrib, hp, ← Complex.ofReal_prod, hnorm]
    simp
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simp at this
  linarith

/-- The family of linear maps `z ↦ α z + t β z̄`. -/
def lin (α β : ℂ) (t : ℝ) (z : ℂ) : ℂ := α * z + t * β * (starRingEnd ℂ) z

/-- The linear maps `z ↦ α z + t β z̄` multiply the orientation of a pair by `|α|² - t² |β|²`. -/
theorem lin_orient (α β : ℂ) (t : ℝ) (z w : ℂ) :
    (lin α β t w * (starRingEnd ℂ) (lin α β t z)).im =
      (‖α‖ ^ 2 - t ^ 2 * ‖β‖ ^ 2) * (w * (starRingEnd ℂ) z).im := by
  simp only [lin, Complex.mul_im, Complex.mul_re, map_add, map_mul, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_ofReal,
    Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  ring

section Deform

variable {u : ZMod n → ℂ} {α β : ℂ}

theorem lin_orient_pos (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : ZMod n) : 0 < (lin α β t (u (i + 1)) * (starRingEnd ℂ) (lin α β t (u i))).im := by
  rw [lin_orient]
  refine mul_pos ?_ (hu i)
  have h0 : 0 ≤ ‖β‖ := norm_nonneg _
  have : t ^ 2 * ‖β‖ ^ 2 ≤ ‖β‖ ^ 2 := by
    have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [sq_nonneg ‖β‖]
  nlinarith [sq_nonneg ‖β‖]

theorem lin_ne_zero (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : ZMod n) : lin α β t (u i) ≠ 0 := by
  intro h
  have := lin_orient_pos hu hβ ht i
  rw [h] at this
  simp at this

theorem lin_ratio_im_pos (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : ZMod n) : 0 < (lin α β t (u (i + 1)) / lin α β t (u i)).im := by
  have h := lin_orient_pos hu hβ ht i
  have hne := lin_ne_zero hu hβ ht i
  set a := lin α β t (u (i + 1))
  set b := lin α β t (u i)
  have hns : 0 < Complex.normSq b := Complex.normSq_pos.mpr hne
  rw [Complex.div_im]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
  have : a.im * b.re / Complex.normSq b - a.re * b.im / Complex.normSq b =
      (a.re * -b.im + a.im * b.re) / Complex.normSq b := by ring
  rw [this]
  exact div_pos h hns

/-- The sum of the arguments of the consecutive ratios of the image of `u` under `lin α β t`. -/
noncomputable def argSum (α β : ℂ) (u : ZMod n → ℂ) (t : ℝ) : ℝ :=
  ∑ i, arg (lin α β t (u (i + 1)) / lin α β t (u i))

theorem argSum_mem (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ k : ℤ, argSum α β u t = 2 * π * k := by
  refine sum_arg_mem (q := fun i => lin α β t (u (i + 1)) / lin α β t (u i)) (fun i => ?_) ?_
  · exact div_ne_zero (lin_ne_zero hu hβ ht _) (lin_ne_zero hu hβ ht i)
  · exact prod_succ_div (f := fun i => lin α β t (u i)) (fun i => lin_ne_zero hu hβ ht i)

theorem continuousOn_argSum (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) :
    ContinuousOn (argSum α β u) (Set.Icc 0 1) := by
  refine continuousOn_finsetSum _ fun i _ => fun t ht => ?_
  have hc : ContinuousAt (fun t : ℝ => lin α β t (u (i + 1)) / lin α β t (u i)) t := by
    refine ContinuousAt.div ?_ ?_ (lin_ne_zero hu hβ ht i)
    · unfold lin; fun_prop
    · unfold lin; fun_prop
  have hslit : lin α β t (u (i + 1)) / lin α β t (u i) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (lin_ratio_im_pos hu hβ ht i).ne')
  exact (ContinuousAt.comp (g := Complex.arg) (f := fun t : ℝ => lin α β t (u (i + 1)) / lin α β t (u i))
    (Complex.continuousAt_arg hslit) hc).continuousWithinAt

/-- A value of a continuous function on `[0, 1]` that is a multiple of `2π` at both ends and at
every point cannot jump: the end values agree. -/
theorem argSum_one_eq_zero (hu : IsPosStar u) (hβ : ‖β‖ < ‖α‖) :
    argSum α β u 1 = argSum α β u 0 := by
  have hcont := continuousOn_argSum hu hβ
  obtain ⟨k1, h1⟩ := argSum_mem hu hβ (t := 1) ⟨zero_le_one, le_rfl⟩
  obtain ⟨k0, h0⟩ := argSum_mem hu hβ (t := 0) ⟨le_rfl, zero_le_one⟩
  have hπ := Real.pi_pos
  -- `F t = F a + π` is impossible, since both are multiples of `2π`
  have hno : ∀ (a : ℤ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      argSum α β u t ≠ 2 * π * a + π := by
    intro a t ht h
    obtain ⟨k, hk⟩ := argSum_mem hu hβ ht
    have : π * (2 * ((k : ℝ) - a)) = π * 1 := by linarith
    have hk2 := mul_left_cancel₀ hπ.ne' this
    have : (2 : ℤ) * (k - a) = 1 := by exact_mod_cast hk2
    omega
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hk : (k1 : ℝ) + 1 ≤ k0 := by
      have : (k1 : ℝ) < k0 := by
        have : 2 * π * k1 < 2 * π * k0 := by linarith
        exact lt_of_mul_lt_mul_left this (by positivity)
      exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast this)
    have hmem : argSum α β u 1 + π ∈ Set.Icc (argSum α β u 1) (argSum α β u 0) :=
      ⟨by linarith, by nlinarith⟩
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont hmem
    exact hno k1 t ht (by rw [hFt, h1])
  · have hk : (k0 : ℝ) + 1 ≤ k1 := by
      have : (k0 : ℝ) < k1 := by
        have : 2 * π * k0 < 2 * π * k1 := by linarith
        exact lt_of_mul_lt_mul_left this (by positivity)
      exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast this)
    have hmem : argSum α β u 0 + π ∈ Set.Icc (argSum α β u 0) (argSum α β u 1) :=
      ⟨by linarith, by nlinarith⟩
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont hmem
    exact hno k0 t ht (by rw [hFt, h0])

end Deform

/-- For a positively oriented pair, the angle between the two vectors is the argument of their
ratio. -/
theorem angle_eq_arg {a b : ℂ} (h : 0 < (a * (starRingEnd ℂ) b).im) :
    InnerProductGeometry.angle b a = arg (a / b) := by
  have hb : b ≠ 0 := by rintro rfl; simp at h
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have him : 0 < (a / b).im := by
    have hns : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
    rw [Complex.div_im]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h
    have : a.im * b.re / Complex.normSq b - a.re * b.im / Complex.normSq b =
        (a.re * -b.im + a.im * b.re) / Complex.normSq b := by ring
    rw [this]; exact div_pos h hns
  rw [InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg ha hb,
    abs_of_nonneg (Complex.arg_nonneg_iff.mpr him.le)]

/-- **The angles around a star are invariant under orientation preserving linear maps.** If `u` is
a positively oriented star and `A z = α z + β z̄` with `|β| < |α|` (every orientation preserving real
linear map of `ℂ`), then the sum of the angles between consecutive vectors is the same for `A u`
as for `u`. -/
theorem sum_angle_linear {u : ZMod n → ℂ} (hu : IsPosStar u) {α β : ℂ} (hβ : ‖β‖ < ‖α‖) :
    ∑ i, InnerProductGeometry.angle (lin α β 1 (u i)) (lin α β 1 (u (i + 1))) =
      ∑ i, InnerProductGeometry.angle (u i) (u (i + 1)) := by
  have hα : α ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hβ
    exact absurd hβ (not_lt.mpr (norm_nonneg _))
  have h1 : ∑ i, InnerProductGeometry.angle (lin α β 1 (u i)) (lin α β 1 (u (i + 1))) =
      argSum α β u 1 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact angle_eq_arg (lin_orient_pos hu hβ ⟨zero_le_one, le_rfl⟩ i)
  have h0 : ∑ i, InnerProductGeometry.angle (u i) (u (i + 1)) = argSum α β u 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [angle_eq_arg (hu i)]
    simp only [lin, Complex.ofReal_zero, zero_mul, add_zero]
    rw [mul_div_mul_left _ _ hα]
  rw [h1, h0, argSum_one_eq_zero hu hβ]

/-! ## Non-vacuity: the four axis vectors -/

/-- The vectors `1, i, -1, -i`, cyclically. -/
noncomputable def axisStar : ZMod 4 → ℂ := ![1, I, -1, -I]

theorem axisStar_isPosStar : IsPosStar axisStar := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  rcases hi with rfl | rfl | rfl | rfl <;> simp [axisStar, e0, e1, e2, e3]

/-- The angle sum around the axis star is `2π`, and it stays `2π` under the stretch
`z ↦ 2 z + z̄`, which has `α = 2`, `β = 1`. -/
theorem axisStar_angle_sum :
    ∑ i, InnerProductGeometry.angle (lin 2 1 1 (axisStar i)) (lin 2 1 1 (axisStar (i + 1))) =
      2 * π := by
  rw [sum_angle_linear axisStar_isPosStar (by simp)]
  have e0 : (0 : ZMod 4) + 1 = 1 := by decide
  have e1 : (1 : ZMod 4) + 1 = 2 := by decide
  have e2 : (2 : ZMod 4) + 1 = 3 := by decide
  have e3 : (3 : ZMod 4) + 1 = 0 := by decide
  have hang : ∀ i : ZMod 4, InnerProductGeometry.angle (axisStar i) (axisStar (i + 1)) = π / 2 := by
    intro i
    rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> simp [axisStar, e0, e1, e2, e3, Complex.inner]
  rw [Finset.sum_congr rfl fun i _ => hang i]
  simp
  ring

end Lightlike.CMS
