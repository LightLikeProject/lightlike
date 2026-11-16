import Lightlike.PL.IndexTheta

/-!
# The index of a straight segment and of a triangle

The increment of the logarithm along a straight segment from `a` to `b`, about a point `q` such that the ratio
`(b - q) / (a - q)` avoids the negative real axis, is the principal logarithm of that ratio (`logInc_segPath`). Three
points seen counterclockwise from `q` have angles that add up to `2π` (`triangle_log_sum`), so a triangle has index `1`
about an interior point (`loopIndex_triangle`). The index of a loop is zero about a point strictly above or below it
(`loopIndex_eq_zero_of_above`, `loopIndex_eq_zero_of_below`) and about a point outside a disc containing it
(`loopIndex_eq_zero_of_far`); these are Lemma 9.12 of the notes in the forms used in the last argument.

This is the computation, left to a picture in the notes, that a triangle `ΔABC` and an interior point `Ω` have
`ind_Ω(ΔABC) = ±1` (the example before Lemma 9.12 in chapter 9 of J. McCleary, *A First Course in Topology:
Continuity and Dimension* (AMS, 2006); the numbering is that of the lecture-notes version of the chapter
(`https://pages.vassar.edu/mccleary/files/2011/04/FinalChapter9.pdf`), not checked against the printed book). The
notes read it off the fundamental group of the circle; here it is computed from the angles of the triangle. The
statements and proofs are Lean's own.

## Main results

* `logInc_segPath`: the increment of the logarithm along a straight segment.
* `triangle_log_sum`, `loopIndex_triangle`: a triangle has index `1` about an interior point.
* `loopIndex_eq_zero_of_above`, `loopIndex_eq_zero_of_below`, `loopIndex_eq_zero_of_far`: loops with a point outside.

## References

* `mccleary-2006`: chapter "The Jordan Curve Theorem" (the chapter location is verified with
  `scripts/sources.py verify`; the lemma-level numbering quoted above is that of the lecture-notes version and is
  not checked).
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

lemma mem_slitPlane_segment_ratio {r : ℂ} (hr : r ∈ Complex.slitPlane) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t : ℂ) + t * r ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hr ⊢
  rcases hr with hre | him
  · rcases ht with ⟨h0, h1⟩
    left
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases h1.eq_or_lt with h | h
    · subst h; simpa using hre
    · nlinarith [mul_nonneg h0 hre.le]
  · rcases ht with ⟨h0, h1⟩
    rcases h0.eq_or_lt with h | h
    · left
      subst h
      simp
    · right
      simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, zero_mul, add_zero, zero_sub, neg_zero]
      intro hh
      apply him
      have : t * r.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h.ne'

/-- A straight segment whose ratio avoids the negative real axis does not pass through `q`. -/
lemma avoid_segPath {a b q : ℂ} (ha : a - q ≠ 0) (hr : (b - q) / (a - q) ∈ Complex.slitPlane) :
    ∀ t, segPath a b t ≠ q := by
  intro t h
  have hmem : (segPath a b t - q) / (a - q) = (1 - ((t : ℝ) : ℂ)) + ((t : ℝ) : ℂ) * ((b - q) / (a - q)) := by
    simp only [segPath, Path.coe_mk_mk]
    field_simp
    ring
  have := mem_slitPlane_segment_ratio hr _ t.2
  rw [← hmem, h, sub_self, zero_div] at this
  simp at this

/-- **The increment of the logarithm along a straight segment** about `q` is the principal logarithm of the ratio
`(b - q) / (a - q)`, when this ratio avoids the negative real axis. -/
theorem logInc_segPath {a b q : ℂ} (ha : a - q ≠ 0) (hr : (b - q) / (a - q) ∈ Complex.slitPlane) :
    logInc (segPath a b) q = Complex.log ((b - q) / (a - q)) := by
  have hmem : ∀ t : I, (segPath a b t - q) / (a - q) = (1 - ((t : ℝ) : ℂ)) + ((t : ℝ) : ℂ) * ((b - q) / (a - q)) := by
    intro t
    simp only [segPath, Path.coe_mk_mk]
    field_simp
    ring
  have hslit : ∀ t : I, (segPath a b t - q) / (a - q) ∈ Complex.slitPlane := fun t => by
    rw [hmem]; exact mem_slitPlane_segment_ratio hr _ t.2
  have hav : ∀ t, segPath a b t ≠ q := avoid_segPath ha hr
  let ℓ : C(I, ℂ) := ⟨fun t => Complex.log (a - q) + Complex.log ((segPath a b t - q) / (a - q)), by
    refine continuous_const.add (continuous_iff_continuousAt.2 fun t => ?_)
    exact (((segPath a b).continuous.sub continuous_const).div_const (a - q)).continuousAt.clog (hslit t)⟩
  have hlog : IsLog ((segPath a b : Path a b) : C(I, ℂ)) q ℓ := by
    intro t
    show exp (Complex.log (a - q) + Complex.log ((segPath a b t - q) / (a - q))) = segPath a b t - q
    have hne : (segPath a b t - q) / (a - q) ≠ 0 := Complex.slitPlane_ne_zero (hslit t)
    rw [Complex.exp_add, Complex.exp_log ha, Complex.exp_log hne]
    field_simp
  rw [logInc_eq _ hav hlog]
  show (Complex.log (a - q) + Complex.log ((segPath a b 1 - q) / (a - q))) -
    (Complex.log (a - q) + Complex.log ((segPath a b 0 - q) / (a - q))) = _
  rw [(segPath a b).target, (segPath a b).source]
  simp [div_self ha]

lemma im_div_pos {w₁ w₂ : ℂ} (h : 0 < (w₂ * (starRingEnd ℂ) w₁).im) : 0 < (w₂ / w₁).im := by
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl; simp at h
  have hn : 0 < Complex.normSq w₁ := Complex.normSq_pos.2 hw₁
  have : (w₂ / w₁).im = (w₂ * (starRingEnd ℂ) w₁).im / Complex.normSq w₁ := by
    rw [Complex.div_im]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [this]; exact div_pos h hn

lemma arg_mem_of_im_pos {u : ℂ} (h : 0 < u.im) : 0 < Complex.arg u ∧ Complex.arg u < π := by
  have h1 : 0 ≤ Complex.arg u := Complex.arg_nonneg_iff.2 h.le
  have h2 : Complex.arg u ≤ π := Complex.arg_le_pi u
  refine ⟨lt_of_le_of_ne h1 (fun h0 => ?_), lt_of_le_of_ne h2 (fun hp => ?_)⟩
  · have := Complex.arg_eq_zero_iff.1 h0.symm
    linarith [this.2]
  · have := Complex.arg_eq_pi_iff.1 hp
    linarith [this.2]

/-- **The three angles of a triangle around a point add up to `2π`**: for three points `w₁, w₂, w₃` seen counterclockwise
from the origin, the logarithms of the successive ratios add up to `2πi`. -/
theorem triangle_log_sum {w₁ w₂ w₃ : ℂ} (h₁ : 0 < (w₂ * (starRingEnd ℂ) w₁).im)
    (h₂ : 0 < (w₃ * (starRingEnd ℂ) w₂).im) (h₃ : 0 < (w₁ * (starRingEnd ℂ) w₃).im) :
    Complex.log (w₂ / w₁) + Complex.log (w₃ / w₂) + Complex.log (w₁ / w₃) = 2 * π * Complex.I := by
  have hw₁ : w₁ ≠ 0 := by rintro rfl; simp at h₁
  have hw₂ : w₂ ≠ 0 := by rintro rfl; simp at h₂
  have hw₃ : w₃ ≠ 0 := by rintro rfl; simp at h₃
  have i₁ := im_div_pos h₁
  have i₂ := im_div_pos h₂
  have i₃ := im_div_pos h₃
  obtain ⟨a1, a1'⟩ := arg_mem_of_im_pos i₁
  obtain ⟨a2, a2'⟩ := arg_mem_of_im_pos i₂
  obtain ⟨a3, a3'⟩ := arg_mem_of_im_pos i₃
  have hprod : (w₂ / w₁) * (w₃ / w₂) * (w₁ / w₃) = 1 := by field_simp
  have hexp : exp (Complex.log (w₂ / w₁) + Complex.log (w₃ / w₂) + Complex.log (w₁ / w₃)) = 1 := by
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_log (div_ne_zero hw₂ hw₁),
      Complex.exp_log (div_ne_zero hw₃ hw₂), Complex.exp_log (div_ne_zero hw₁ hw₃)]
    exact hprod
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hexp
  have hme : (m : ℂ) * (2 * π * Complex.I) = ((2 * π * m : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hme] at hm
  have him := congrArg Complex.im hm
  simp only [Complex.add_im, Complex.log_im, Complex.mul_I_im, Complex.ofReal_re] at him
  have hπ := Real.pi_pos
  have hm1 : (0 : ℝ) < m := by
    by_contra hcon; push Not at hcon
    nlinarith
  have hm2 : (m : ℝ) < 2 := by
    by_contra hcon; push Not at hcon
    nlinarith
  have hm' : m = 1 := by
    have : 0 < m := by exact_mod_cast hm1
    have : m < 2 := by exact_mod_cast hm2
    omega
  rw [hm, hm']
  simp

/-- The triangle with corners `z₁, z₂, z₃`, as a loop based at `z₁`. -/
noncomputable def triangleLoop (z₁ z₂ z₃ : ℂ) : Path z₁ z₁ :=
  (segPath z₁ z₂).trans ((segPath z₂ z₃).trans (segPath z₃ z₁))

/-- **A triangle has index `1` about an interior point** (a point seen counterclockwise from the corners). -/
theorem loopIndex_triangle {z₁ z₂ z₃ q : ℂ} (h₁ : 0 < ((z₂ - q) * (starRingEnd ℂ) (z₁ - q)).im)
    (h₂ : 0 < ((z₃ - q) * (starRingEnd ℂ) (z₂ - q)).im) (h₃ : 0 < ((z₁ - q) * (starRingEnd ℂ) (z₃ - q)).im) :
    loopIndex (triangleLoop z₁ z₂ z₃) q = 1 := by
  have hz₁ : z₁ - q ≠ 0 := by rintro h; rw [h] at h₁; simp at h₁
  have hz₂ : z₂ - q ≠ 0 := by rintro h; rw [h] at h₂; simp at h₂
  have hz₃ : z₃ - q ≠ 0 := by rintro h; rw [h] at h₃; simp at h₃
  have r₁ : (z₂ - q) / (z₁ - q) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (im_div_pos h₁).ne')
  have r₂ : (z₃ - q) / (z₂ - q) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (im_div_pos h₂).ne')
  have r₃ : (z₁ - q) / (z₃ - q) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (im_div_pos h₃).ne')
  have a₁ := avoid_segPath hz₁ r₁
  have a₂ := avoid_segPath hz₂ r₂
  have a₃ := avoid_segPath hz₃ r₃
  have hall : ∀ t, triangleLoop z₁ z₂ z₃ t ≠ q := avoid_trans a₁ (avoid_trans a₂ a₃)
  have h := loopIndex_spec (triangleLoop z₁ z₂ z₃) hall
  have hlog : logInc (triangleLoop z₁ z₂ z₃) q = 2 * π * Complex.I := by
    show logInc ((segPath z₁ z₂).trans ((segPath z₂ z₃).trans (segPath z₃ z₁))) q = _
    rw [logInc_trans _ _ a₁ (avoid_trans a₂ a₃), logInc_trans _ _ a₂ a₃,
      logInc_segPath hz₁ r₁, logInc_segPath hz₂ r₂, logInc_segPath hz₃ r₃, ← add_assoc,
      triangle_log_sum h₁ h₂ h₃]
  rw [hlog] at h
  have hne2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h' : ((loopIndex (triangleLoop z₁ z₂ z₃) q : ℤ) : ℂ) = 1 := by
    apply mul_right_cancel₀ hne2
    rw [← h, one_mul]
  exact_mod_cast h'

/-- **A loop strictly below a point has index zero about it** (Lemma 9.12 with the half plane below the point). -/
theorem loopIndex_eq_zero_of_below {a : ℂ} (α : Path a a) {Ω : ℂ} (h : ∀ t, (α t).im < Ω.im) :
    loopIndex α Ω = 0 := by
  refine loopIndex_eq_zero_of_halfplane α (u := -Complex.I) fun t => ?_
  have := h t
  simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, zero_mul, one_mul, zero_sub]
  linarith

/-- **A loop strictly above a point has index zero about it.** -/
theorem loopIndex_eq_zero_of_above {a : ℂ} (α : Path a a) {Ω : ℂ} (h : ∀ t, Ω.im < (α t).im) :
    loopIndex α Ω = 0 := by
  refine loopIndex_eq_zero_of_halfplane α (u := Complex.I) fun t => ?_
  have := h t
  simp only [Complex.conj_I, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im,
    Complex.sub_re, Complex.sub_im, zero_mul, zero_sub, neg_mul, one_mul, neg_neg]
  linarith

/-- **A loop in a disc has index zero about every point outside the disc** (a point far from the loop). -/
theorem loopIndex_eq_zero_of_far {a : ℂ} (α : Path a a) {Ω : ℂ} {ρ : ℝ} (hα : ∀ t, ‖α t‖ ≤ ρ) (hΩ : ρ < ‖Ω‖) :
    loopIndex α Ω = 0 := by
  refine loopIndex_eq_zero_of_halfplane α (u := -Ω) fun t => ?_
  have hΩ0 : 0 < ‖Ω‖ := lt_of_le_of_lt ((norm_nonneg _).trans (hα 0)) hΩ
  have h1 : ((starRingEnd ℂ) Ω * α t).re ≤ ‖Ω‖ * ρ := by
    calc ((starRingEnd ℂ) Ω * α t).re ≤ ‖(starRingEnd ℂ) Ω * α t‖ := Complex.re_le_norm _
      _ = ‖Ω‖ * ‖α t‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖Ω‖ * ρ := by gcongr; exact hα t
  have h2 : ((starRingEnd ℂ) Ω * Ω).re = ‖Ω‖ ^ 2 := by
    rw [Complex.conj_mul']; simp [sq]
  have : ((starRingEnd ℂ) (-Ω) * (α t - Ω)).re = ‖Ω‖ ^ 2 - ((starRingEnd ℂ) Ω * α t).re := by
    rw [map_neg, neg_mul, mul_sub, Complex.neg_re, Complex.sub_re, h2]; ring
  rw [this]
  nlinarith

end Lightlike.PL
