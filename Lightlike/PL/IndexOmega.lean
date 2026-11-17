import Lightlike.PL.IndexTriangle

/-!
# The index of a loop through two arcs and a vertex

Triangles traversed clockwise have index `-1`; a loop that goes along an arc from `P` to `Q` below a point `q` inside the triangle `P Q Ω`, then along the sides `Q Ω` and `Ω P`, has index `±1` about `q`.

## Main results

* `loopIndex_omega1`: index `±1` about a point of the triangle

## References

* McCleary, *A First Course in Topology: Continuity and Dimension* (2006), `mccleary-2006`, Chapter 9: the chapter location is verified, the lemma-level numbering is not.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

lemma arg_mem_of_im_neg {u : ℂ} (h : u.im < 0) : -π < Complex.arg u ∧ Complex.arg u < 0 := by
  have h1 : Complex.arg u < 0 := Complex.arg_neg_iff.2 h
  have h2 : -π < Complex.arg u := Complex.neg_pi_lt_arg u
  exact ⟨h2, h1⟩

lemma im_div_neg {w₁ w₂ : ℂ} (h : (w₂ * (starRingEnd ℂ) w₁).im < 0) : (w₂ / w₁).im < 0 := by
  have hw₁ : w₁ ≠ 0 := by
    rintro rfl; simp at h
  have hn : 0 < Complex.normSq w₁ := Complex.normSq_pos.2 hw₁
  have : (w₂ / w₁).im = (w₂ * (starRingEnd ℂ) w₁).im / Complex.normSq w₁ := by
    rw [Complex.div_im]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [this]; exact div_neg_of_neg_of_pos h hn

/-- **The three angles of a clockwise triangle around a point add up to `-2π`.** -/
theorem triangle_log_sum_neg {w₁ w₂ w₃ : ℂ} (h₁ : (w₂ * (starRingEnd ℂ) w₁).im < 0)
    (h₂ : (w₃ * (starRingEnd ℂ) w₂).im < 0) (h₃ : (w₁ * (starRingEnd ℂ) w₃).im < 0) :
    Complex.log (w₂ / w₁) + Complex.log (w₃ / w₂) + Complex.log (w₁ / w₃) = -(2 * π * Complex.I) := by
  have hw₁ : w₁ ≠ 0 := by rintro rfl; simp at h₁
  have hw₂ : w₂ ≠ 0 := by rintro rfl; simp at h₂
  have hw₃ : w₃ ≠ 0 := by rintro rfl; simp at h₃
  obtain ⟨a1, a1'⟩ := arg_mem_of_im_neg (im_div_neg h₁)
  obtain ⟨a2, a2'⟩ := arg_mem_of_im_neg (im_div_neg h₂)
  obtain ⟨a3, a3'⟩ := arg_mem_of_im_neg (im_div_neg h₃)
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
  have hm1 : (m : ℝ) < 0 := by
    by_contra hcon; push Not at hcon
    nlinarith
  have hm2 : (-2 : ℝ) < m := by
    by_contra hcon; push Not at hcon
    nlinarith
  have hm' : m = -1 := by
    have : m < 0 := by exact_mod_cast hm1
    have : -2 < m := by exact_mod_cast hm2
    omega
  rw [hm, hm']
  push_cast
  ring

/-- The cross products of the three vectors from an interior point of a triangle to its corners are the signed area
times the barycentric coordinates. -/
lemma cross_algebra (p s : ℂ) (a b : ℝ) :
    ((-(a : ℂ) * p - (b : ℂ) * s) * (starRingEnd ℂ) (-(a : ℂ) * p + (1 - (b : ℂ)) * s)).im = a * (s * (starRingEnd ℂ) p).im ∧
    ((((1 : ℂ) - a) * p - (b : ℂ) * s) * (starRingEnd ℂ) (-(a : ℂ) * p - (b : ℂ) * s)).im = b * (s * (starRingEnd ℂ) p).im ∧
    ((-(a : ℂ) * p + (1 - (b : ℂ)) * s) * (starRingEnd ℂ) (((1 : ℂ) - a) * p - (b : ℂ) * s)).im =
      (1 - a - b) * (s * (starRingEnd ℂ) p).im := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Complex.mul_im, Complex.mul_re, map_sub, map_mul, map_neg, map_add, map_one, Complex.conj_ofReal,
      Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring

lemma im_segPath_lt {a b : ℂ} {c : ℝ} (ha : a.im < c) (hb : b.im < c) (t : I) : (segPath a b t).im < c := by
  simp only [segPath, Path.coe_mk_mk, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, zero_mul, add_zero]
  have h0 := t.2.1
  have h1 := t.2.2
  rcases le_total (t : ℝ) (1 / 2) with h | h
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 (le_of_lt hb)), mul_nonneg h0 (sub_nonneg.2 (le_of_lt ha))]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_of_lt hb)), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_of_lt ha))]

lemma im_mul_conj_swap (x y : ℂ) : (y * (starRingEnd ℂ) x).im = -(x * (starRingEnd ℂ) y).im := by
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **The index of `ω₁` about a point inside the triangle `PQΩ` and above the curve is `±1`.** The loop
`γ₁ * (QΩ * ΩP)` of the notes' last argument, with `γ₁` an arc from `P` to `Q` that stays below the point `q`: the
arc is closed up by the chord `QP`, which has index `0` since everything lies below `q`, and what is left is the
triangle `QΩP`. -/
theorem loopIndex_omega1 {P Q Ω q : ℂ} (γ₁ : Path P Q) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (hq : q = Ω + (a : ℂ) * (P - Ω) + (b : ℂ) * (Q - Ω))
    (hA : ((Q - Ω) * (starRingEnd ℂ) (P - Ω)).im ≠ 0)
    (hγ : ∀ t, (γ₁ t).im < q.im) (hP : P.im < q.im) (hQ : Q.im < q.im) :
    loopIndex (γ₁.trans ((segPath Q Ω).trans (segPath Ω P))) q = 1 ∨
      loopIndex (γ₁.trans ((segPath Q Ω).trans (segPath Ω P))) q = -1 := by
  set p : ℂ := P - Ω with hp
  set s : ℂ := Q - Ω with hs
  have hwΩ : Ω - q = -(a : ℂ) * p - (b : ℂ) * s := by rw [hq, hp, hs]; ring
  have hwP : P - q = ((1 : ℂ) - a) * p - (b : ℂ) * s := by rw [hq, hp, hs]; ring
  have hwQ : Q - q = -(a : ℂ) * p + (1 - (b : ℂ)) * s := by rw [hq, hp, hs]; ring
  obtain ⟨c1, c2, c3⟩ := cross_algebra p s a b
  rw [← hwΩ, ← hwQ] at c1
  rw [← hwP, ← hwΩ] at c2
  rw [← hwQ, ← hwP] at c3
  have hab' : 0 < 1 - a - b := by linarith
  -- the three ratios avoid the negative real axis
  have rΩQ : (Ω - q) / (Q - q) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    rcases lt_or_gt_of_ne hA with h | h
    · exact (im_div_neg (by rw [c1]; nlinarith)).ne
    · exact (im_div_pos (by rw [c1]; nlinarith)).ne'
  have rPΩ : (P - q) / (Ω - q) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    rcases lt_or_gt_of_ne hA with h | h
    · exact (im_div_neg (by rw [c2]; nlinarith)).ne
    · exact (im_div_pos (by rw [c2]; nlinarith)).ne'
  have rQP : (Q - q) / (P - q) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    rcases lt_or_gt_of_ne hA with h | h
    · exact (im_div_neg (by rw [c3]; nlinarith)).ne
    · exact (im_div_pos (by rw [c3]; nlinarith)).ne'
  have rPQ : (P - q) / (Q - q) ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    have h3 := c3
    rcases lt_or_gt_of_ne hA with h | h
    · exact (im_div_pos (by rw [im_mul_conj_swap, c3]; nlinarith)).ne'
    · exact (im_div_neg (by rw [im_mul_conj_swap, c3]; nlinarith)).ne
  have hQq : Q - q ≠ 0 := by
    rintro h; rw [h] at rQP; simp at rQP
  have hPq : P - q ≠ 0 := by
    rintro h; rw [h] at rPQ; simp at rPQ
  have hΩq : Ω - q ≠ 0 := by
    rintro h; rw [h] at rPΩ; simp at rPΩ
  have a₁ := avoid_segPath hQq rΩQ
  have a₂ := avoid_segPath hΩq rPΩ
  have a₃ := avoid_segPath hQq rPQ
  have hγq : ∀ t, γ₁ t ≠ q := fun t h => by have := hγ t; rw [h] at this; exact lt_irrefl _ this
  -- the closing chord
  have hloop3 : loopIndex (γ₁.trans (segPath Q P)) q = 0 := by
    refine loopIndex_eq_zero_of_below _ fun t => ?_
    rw [Path.trans_apply]
    split_ifs
    · exact hγ _
    · exact im_segPath_lt hQ hP _
  have hav3 : ∀ t, (γ₁.trans (segPath Q P)) t ≠ q := avoid_trans hγq a₃
  have h3 := loopIndex_spec _ hav3
  rw [hloop3] at h3
  rw [logInc_trans γ₁ _ hγq a₃, logInc_segPath hQq rPQ] at h3
  simp only [Int.cast_zero, zero_mul] at h3
  have hγlog : logInc γ₁ q = Complex.log ((Q - q) / (P - q)) := by
    have hneg : Complex.log ((P - q) / (Q - q)) = -Complex.log ((Q - q) / (P - q)) := by
      rw [← inv_div, Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.1 rQP).1]
    linear_combination h3 - hneg
  -- the loop `ω₁` and the triangle
  have hall : ∀ t, (γ₁.trans ((segPath Q Ω).trans (segPath Ω P))) t ≠ q :=
    avoid_trans hγq (avoid_trans a₁ a₂)
  have h1 := loopIndex_spec _ hall
  rw [logInc_trans γ₁ _ hγq (avoid_trans a₁ a₂), logInc_trans _ _ a₁ a₂, logInc_segPath hQq rΩQ,
    logInc_segPath hΩq rPΩ, hγlog] at h1
  have hne2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rcases lt_or_gt_of_ne hA with h | h
  · have hsum := triangle_log_sum_neg (w₁ := Q - q) (w₂ := Ω - q) (w₃ := P - q)
      (by rw [c1]; nlinarith) (by rw [c2]; nlinarith) (by rw [c3]; nlinarith)
    right
    have : ((loopIndex (γ₁.trans ((segPath Q Ω).trans (segPath Ω P))) q : ℤ) : ℂ) = -1 := by
      apply mul_right_cancel₀ hne2
      rw [← h1]
      linear_combination hsum
    exact_mod_cast this
  · have hsum := triangle_log_sum (w₁ := Q - q) (w₂ := Ω - q) (w₃ := P - q)
      (by rw [c1]; nlinarith) (by rw [c2]; nlinarith) (by rw [c3]; nlinarith)
    left
    have : ((loopIndex (γ₁.trans ((segPath Q Ω).trans (segPath Ω P))) q : ℤ) : ℂ) = 1 := by
      apply mul_right_cancel₀ hne2
      rw [← h1]
      linear_combination hsum
    exact_mod_cast this

end Lightlike.PL
