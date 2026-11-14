import Lightlike.Asymptotics.Valley
import Lightlike.Asymptotics.ContourTests

/-!
# Trust checks for the valleys at the saddle

* **Known value.** For the regular unit tetrahedron, with saddle `s = 11/3 + i√2/6`,
  `ψ''(s) = −896/81 − (136√2/81) i` (`d2phaseC_saddle_regular`), computed term by term from
  `1/s = 22/81 − (√2/81) i`, `1/(s − 3) = 4/3 − (√2/3) i` and `1/(s − 4) = −2 − √2 i`, without
  the volume formula of `Saddle.lean`. Its norm is `8√2` (`norm_d2phaseC_saddle_regular`), which
  agrees with `IsEuclid.d2phase_saddle`: `‖ψ''(s)‖ ‖s − 3‖⁴ = 24 √(1/72)` with `‖s − 3‖² = 1/2`.
* **Wrong input fails.** In a direction `u` with `b u² = +‖b‖` instead of `−‖b‖`, `Re ψ` rises
  above the saddle level (`exists_re_phaseC_gt`). For the regular tetrahedron this happens in
  the direction `i u₀`, at right angles to the valleys (`exists_ascent_regular`): the saddle is
  a saddle, and the sign condition of `exists_valley` is what selects the descending rays.
* **Non-vacuity.** The hypotheses of `exists_valley` hold for the regular tetrahedron, with
  `‖b‖ = 4√2`, and in each valley every level near `Im ψ s` is taken at a point strictly below
  the saddle level (`exists_valley_regular`).
* **Junk values.** `d2phaseC` contains `1/z` and `1/(z − c)` for real `c`, which are Lean's `0`
  on the real axis; every statement of `Valley.lean` assumes or proves `Im > 0` at the points
  where `d2phaseC` is used, so none relies on that junk value.
-/

open Complex Set
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: `ψ''(s) = −896/81 − (136√2/81) i` at the saddle of the regular unit
tetrahedron, computed directly from `ψ''(s) = 1/s − 4/(s − 3) + 3/(s − 4)`. -/
theorem d2phaseC_saddle_regular :
    d2phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1)) =
      ⟨-896 / 81, -(136 * √2 / 81)⟩ := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e0 : 1 / (⟨11 / 3, √2 / 6⟩ : ℂ) = ⟨22 / 81, -(√2 / 81)⟩ := by
    rw [one_div]; apply inv_eq_of_mul_eq_one_left
    apply Complex.ext <;> simp only [mul_re, mul_im, one_re, one_im]
    · linear_combination h2 / 486
    · ring
  have e3 : 1 / ((⟨11 / 3, √2 / 6⟩ : ℂ) - ((3 : ℝ) : ℂ)) = ⟨4 / 3, -(√2 / 3)⟩ := by
    rw [one_div]; apply inv_eq_of_mul_eq_one_left
    apply Complex.ext <;> simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, one_re,
      one_im]
    · linear_combination h2 / 18
    · ring
  have e4 : 1 / ((⟨11 / 3, √2 / 6⟩ : ℂ) - ((4 : ℝ) : ℂ)) = ⟨-2, -√2⟩ := by
    rw [one_div]; apply inv_eq_of_mul_eq_one_left
    apply Complex.ext <;> simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, one_re,
      one_im]
    · linear_combination h2 / 6
    · ring
  rw [faceSum_regular, quadSum_regular, saddle_regular]
  simp only [d2phaseC, Fin.sum_univ_four, Fin.sum_univ_three, e0, e3, e4]
  apply Complex.ext <;> simp only [add_re, sub_re, add_im, sub_im] <;> ring

/-- **Known value**: `‖ψ''(s)‖ = 8√2` for the regular unit tetrahedron. -/
theorem norm_d2phaseC_saddle_regular :
    ‖d2phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))‖ = 8 * √2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [d2phaseC_saddle_regular, norm_eq_sqrt_sq_add_sq,
    Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  show 8 * √2 * (8 * √2) = (-896 / 81 : ℝ) ^ 2 + (-(136 * √2 / 81)) ^ 2
  linear_combination (64 - 136 ^ 2 / 81 ^ 2) * h2

/-- **Wrong input**: in a direction `u` with `b u² = +‖b‖` (instead of the valley condition
`b u² = −‖b‖`), `Re ψ` rises above its value at the nondegenerate critical point `s`. -/
theorem exists_re_phaseC_gt (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {s : ℂ} (hs : 0 < s.im)
    (hd : dphaseC A B s = 0) {b : ℂ} (hb : d2phaseC A B s = 2 * b) (hb0 : b ≠ 0) {u : ℂ}
    (hu : ‖u‖ = 1) (hbu : b * u ^ 2 = ‖b‖) :
    ∃ t : ℝ, 0 < t ∧ (phaseC A B s).re < (phaseC A B (s + t * u)).re := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = 32 / s.im ^ 2 := ⟨_, rfl⟩
  have hK : 0 < K₀ := by rw [hK₀]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min (s.im / 2) (‖b‖ / (2 * K₀)) := ⟨_, rfl⟩
  have ht0 : 0 < t := ht ▸ lt_min (by linarith) (by positivity)
  have ht1 : t ≤ s.im / 2 := ht ▸ min_le_left _ _
  have ht2 : t ≤ ‖b‖ / (2 * K₀) := ht ▸ min_le_right _ _
  have hn : ‖(t : ℂ) * u‖ = t := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ht0, hu, mul_one]
  have hzs : s + t * u - s = t * u := by ring
  have hT := norm_phaseC_taylor_le A B hs
    (show ‖s + t * u - s‖ ≤ s.im / 2 by rw [hzs, hn]; exact ht1)
  rw [hd, zero_mul, sub_zero, hb, hzs, hn, ← hK₀,
    show 2 * b / 2 * ((t : ℂ) * u) ^ 2 = ((‖b‖ * t ^ 2 : ℝ) : ℂ) by
      rw [show 2 * b / 2 * ((t : ℂ) * u) ^ 2 = (b * u ^ 2) * t ^ 2 by ring, hbu]; push_cast; ring]
    at hT
  have hre := abs_re_le_norm (phaseC A B (s + t * u) - phaseC A B s - ((‖b‖ * t ^ 2 : ℝ) : ℂ))
  rw [sub_re, sub_re, ofReal_re] at hre
  have h1 : K₀ * t ≤ ‖b‖ / 2 := by
    rw [le_div_iff₀ (by positivity)] at ht2; linarith
  have h3 : K₀ * t ^ 3 ≤ ‖b‖ / 2 * t ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg t)
    nlinarith
  have h4 := (abs_le.1 (hre.trans hT)).1
  refine ⟨t, ht0, ?_⟩
  nlinarith [pow_pos ht0 2]

/-- **Wrong input** for the regular tetrahedron: at right angles to the valleys, in the
direction `i u₀`, `Re ψ` rises above the saddle level. -/
theorem exists_ascent_regular : ∃ (b u₀ : ℂ), b * u₀ ^ 2 = -‖b‖ ∧ ‖u₀‖ = 1 ∧
    d2phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1)) = 2 * b ∧
    ∃ t : ℝ, 0 < t ∧
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re <
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
          (saddle (fun _ => 1) + t * (I * u₀))).re := by
  obtain ⟨b, u₀, K, r, hb, hb0, hu, hbu, -⟩ := isEuclid_regular.exists_valley
  refine ⟨b, u₀, hbu, hu, hb, ?_⟩
  refine exists_re_phaseC_gt _ _ isEuclid_regular.saddle_im_pos isEuclid_regular.dphaseC_saddle
    hb hb0 (by rw [norm_mul, norm_I, one_mul, hu]) ?_
  rw [mul_pow, I_sq, show b * (-1 * u₀ ^ 2) = -(b * u₀ ^ 2) by ring, hbu, neg_neg]

/-- **Non-vacuity**: the valley data exist for the regular unit tetrahedron, with `‖b‖ = 4√2`,
and in each valley every level `Im ψ s + η` with `|η| ≤ ‖b‖ r²/2` is taken at the end point of a
valley ray strictly below the saddle level. -/
theorem exists_valley_regular : ∃ (b u₀ : ℂ) (r : ℝ), ‖b‖ = 4 * √2 ∧ 0 < r ∧
    b * u₀ ^ 2 = -‖b‖ ∧ ∀ ε : ℝ, ε ^ 2 = 1 → ∀ η : ℝ, |η| ≤ ‖b‖ * r ^ 2 / 2 →
      ∃ τ : ℝ, |τ| ≤ 1 / 2 ∧
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
          (saddle (fun _ => 1) + r * valleyDir u₀ ε τ)).im =
          (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im + η ∧
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
          (saddle (fun _ => 1) + r * valleyDir u₀ ε τ)).re <
          (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re := by
  obtain ⟨b, u₀, K, r, hb, hb0, hu, hbu, hr, -, h1, h2⟩ := isEuclid_regular.exists_valley
  have hnb : ‖b‖ = 4 * √2 := by
    have := norm_d2phaseC_saddle_regular
    rw [hb, norm_mul, Complex.norm_two] at this
    linarith
  refine ⟨b, u₀, r, hnb, hr, hbu, fun ε hε η hη => ?_⟩
  obtain ⟨τ, hτ, him⟩ := h2 ε hε η hη
  refine ⟨τ, hτ, him, ?_⟩
  have hre := (h1 ε hε τ hτ r ⟨hr.le, le_rfl⟩).2.2
  have : 0 < ‖b‖ / 4 * r ^ 2 := by positivity
  linarith

end Lightlike.Asymptotics
