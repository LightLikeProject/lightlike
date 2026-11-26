import Lightlike.Asymptotics.KummerSum.Kernel
import Lightlike.Oscillatory.LaplaceRay

/-!
# Laplace's method across the saddle of Kummer's kernel

Along the horizontal line `α = α₀ + s`, `s ∈ [−½, ½]`, through the saddle `α₀ = (1 + i)/2` of
`ψ = kummerPhase`, with `φ(s) = ψ(α₀ + s) − ψ(α₀)`:

* **Laplace** (`norm_integral_kummerPhase_sub_le`): there is `C` with
  `‖∫_{−½}^{½} exp(N φ(s)) ds − (π/(2N))^{1/2}‖ ≤ C/N` for all `N > 0`. Both halves are
  `Lightlike.Oscillatory.laplace_ray_uniform` with `a = −ψ''(α₀) = 4`, using
  `‖φ(s) + 2s²‖ ≤ 16|s|³` and `Re φ(s) ≤ −s²/2` (`KummerSum/Phase.lean`).
* **The slowly varying factor** (`norm_kummerAmp_sub_one_le`): on the line `Im z = N/2`,
  `‖exp(−2(μ(w₁) + μ(w₂)))/(1 + exp(2πi w₁)) − 1‖ ≤ 26/N` for `N = m + 1 ≥ 6`, from the
  Stirling remainder bound `‖μ(w)‖ ≤ 3/(4‖w‖)` (`norm_stirMu_le`) with `‖w₁‖, ‖w₂‖ ≥ N/2`, and
  `‖exp(2πi w₁)‖ = e^{−πN}`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Real

namespace Lightlike.Asymptotics

/-- `φ(s) = ψ(α₀ + s) − ψ(α₀)`. -/
noncomputable def kummerPhi (s : ℝ) : ℂ := kummerPhase (kummerSaddle + s) - kummerPhase kummerSaddle

lemma hasDerivAt_kummerPhase_line (s : ℝ) :
    HasDerivAt (fun s : ℝ => kummerPhase (kummerSaddle + s)) (dkummerPhase (kummerSaddle + s)) s := by
  have h := im_kummerSaddle_add s
  have := (hasDerivAt_kummerPhase (mem_slitPlane_of_im_eq h)
    (one_sub_mem_slitPlane_of_im_eq h)).comp (s : ℂ) ((hasDerivAt_id' (s : ℂ)).const_add kummerSaddle)
  simpa using this.comp_ofReal

lemma continuous_kummerPhi : Continuous kummerPhi :=
  continuous_iff_continuousAt.2 fun s =>
    ((hasDerivAt_kummerPhase_line s).continuousAt).sub continuousAt_const

lemma norm_kummerPhi_add_le (s : ℝ) :
    ‖kummerPhi s + 4 * s ^ 2 / 2‖ ≤ 16 * |s| ^ 3 := by
  have := norm_kummerPhase_taylor_le (im_kummerSaddle_add s)
  simp only [add_sub_cancel_left, norm_real, Real.norm_eq_abs] at this
  rw [kummerPhi]
  convert this using 2
  ring

lemma re_kummerPhi_le {s : ℝ} (hs : |s| ≤ 1 / 2) : (kummerPhi s).re ≤ -(1 / 2) * s ^ 2 := by
  have := re_kummerPhase_sub_le hs
  rw [kummerPhi]; linarith

/-- **Laplace's method across the saddle.** -/
theorem norm_integral_kummerPhase_sub_le :
    ∃ C : ℝ, ∀ N : ℝ, 0 < N →
      ‖(∫ s in (-(1 / 2) : ℝ)..(1 / 2), cexp (N * kummerPhi s)) -
        ((π : ℂ) / (N * 4 / 2)) ^ (1 / 2 : ℂ)‖ ≤ C / N := by
  obtain ⟨C, hC⟩ := Lightlike.Oscillatory.laplace_ray_uniform (1 / 2) 4 16 (1 / 2) 0 1
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨2 * C, fun N hN => ?_⟩
  have hcont : ∀ ε : ℝ, ContinuousOn (fun t : ℝ => kummerPhi (ε * t)) (Icc 0 (1 / 2)) :=
    fun ε => (continuous_kummerPhi.comp (continuous_const.mul continuous_id)).continuousOn
  have hside : ∀ ε : ℝ, ε ^ 2 = 1 →
      ‖(∫ t in (0 : ℝ)..(1 / 2), (fun _ : ℝ => (1 : ℂ)) t * cexp (N * kummerPhi (ε * t))) -
        (fun _ : ℝ => (1 : ℂ)) 0 * (((π : ℂ) / (N * 4 / 2)) ^ (1 / 2 : ℂ) / 2)‖ ≤ C / N := by
    intro ε hε
    have hεa : |ε| = 1 := by
      have := sq_abs ε; rw [hε] at this
      nlinarith [abs_nonneg ε, sq_nonneg (|ε| - 1)]
    have habs : ∀ t ∈ Icc (0 : ℝ) (1 / 2), |ε * t| = t := fun t ht => by
      rw [abs_mul, hεa, one_mul, abs_of_nonneg ht.1]
    refine hC (4 : ℂ) (fun t => kummerPhi (ε * t)) (fun _ => 1) (by norm_num) (hcont ε)
      continuousOn_const (fun t ht => ?_) (fun t ht => ?_) (fun t _ => by simp) (by simp) N hN
    · have h := norm_kummerPhi_add_le (ε * t)
      rw [habs t ht] at h
      convert h using 3
      push_cast
      rw [mul_pow, show (ε : ℂ) ^ 2 = 1 by exact_mod_cast hε, one_mul]
    · have h := re_kummerPhi_le (s := ε * t) (by rw [habs t ht]; exact ht.2)
      rw [mul_pow, hε, one_mul] at h
      linarith
  have h1 := hside 1 (by norm_num)
  have h2 := hside (-1) (by norm_num)
  simp only [one_mul, neg_mul] at h1 h2
  have hint : Continuous fun s : ℝ => cexp (N * kummerPhi s) :=
    (continuous_const.mul continuous_kummerPhi).cexp
  have hsplit : (∫ s in (-(1 / 2) : ℝ)..(1 / 2), cexp (N * kummerPhi s)) =
      (∫ t in (0 : ℝ)..(1 / 2), cexp (N * kummerPhi t)) +
        ∫ t in (0 : ℝ)..(1 / 2), cexp (N * kummerPhi (-t)) := by
    rw [← integral_add_adjacent_intervals (b := 0) (hint.intervalIntegrable _ _)
      (hint.intervalIntegrable _ _), intervalIntegral.integral_comp_neg
        (fun t => cexp (N * kummerPhi t))]
    simp only [neg_zero]
    ring
  rw [hsplit]
  calc _ = ‖((∫ t in (0 : ℝ)..(1 / 2), cexp (N * kummerPhi t)) -
          ((π : ℂ) / (N * 4 / 2)) ^ (1 / 2 : ℂ) / 2) +
        ((∫ t in (0 : ℝ)..(1 / 2), cexp (N * kummerPhi (-t))) -
          ((π : ℂ) / (N * 4 / 2)) ^ (1 / 2 : ℂ) / 2)‖ := by ring_nf
    _ ≤ C / N + C / N := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * C / N := by ring

/-! ## The slowly varying factor on the line through the saddle -/

/-- A Stirling remainder bound on the line `Im w = ±N/2`, `Re w ≥ 0`, for `N ≥ 6`. -/
lemma norm_stirMu_le_line {w : ℂ} {N : ℝ} (hN : 6 ≤ N) (hre : 0 ≤ w.re) (him : |w.im| = N / 2) :
    ‖stirMu w‖ ≤ 3 / (2 * N) := by
  have hw : N / 2 ≤ ‖w‖ := by rw [← him]; exact abs_im_le_norm w
  have hN0 : 0 < N := by linarith
  have h := (norm_stirMu_le (c := 0) le_rfl (by norm_num) (by simpa using hre)
    (by norm_num; nlinarith)).2
  calc ‖stirMu w‖ ≤ 3 / 4 / ((1 - 0) * ‖w‖) := h
    _ ≤ 3 / 4 / ((1 - 0) * (N / 2)) := by gcongr
    _ = 3 / (2 * N) := by field_simp; ring

/-- The point of the horizontal line through the saddle: `z(s) = N (α₀ + s) − ½`. -/
noncomputable def kummerLinePt (N s : ℝ) : ℂ := N * (kummerSaddle + s) - 1 / 2

lemma kummerLinePt_im (N s : ℝ) : (kummerLinePt N s).im = N / 2 := by
  simp [kummerLinePt, kummerSaddle]; ring

lemma kummerLinePt_re (N s : ℝ) : (kummerLinePt N s).re = N * (1 / 2 + s) - 1 / 2 := by
  simp [kummerLinePt, kummerSaddle]

/-- **The slowly varying factor is `1 + O(1/N)`** on the line through the saddle. -/
theorem norm_kummerAmp_sub_one_le {m : ℕ} (hm : 5 ≤ m) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    ‖kummerAmp m (kummerLinePt (m + 1) s) - 1‖ ≤ 26 / (m + 1) := by
  set N : ℝ := m + 1 with hN
  have hN6 : 6 ≤ N := by
    have : (5 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hN]; linarith
  have hN0 : 0 < N := by linarith
  have hs' := abs_le.1 hs
  set z := kummerLinePt N s
  set w₁ := z + 1 / 2 with hw₁
  set w₂ := (m : ℂ) - z + 1 / 2 with hw₂
  have hw1re : 0 ≤ w₁.re := by
    simp only [hw₁, add_re, kummerLinePt_re, z]; norm_num; nlinarith
  have hw1im : |w₁.im| = N / 2 := by
    simp only [hw₁, add_im, kummerLinePt_im, z]; norm_num; linarith
  have hw2re : 0 ≤ w₂.re := by
    simp only [hw₂, add_re, sub_re, natCast_re, kummerLinePt_re, z]; norm_num
    rw [hN]; nlinarith
  have hw2im : |w₂.im| = N / 2 := by
    simp only [hw₂, add_im, sub_im, natCast_im, kummerLinePt_im, z]; norm_num
    linarith
  have hμ1 := norm_stirMu_le_line hN6 hw1re hw1im
  have hμ2 := norm_stirMu_le_line hN6 hw2re hw2im
  set u := -2 * (stirMu w₁ + stirMu w₂) with hu
  have hu1 : ‖u‖ ≤ 6 / N := by
    rw [hu, norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num]
    calc 2 * ‖stirMu w₁ + stirMu w₂‖ ≤ 2 * (‖stirMu w₁‖ + ‖stirMu w₂‖) := by
          gcongr; exact norm_add_le _ _
      _ ≤ 2 * (3 / (2 * N) + 3 / (2 * N)) := by gcongr
      _ = 6 / N := by field_simp; ring
  have hu2 : ‖u‖ ≤ 1 := hu1.trans (by rw [div_le_one hN0]; linarith)
  set v := cexp (2 * π * I * w₁) with hv
  have hv1 : ‖v‖ = Real.exp (-(π * N)) := by
    rw [hv, norm_exp]; congr 1
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    have : w₁.im = N / 2 := by simp only [hw₁, add_im, kummerLinePt_im, z]; norm_num
    rw [this]; ring
  have hvN : ‖v‖ ≤ 1 / N := by
    rw [hv1, Real.exp_neg, le_div_iff₀ hN0, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    have := Real.add_one_le_exp (π * N)
    nlinarith [Real.pi_gt_three]
  have hvh : ‖v‖ ≤ 1 / 2 := hvN.trans (by rw [div_le_div_iff₀ hN0 (by norm_num)]; linarith)
  have hden : 1 / 2 ≤ ‖1 + v‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-v)
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  have hden0 : (1 + v) ≠ 0 := by intro h; rw [h, norm_zero] at hden; norm_num at hden
  have e : kummerAmp m z - 1 = ((cexp u - 1) - v) / (1 + v) := by
    rw [kummerAmp, ← hw₁, ← hw₂, ← hu, ← hv]
    field_simp
    ring
  rw [e, norm_div, div_le_iff₀ (by linarith)]
  calc ‖cexp u - 1 - v‖ ≤ ‖cexp u - 1‖ + ‖v‖ := norm_sub_le _ _
    _ ≤ 2 * ‖u‖ + 1 / N := add_le_add (norm_exp_sub_one_le hu2) hvN
    _ ≤ 2 * (6 / N) + 1 / N := by gcongr
    _ = 26 / N * (1 / 2) := by ring
    _ ≤ 26 / N * ‖1 + v‖ := by gcongr

end Lightlike.Asymptotics
