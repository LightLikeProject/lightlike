import Lightlike.Asymptotics.Stirling

/-!
# Uniform bounds for `1/Γ` and `Γ` from Stirling's formula

With the Stirling exponent `f(w) = w log w − w` (`stirF`, principal logarithm),

* `‖1/Γ(w + ½)‖ ≤ exp(3/(4‖w‖) − Re f(w))` for **every** `w ∈ ℂ` with `‖w‖² ≥ 2`
  (`norm_inv_Gamma_half_add_le`), and `‖1/Γ(w + ½)‖ ≤ C exp(−Re f(w))` for all `w ∈ ℂ`, with an
  absolute constant `C` (`exists_norm_inv_Gamma_half_add_le`);
* `‖Γ(w + ½)‖ ≤ √(2π) exp(3/(4‖w‖) + Re f(w))` for `Re w ≥ 0` and `‖w‖² ≥ 2`
  (`norm_Gamma_half_add_le`), and `‖Γ(w + ½)‖ ≤ C exp(Re f(w))` for all `w` with `Re w ≥ 0`
  (`exists_norm_Gamma_half_add_le`).

These are the bounds that dominate Racah's kernel `π T(z) / sin(π z)` along the steepest-descent
contour, whose factors are `Γ(σ + ½)` and `1/Γ(· + ½)` at arguments that leave every sector.

On the right half-plane the bounds are Stirling's formula `Gamma_half_add` with the remainder bound
`norm_stirMu_le` (sector constant `c = 0`). On the left half-plane, the reflection formula
`Γ(w + ½) Γ(½ − w) = π / cos(π w)` turns `1/Γ(w + ½)` into `Γ(½ − w) cos(π w) / π`, with `−w` in
the right half-plane. Two elementary facts then close the estimate:
`Re f(−w) = −Re f(w) − π |Im w|` (`re_stirF_neg`, the two logarithms differ by `±iπ`) and
`‖cos z‖ ≤ exp |Im z|` (`norm_cos_le_exp_abs_im`), so the growth `exp(π |Im w|)` of the cosine is
cancelled exactly. For `‖w‖² < 2`, `1/Γ` and `Γ` are bounded on a compact set and
`|Re f(w)| ≤ 4 + 2π` (`abs_re_stirF_le`).
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-! ## Elementary facts -/

/-- `x |log x| ≤ 2` on `[0, 2]`. -/
lemma mul_abs_log_le_two {x : ℝ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : x * |Real.log x| ≤ 2 := by
  rcases h0.eq_or_lt with rfl | hx
  · simp
  rcases le_or_gt x 1 with h1 | h1
  · have h := Real.abs_log_mul_self_lt x hx h1
    rw [abs_mul, abs_of_pos hx] at h
    linarith
  · rw [abs_of_nonneg (Real.log_nonneg h1.le)]
    have h := Real.log_le_sub_one_of_pos hx
    nlinarith [Real.log_nonneg h1.le]

/-- The real part of the Stirling exponent, `Re f(w) = Re w log ‖w‖ − Im w arg w − Re w`. -/
lemma re_stirF (w : ℂ) : (stirF w).re = w.re * Real.log ‖w‖ - w.im * arg w - w.re := by
  simp only [stirF, sub_re, mul_re, log_re, log_im]

/-- **Reflection of the Stirling exponent**: `Re f(−w) = −Re f(w) − π |Im w|`. The two
principal logarithms `log(−w)` and `log w` differ by `∓iπ`, and the real part of `w · (∓iπ)` is
`−π |Im w|`. -/
theorem re_stirF_neg (w : ℂ) : (stirF (-w)).re = -(stirF w).re - π * |w.im| := by
  rw [re_stirF, re_stirF, neg_re, neg_im, norm_neg]
  rcases lt_trichotomy w.im 0 with h | h | h
  · rw [arg_neg_eq_arg_add_pi_of_im_neg h, abs_of_neg h]
    ring
  · rw [h, abs_zero]
    ring
  · rw [arg_neg_eq_arg_sub_pi_of_im_pos h, abs_of_pos h]
    ring

/-- `‖cos z‖ ≤ exp |Im z|`. -/
theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h : ‖(2 : ℂ) * Complex.cos z‖ ≤ 2 * Real.exp |z.im| := by
    rw [two_cos]
    refine (norm_add_le _ _).trans ?_
    rw [norm_exp, norm_exp]
    have h1 : (z * I).re ≤ |z.im| := by
      simp only [mul_re, I_re, I_im, mul_zero, mul_one, zero_sub]
      exact neg_le_abs _
    have h2 : (-z * I).re ≤ |z.im| := by
      simp only [mul_re, I_re, I_im, mul_zero, mul_one, zero_sub, neg_im, neg_neg]
      exact le_abs_self _
    linarith [Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2]
  rw [norm_mul, Complex.norm_two] at h
  linarith

/-- On the disc `‖w‖ ≤ 2`, `|Re f(w)| ≤ 4 + 2π`. -/
theorem abs_re_stirF_le {w : ℂ} (hw : ‖w‖ ≤ 2) : |(stirF w).re| ≤ 4 + 2 * π := by
  rw [re_stirF]
  have h1 : |w.re * Real.log ‖w‖| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (abs_re_le_norm w) (abs_nonneg _)).trans
      (mul_abs_log_le_two (norm_nonneg w) hw)
  have h2 : |w.im * arg w| ≤ 2 * π := by
    rw [abs_mul]
    exact mul_le_mul ((abs_im_le_norm w).trans hw) (abs_arg_le_pi w) (abs_nonneg _)
      (by norm_num)
  have h3 : |w.re| ≤ 2 := (abs_re_le_norm w).trans hw
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- `1 ≤ √(2π)`. -/
lemma one_le_sqrt_two_pi : 1 ≤ √(2 * π) := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])

/-- `√(2π) ≤ π`. -/
lemma sqrt_two_pi_le_pi : √(2 * π) ≤ π := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.pi_gt_three]

/-- The reflection formula in midpoint form: `Γ(w + ½) Γ(½ − w) = π / cos(π w)`. -/
theorem Gamma_half_add_mul_Gamma_half_sub (w : ℂ) :
    Gamma (w + 1 / 2) * Gamma (-w + 1 / 2) = π / Complex.cos (π * w) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (w + 1 / 2)
  rw [show 1 - (w + 1 / 2) = -w + 1 / 2 by ring,
    show (π : ℂ) * (w + 1 / 2) = π * w + π / 2 by ring, Complex.sin_add_pi_div_two] at h
  exact h

/-! ## Bounds for `‖w‖² ≥ 2` -/

/-- Stirling's bound for `1/Γ` on the closed right half-plane: for `Re w ≥ 0` and `‖w‖² ≥ 2`,
`‖1/Γ(w + ½)‖ ≤ exp(3/(4‖w‖) − Re f(w))`. -/
theorem norm_inv_Gamma_half_add_le_of_re_nonneg {w : ℂ} (hre : 0 ≤ w.re) (hR : 2 ≤ ‖w‖ ^ 2) :
    ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hR
  have hw : w ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    rcases hre.eq_or_lt with h | h
    · right
      intro hi
      exact hw0 (Complex.ext h.symm hi)
    · left
      exact h
  have hμ := (norm_stirMu_le (w := w) (le_refl 0) zero_lt_one (by simpa using hre)
    (by simpa using hR)).2
  rw [sub_zero, one_mul] at hμ
  rw [Gamma_half_add hw, mul_inv, ← exp_neg, norm_mul, norm_inv, norm_exp,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hexp : Real.exp (-(stirF w + stirMu w)).re ≤ Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_re, add_re]
    linarith [neg_le_abs (stirMu w).re, abs_re_le_norm (stirMu w)]
  refine le_trans ?_ hexp
  refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
  exact inv_le_one_of_one_le₀ one_le_sqrt_two_pi

/-- Stirling's bound for `1/Γ` on the closed left half-plane, by reflection: for `Re w ≤ 0` and
`‖w‖² ≥ 2`, `‖1/Γ(w + ½)‖ ≤ exp(3/(4‖w‖) − Re f(w))`. -/
theorem norm_inv_Gamma_half_add_le_of_re_nonpos {w : ℂ} (hre : w.re ≤ 0) (hR : 2 ≤ ‖w‖ ^ 2) :
    ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
  by_cases hG : Gamma (w + 1 / 2) = 0
  · rw [hG, inv_zero, norm_zero]
    exact (Real.exp_pos _).le
  have hG' : Gamma (-w + 1 / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by rw [add_re, neg_re]; norm_num; linarith)
  have hrefl := Gamma_half_add_mul_Gamma_half_sub w
  have hc : Complex.cos (π * w) ≠ 0 := by
    intro hc
    rw [hc, div_zero] at hrefl
    exact mul_ne_zero hG hG' hrefl
  have hrefl' : Gamma (w + 1 / 2) * Gamma (-w + 1 / 2) * Complex.cos (π * w) = π := by
    rw [hrefl, div_mul_cancel₀ _ hc]
  have hinv : (Gamma (w + 1 / 2))⁻¹ = Gamma (-w + 1 / 2) * Complex.cos (π * w) / π := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [eq_div_iff hπ, inv_mul_eq_iff_eq_mul₀ hG, ← mul_assoc]
    exact hrefl'.symm
  have hn : ‖-w‖ = ‖w‖ := norm_neg w
  have hw0 : -w ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h] at hR
    norm_num at hR
  have hw : -w ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    rcases hre.eq_or_lt with h | h
    · right
      intro hi
      exact hw0 (Complex.ext (by rw [neg_re, h, neg_zero, zero_re]) hi)
    · left
      rw [neg_re]
      linarith
  have hμ := (norm_stirMu_le (w := -w) (le_refl 0) zero_lt_one (by simpa using hre)
    (by simpa [hn] using hR)).2
  rw [sub_zero, one_mul, hn] at hμ
  rw [hinv, norm_div, norm_mul, Gamma_half_add hw, norm_mul, norm_exp,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_of_nonneg Real.pi_pos.le]
  have hcos := norm_cos_le_exp_abs_im (π * w)
  have him : |((π : ℂ) * w).im| = π * |w.im| := by
    rw [show ((π : ℂ) * w).im = π * w.im by simp, abs_mul, abs_of_pos Real.pi_pos]
  rw [him] at hcos
  have hF := re_stirF_neg w
  have hexp : Real.exp (stirF (-w) + stirMu (-w)).re * Real.exp (π * |w.im|) ≤
      Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [add_re, hF]
    linarith [le_abs_self (stirMu (-w)).re, abs_re_le_norm (stirMu (-w))]
  have hpi : √(2 * π) / π ≤ 1 := (div_le_one Real.pi_pos).2 sqrt_two_pi_le_pi
  calc √(2 * π) * Real.exp (stirF (-w) + stirMu (-w)).re * ‖Complex.cos (π * w)‖ / π
      ≤ √(2 * π) * Real.exp (stirF (-w) + stirMu (-w)).re * Real.exp (π * |w.im|) / π := by
        gcongr
    _ = √(2 * π) / π *
        (Real.exp (stirF (-w) + stirMu (-w)).re * Real.exp (π * |w.im|)) := by ring
    _ ≤ 1 * Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
        gcongr
    _ = Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := one_mul _

/-- **Stirling's bound for `1/Γ` on the whole plane**: for every `w ∈ ℂ` with `‖w‖² ≥ 2`,
`‖1/Γ(w + ½)‖ ≤ exp(3/(4‖w‖) − Re f(w))`. On the left half-plane this goes through the
reflection formula, where the growth `exp(π |Im w|)` of `cos(π w)` is cancelled by
`Re f(−w) = −Re f(w) − π |Im w|`. -/
theorem norm_inv_Gamma_half_add_le {w : ℂ} (hR : 2 ≤ ‖w‖ ^ 2) :
    ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ Real.exp (3 / 4 / ‖w‖ - (stirF w).re) := by
  rcases le_total 0 w.re with h | h
  · exact norm_inv_Gamma_half_add_le_of_re_nonneg h hR
  · exact norm_inv_Gamma_half_add_le_of_re_nonpos h hR

/-- **Stirling's bound for `Γ` on the closed right half-plane**: for `Re w ≥ 0` and `‖w‖² ≥ 2`,
`‖Γ(w + ½)‖ ≤ √(2π) exp(3/(4‖w‖) + Re f(w))`. -/
theorem norm_Gamma_half_add_le {w : ℂ} (hre : 0 ≤ w.re) (hR : 2 ≤ ‖w‖ ^ 2) :
    ‖Gamma (w + 1 / 2)‖ ≤ √(2 * π) * Real.exp (3 / 4 / ‖w‖ + (stirF w).re) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at hR
  have hw : w ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    rcases hre.eq_or_lt with h | h
    · right
      intro hi
      exact hw0 (Complex.ext h.symm hi)
    · left
      exact h
  have hμ := (norm_stirMu_le (w := w) (le_refl 0) zero_lt_one (by simpa using hre)
    (by simpa using hR)).2
  rw [sub_zero, one_mul] at hμ
  rw [Gamma_half_add hw, norm_mul, norm_exp, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  gcongr
  rw [add_re]
  linarith [le_abs_self (stirMu w).re, abs_re_le_norm (stirMu w)]

/-! ## Global bounds with absolute constants -/

/-- `‖w‖² < 2` puts `w` in the disc of radius `2`. -/
lemma norm_le_two_of_sq_lt {w : ℂ} (h : ¬ 2 ≤ ‖w‖ ^ 2) : ‖w‖ ≤ 2 := by
  nlinarith [norm_nonneg w]

/-- `‖w‖² ≥ 2` gives `3/(4‖w‖) ≤ 1`. -/
lemma three_div_four_div_le_one {w : ℂ} (h : 2 ≤ ‖w‖ ^ 2) : 3 / 4 / ‖w‖ ≤ 1 := by
  have h1 : 1 ≤ ‖w‖ := by nlinarith [norm_nonneg w]
  rw [div_le_one (by linarith)]
  linarith

/-- **Global bound for `1/Γ`**: there is an absolute constant `C > 0` with
`‖1/Γ(w + ½)‖ ≤ C exp(−Re f(w))` for every `w ∈ ℂ`. -/
theorem exists_norm_inv_Gamma_half_add_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ C * Real.exp (-(stirF w).re) := by
  have hcont : ContinuousOn (fun w : ℂ => (Gamma (w + 1 / 2))⁻¹) (Metric.closedBall 0 2) :=
    (differentiable_one_div_Gamma.comp (differentiable_id.add_const _)).continuous.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn hcont
  refine ⟨Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π), by positivity, fun w => ?_⟩
  have hE : 0 ≤ Real.exp (-(stirF w).re) := (Real.exp_pos _).le
  have hB : 0 ≤ (|M| + 1) * Real.exp (4 + 2 * π) := by positivity
  by_cases hR : 2 ≤ ‖w‖ ^ 2
  · calc ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ Real.exp (3 / 4 / ‖w‖ - (stirF w).re) :=
          norm_inv_Gamma_half_add_le hR
      _ = Real.exp (3 / 4 / ‖w‖) * Real.exp (-(stirF w).re) := by
          rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ Real.exp 1 * Real.exp (-(stirF w).re) := by
          gcongr
          exact three_div_four_div_le_one hR
      _ ≤ (Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π)) * Real.exp (-(stirF w).re) := by
          gcongr
          linarith
  · have hw := norm_le_two_of_sq_lt hR
    have hb := hM w (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
    have hF := (abs_le.1 (abs_re_stirF_le hw)).2
    have h1 : 1 ≤ Real.exp (4 + 2 * π) * Real.exp (-(stirF w).re) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖(Gamma (w + 1 / 2))⁻¹‖ ≤ |M| + 1 := by linarith [le_abs_self M]
      _ ≤ (|M| + 1) * (Real.exp (4 + 2 * π) * Real.exp (-(stirF w).re)) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (|M| + 1) * Real.exp (4 + 2 * π) * Real.exp (-(stirF w).re) := by ring
      _ ≤ (Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π)) * Real.exp (-(stirF w).re) := by
          gcongr
          linarith [Real.exp_pos 1]

/-- **Global bound for `Γ` on the closed right half-plane**: there is an absolute constant
`C > 0` with `‖Γ(w + ½)‖ ≤ C exp(Re f(w))` for every `w` with `Re w ≥ 0`. -/
theorem exists_norm_Gamma_half_add_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 ≤ w.re → ‖Gamma (w + 1 / 2)‖ ≤ C * Real.exp ((stirF w).re) := by
  set K := Metric.closedBall (0 : ℂ) 2 ∩ {w : ℂ | 0 ≤ w.re}
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) 2).inter_right (isClosed_le continuous_const continuous_re)
  have hcont : ContinuousOn (fun w : ℂ => Gamma (w + 1 / 2)) K := by
    intro w hw
    have hre : 0 ≤ w.re := hw.2
    have hd : DifferentiableAt ℂ Gamma (w + 1 / 2) := by
      refine differentiableAt_Gamma _ fun m e => ?_
      have := congrArg Complex.re e
      rw [add_re, neg_re, natCast_re] at this
      norm_num at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    exact (ContinuousAt.comp (f := fun x : ℂ => x + 1 / 2) (x := w) hd.continuousAt
      (by fun_prop)).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨√(2 * π) * Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π), by positivity,
    fun w hre => ?_⟩
  have hE : 0 ≤ Real.exp ((stirF w).re) := (Real.exp_pos _).le
  by_cases hR : 2 ≤ ‖w‖ ^ 2
  · calc ‖Gamma (w + 1 / 2)‖ ≤ √(2 * π) * Real.exp (3 / 4 / ‖w‖ + (stirF w).re) :=
          norm_Gamma_half_add_le hre hR
      _ = √(2 * π) * Real.exp (3 / 4 / ‖w‖) * Real.exp ((stirF w).re) := by
          rw [Real.exp_add, mul_assoc]
      _ ≤ √(2 * π) * Real.exp 1 * Real.exp ((stirF w).re) := by
          gcongr
          exact three_div_four_div_le_one hR
      _ ≤ (√(2 * π) * Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π)) *
          Real.exp ((stirF w).re) := by
          gcongr
          have : 0 ≤ (|M| + 1) * Real.exp (4 + 2 * π) := by positivity
          linarith
  · have hw := norm_le_two_of_sq_lt hR
    have hb := hM w ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hw, hre⟩
    have hF := (abs_le.1 (abs_re_stirF_le hw)).1
    have h1 : 1 ≤ Real.exp (4 + 2 * π) * Real.exp ((stirF w).re) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖Gamma (w + 1 / 2)‖ ≤ |M| + 1 := by linarith [le_abs_self M]
      _ ≤ (|M| + 1) * (Real.exp (4 + 2 * π) * Real.exp ((stirF w).re)) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = (|M| + 1) * Real.exp (4 + 2 * π) * Real.exp ((stirF w).re) := by ring
      _ ≤ (√(2 * π) * Real.exp 1 + (|M| + 1) * Real.exp (4 + 2 * π)) *
          Real.exp ((stirF w).re) := by
          gcongr
          have : 0 ≤ √(2 * π) * Real.exp 1 := by positivity
          linarith

end Lightlike.Asymptotics
