import Mathlib

/-!
# The holomorphic function `z ↦ z coth(πz)` on the strip `|Im z| < 1`

`rhoCoth z = z cosh(πz)/sinh(πz)` for `z ≠ 0` and `1/π` at `0` (the removable singularity of `z coth(πz)`);
`differentiableOn_rhoCoth` shows it is holomorphic on `|Im z| < 1` (Riemann's removable singularity theorem in
the form `Complex.differentiableOn_compl_singleton_and_continuousAt_iff`). At the shifted points
`x ± i/2` it is `(x ± i/2) tanh(πx)` (`rhoCoth_add_half`, `rhoCoth_sub_half`), because
`coth(π(x ± i/2)) = tanh(πx)`: this is how the odd Plancherel density `ρ coth(πρ)` becomes the even density
`ρ tanh(πρ)` after a contour shift by `i/2` (`docs/notes/sl2r-odd-plancherel-route.md`).
-/

open Complex Filter Topology Set
open scoped Real

noncomputable section

namespace Lightlike.Lorentz.SL2ROddPlancherel

/-- The holomorphic extension of `z ↦ z coth(πz)` across `0` (value `1/π`). -/
noncomputable def rhoCoth (z : ℂ) : ℂ :=
  if z = 0 then 1 / (Real.pi : ℂ) else z * Complex.cosh (Real.pi * z) / Complex.sinh (Real.pi * z)

lemma sinh_pi_mul_ne_zero {z : ℂ} (hz : |z.im| < 1) (hz0 : z ≠ 0) : Complex.sinh (Real.pi * z) ≠ 0 := by
  intro h
  have h' : Complex.sin ((Real.pi * z : ℂ) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, h, zero_mul]
  rw [Complex.sin_eq_zero_iff] at h'
  obtain ⟨n, hn⟩ := h'
  have : z = (-(n : ℂ)) * Complex.I := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    apply mul_left_cancel₀ hpi
    apply mul_right_cancel₀ hI
    calc (Real.pi : ℂ) * z * Complex.I = n * Real.pi := hn
      _ = (Real.pi : ℂ) * (-(n : ℂ) * Complex.I) * Complex.I := by
        have : Complex.I * Complex.I = -1 := Complex.I_mul_I
        linear_combination ((n : ℂ) * Real.pi) * this
  have him : z.im = -n := by rw [this]; simp
  rw [him] at hz
  have h2 : |n| < 1 := by
    rw [abs_neg] at hz
    exact_mod_cast hz
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp h2
  apply hz0
  rw [‹z = _›, hn0]; simp

lemma tendsto_rhoCoth_zero :
    Tendsto (fun z : ℂ => z * Complex.cosh (Real.pi * z) / Complex.sinh (Real.pi * z)) (𝓝[≠] 0)
      (𝓝 (1 / (Real.pi : ℂ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hd : HasDerivAt (fun z : ℂ => Complex.sinh (Real.pi * z)) (Real.pi : ℂ) 0 := by
    have := (Complex.hasDerivAt_sinh (Real.pi * (0 : ℂ))).comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ))
    exact this.congr_deriv (by simp)
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  have h1 : Tendsto (fun z : ℂ => Complex.sinh (Real.pi * z) / z) (𝓝[≠] 0) (𝓝 (Real.pi : ℂ)) := by
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp [slope_def_field, div_eq_inv_mul]
  have h2 : Tendsto (fun z : ℂ => Complex.cosh (Real.pi * z)) (𝓝[≠] 0) (𝓝 1) := by
    have : Continuous fun z : ℂ => Complex.cosh (Real.pi * z) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h3 := h2.div h1 hpi
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz' : z ≠ 0 := hz
  by_cases hs0 : Complex.sinh (Real.pi * z) = 0
  · simp [hs0]
  · simp only [Pi.div_apply]
    field_simp

lemma differentiableOn_rhoCoth : DifferentiableOn ℂ rhoCoth {z : ℂ | |z.im| < 1} := by
  have hopen : IsOpen {z : ℂ | |z.im| < 1} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 0)
    (hopen.mem_nhds (by simp))]
  constructor
  · intro z hz
    have hz0 : z ≠ 0 := hz.2
    have hs := sinh_pi_mul_ne_zero hz.1 hz0
    have hd : DifferentiableAt ℂ (fun z : ℂ => z * Complex.cosh (Real.pi * z) / Complex.sinh (Real.pi * z)) z := by
      refine DifferentiableAt.div (by fun_prop) (by fun_prop) hs
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    simp [rhoCoth, hw]
  · have hlim := tendsto_rhoCoth_zero
    rw [← continuousWithinAt_compl_self]
    have h0 : rhoCoth 0 = 1 / (Real.pi : ℂ) := by simp [rhoCoth]
    unfold ContinuousWithinAt
    rw [h0]
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have : z ≠ 0 := hz
    simp [rhoCoth, this]

lemma rhoCoth_add_half (x : ℝ) :
    rhoCoth ((x : ℂ) + Complex.I / 2) = ((x : ℂ) + Complex.I / 2) * Complex.tanh (Real.pi * x) := by
  have hne : ((x : ℂ) + Complex.I / 2) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hc : Complex.cosh (Real.pi * x) ≠ 0 := by
    have : Complex.cosh ((Real.pi : ℂ) * x) = ((Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
    rw [this]; exact_mod_cast (Real.cosh_pos _).ne'
  have e1 : Complex.cosh (Real.pi * ((x : ℂ) + Complex.I / 2)) = Complex.I * Complex.sinh (Real.pi * x) := by
    have : (Real.pi : ℂ) * ((x : ℂ) + Complex.I / 2) = Real.pi * x + (Real.pi / 2 : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.cosh_add]
    simp [Complex.cosh_mul_I, Complex.sinh_mul_I]
    ring
  have e2 : Complex.sinh (Real.pi * ((x : ℂ) + Complex.I / 2)) = Complex.I * Complex.cosh (Real.pi * x) := by
    have : (Real.pi : ℂ) * ((x : ℂ) + Complex.I / 2) = Real.pi * x + (Real.pi / 2 : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.sinh_add]
    simp [Complex.cosh_mul_I, Complex.sinh_mul_I]
    ring
  simp only [rhoCoth, hne, ↓reduceIte]
  rw [e1, e2, Complex.tanh_eq_sinh_div_cosh]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp

lemma rhoCoth_sub_half (x : ℝ) :
    rhoCoth ((x : ℂ) - Complex.I / 2) = ((x : ℂ) - Complex.I / 2) * Complex.tanh (Real.pi * x) := by
  have hne : ((x : ℂ) - Complex.I / 2) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have e1 : Complex.cosh (Real.pi * ((x : ℂ) - Complex.I / 2)) =
      -(Complex.I * Complex.sinh (Real.pi * x)) := by
    have : (Real.pi : ℂ) * ((x : ℂ) - Complex.I / 2) = Real.pi * x + (-(Real.pi / 2) : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.cosh_add]
    simp [Complex.cosh_mul_I, Complex.sinh_mul_I]
    ring
  have e2 : Complex.sinh (Real.pi * ((x : ℂ) - Complex.I / 2)) =
      -(Complex.I * Complex.cosh (Real.pi * x)) := by
    have : (Real.pi : ℂ) * ((x : ℂ) - Complex.I / 2) = Real.pi * x + (-(Real.pi / 2) : ℝ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.sinh_add]
    simp [Complex.cosh_mul_I, Complex.sinh_mul_I]
    ring
  have hc : Complex.cosh (Real.pi * x) ≠ 0 := by
    have : Complex.cosh ((Real.pi : ℂ) * x) = ((Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
    rw [this]; exact_mod_cast (Real.cosh_pos _).ne'
  simp only [rhoCoth, hne, ↓reduceIte]
  rw [e1, e2, Complex.tanh_eq_sinh_div_cosh]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp

/-- Away from the imaginary axis `|cosh w| ≤ 3 |sinh w|`: `e^R + e^{-R} ≤ 3 (e^R - e^{-R})` once `e^{2R} ≥ 2`. -/
lemma norm_cosh_le_three_mul_norm_sinh {w : ℂ} (hw : 1 ≤ |w.re|) :
    ‖Complex.cosh w‖ ≤ 3 * ‖Complex.sinh w‖ := by
  -- reduce to `0 ≤ Re w`
  have key : ∀ u : ℂ, 1 ≤ u.re → ‖Complex.cosh u‖ ≤ 3 * ‖Complex.sinh u‖ := by
    intro u hu
    have h1 : ‖Complex.exp u‖ = Real.exp u.re := Complex.norm_exp u
    have h2 : ‖Complex.exp (-u)‖ = Real.exp (-u.re) := by rw [Complex.norm_exp]; simp
    have hc : ‖Complex.cosh u‖ ≤ (Real.exp u.re + Real.exp (-u.re)) / 2 := by
      rw [Complex.cosh]
      calc ‖(Complex.exp u + Complex.exp (-u)) / 2‖ = ‖Complex.exp u + Complex.exp (-u)‖ / 2 := by
            rw [norm_div]; simp
        _ ≤ (‖Complex.exp u‖ + ‖Complex.exp (-u)‖) / 2 := by
            gcongr; exact norm_add_le _ _
        _ = _ := by rw [h1, h2]
    have hs : (Real.exp u.re - Real.exp (-u.re)) / 2 ≤ ‖Complex.sinh u‖ := by
      rw [Complex.sinh]
      have : ‖Complex.exp u‖ - ‖Complex.exp (-u)‖ ≤ ‖Complex.exp u - Complex.exp (-u)‖ := norm_sub_norm_le _ _
      calc (Real.exp u.re - Real.exp (-u.re)) / 2 = (‖Complex.exp u‖ - ‖Complex.exp (-u)‖) / 2 := by
            rw [h1, h2]
        _ ≤ ‖Complex.exp u - Complex.exp (-u)‖ / 2 := by gcongr
        _ = ‖(Complex.exp u - Complex.exp (-u)) / 2‖ := by rw [norm_div]; simp
    have hexp : 2 ≤ Real.exp (2 * u.re) := by
      have := Real.add_one_le_exp (2 * u.re)
      linarith
    have hE : Real.exp (2 * u.re) = Real.exp u.re * Real.exp u.re := by
      rw [two_mul, Real.exp_add]
    have hinv : Real.exp (-u.re) * Real.exp u.re = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos u.re
    have hpos' := Real.exp_pos (-u.re)
    nlinarith
  rcases le_total 0 w.re with h | h
  · rw [abs_of_nonneg h] at hw; exact key w hw
  · rw [abs_of_nonpos h] at hw
    have := key (-w) (by simpa using hw)
    simpa [Complex.cosh_neg, Complex.sinh_neg] using this

/-- **Growth of `rhoCoth` on the strip `|Im w| ≤ 1/2`**: `‖rhoCoth w‖ ≤ M (1 + |Re w|)`. -/
lemma exists_norm_rhoCoth_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, |w.im| ≤ 1 / 2 → ‖rhoCoth w‖ ≤ M * (1 + |w.re|) := by
  have hK : IsCompact ((Icc (-1 : ℝ) 1) ×ℂ (Icc (-1 / 2 : ℝ) (1 / 2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn rhoCoth ((Icc (-1 : ℝ) 1) ×ℂ (Icc (-1 / 2 : ℝ) (1 / 2))) := by
    refine differentiableOn_rhoCoth.continuousOn.mono ?_
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    have := hw.2
    show |w.im| < 1
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max 3 (max B 0), by positivity, fun w hw => ?_⟩
  by_cases hre : 1 ≤ |w.re|
  · have hw0 : w ≠ 0 := by
      intro h0; rw [h0] at hre; simp at hre; linarith
    have hs : Complex.sinh (Real.pi * w) ≠ 0 := by
      have h1 : |w.im| < 1 := by linarith
      exact sinh_pi_mul_ne_zero h1 hw0
    have hcs := norm_cosh_le_three_mul_norm_sinh (w := Real.pi * w) (by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, abs_mul,
        abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three, abs_nonneg w.re])
    simp only [rhoCoth, hw0, ↓reduceIte]
    rw [norm_div, norm_mul]
    have hsn : 0 < ‖Complex.sinh (Real.pi * w)‖ := norm_pos_iff.mpr hs
    rw [div_le_iff₀ hsn]
    have hwn : ‖w‖ ≤ 1 + |w.re| := by
      calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ ≤ 1 + |w.re| := by linarith
    have h3w : 3 * ‖w‖ ≤ max 3 (max B 0) * (1 + |w.re|) := by
      have hM := le_max_left (3 : ℝ) (max B 0)
      nlinarith [norm_nonneg w, abs_nonneg w.re,
        mul_nonneg (sub_nonneg.2 hM) (by positivity : (0 : ℝ) ≤ 1 + |w.re|)]
    calc ‖w‖ * ‖Complex.cosh (Real.pi * w)‖ ≤ ‖w‖ * (3 * ‖Complex.sinh (Real.pi * w)‖) := by gcongr
      _ = 3 * ‖w‖ * ‖Complex.sinh (Real.pi * w)‖ := by ring
      _ ≤ (max 3 (max B 0) * (1 + |w.re|)) * ‖Complex.sinh (Real.pi * w)‖ := by gcongr
  · have hre := not_le.mp hre
    have hmem : w ∈ (Icc (-1 : ℝ) 1) ×ℂ (Icc (-1 / 2 : ℝ) (1 / 2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨by linarith [(abs_lt.mp hre).1], by linarith [(abs_lt.mp hre).2]⟩,
        ⟨by linarith [(abs_le.mp hw).1], by linarith [(abs_le.mp hw).2]⟩⟩
    calc ‖rhoCoth w‖ ≤ B := hB w hmem
      _ ≤ max 3 (max B 0) := le_trans (le_max_left B 0) (le_max_right _ _)
      _ ≤ max 3 (max B 0) * (1 + |w.re|) := by
          have : (1 : ℝ) ≤ 1 + |w.re| := by linarith [abs_nonneg w.re]
          nlinarith [le_max_left (3 : ℝ) (max B 0), le_max_left B (0 : ℝ), le_max_right B (0:ℝ)]

end Lightlike.Lorentz.SL2ROddPlancherel
