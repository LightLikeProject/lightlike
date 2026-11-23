import Lightlike.FieldTheory.Borel.Strip
import Lightlike.FieldTheory.Borel.Hankel

/-!
# The Laplace representation of `f`: support lemmas for T-GF7-P5

Notation: `G x c = b₀(x) - a₀` along the line `Re w = c`, written as an integral in `ξ` where `w = c + 2πiξ`.
We show `G x c = ∫ ξ, e^{xw} ψ(ξ)` with `ψ(ξ) = (f(w⁻¹) - a₀)/w`, the bound `‖G x c‖ ≤ e^{xc} M/(2c)`, and
that `G x c = 0` for `x ≤ 0`.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat FourierTransform

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a₀ : ℂ} {R M : ℝ}

/-- `b₀(x) - a₀` as an integral over `ξ`, with `w = c + 2πiξ`. -/
lemma borelZero_sub_eq (f : ℂ → ℂ) (a₀ : ℂ) (x c : ℝ) :
    borelZero f a₀ x c - a₀ = ∫ ξ : ℝ, borelIntegrand f a₀ x (vline c ξ) := by
  unfold borelZero
  rw [add_sub_cancel_left]
  have h := Measure.integral_comp_mul_left (fun y : ℝ => borelIntegrand f a₀ x (c + y * I)) (2 * π)
  have e : ∀ ξ : ℝ, borelIntegrand f a₀ x (vline c ξ) = borelIntegrand f a₀ x (c + ((2 * π * ξ : ℝ) : ℂ) * I) :=
    fun ξ => by simp only [vline]; push_cast; ring_nf
  simp_rw [e]
  rw [h, Complex.real_smul, abs_of_pos (by positivity)]
  push_cast
  rfl

lemma integral_inv_sq_vline {c : ℝ} (hc : 0 < c) :
    ∫ ξ : ℝ, (c ^ 2 + (2 * π * ξ) ^ 2)⁻¹ = 1 / (2 * c) := by
  have h := Measure.integral_comp_mul_left (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) (2 * π)
  rw [h, integral_inv_sq_add hc, smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

/-- `‖b₀(x) - a₀‖ ≤ e^{xc} M/(2c)` along the line `Re w = c > 1/R`. -/
lemma norm_borelZero_sub_le (hR : 0 < R) (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (x : ℝ) {c : ℝ}
    (hc : 1 / R < c) : ‖borelZero f a₀ x c - a₀‖ ≤ Real.exp (x * c) * M / (2 * c) := by
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  rw [borelZero_sub_eq]
  have hint := (integrable_inv_sq_vline hc0).const_mul (Real.exp (x * c) * M)
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun ξ => ?_)).trans_eq ?_
  · have h := norm_borelIntegrand_le hR hM x (w := vline c ξ) (by rwa [vline_re])
    rw [vline_re, sq_norm_vline] at h
    simpa [div_eq_mul_inv, mul_assoc] using h
  · rw [integral_const_mul, integral_inv_sq_vline hc0]
    field_simp

/-- `b₀(x) = a₀` for `x ≤ 0`. -/
lemma borelZero_of_nonpos (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (hM0 : 0 ≤ M) {x : ℝ} (hx : x ≤ 0) {c : ℝ} (hc : 1 / R < c) :
    borelZero f a₀ x c = a₀ := by
  have hR' : 0 < 1 / R := one_div_pos.2 hR
  have hb : ∀ c' : ℝ, max c (1 / R + 1) ≤ c' → ‖borelZero f a₀ x c - a₀‖ ≤ M / (2 * c') := by
    intro c' hc'
    have h1 : 1 / R < c' := by linarith [le_max_right c (1 / R + 1)]
    rw [borelZero_indep hR hf hM hM0 x hc h1]
    have hc'0 : 0 < c' := hR'.trans h1
    refine (norm_borelZero_sub_le hR hM x h1).trans ?_
    have : Real.exp (x * c') ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc Real.exp (x * c') * M / (2 * c') ≤ 1 * M / (2 * c') := by gcongr
      _ = M / (2 * c') := by rw [one_mul]
  have hlim : Tendsto (fun c' : ℝ => M / (2 * c')) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := M)).div_atTop (tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num))
    simpa using this
  have := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨_, hb⟩)
  rw [← sub_eq_zero]
  exact norm_le_zero_iff.1 this

/-- `ψ(ξ) = (f(w⁻¹) - a₀)/w` at `w = c + 2πiξ`: `b₀ - a₀` is its inverse Fourier transform, up to `e^{cx}`. -/
noncomputable def psiLine (f : ℂ → ℂ) (a₀ : ℂ) (c ξ : ℝ) : ℂ := (f (vline c ξ)⁻¹ - a₀) / vline c ξ

lemma continuous_psiLine (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R)) {c : ℝ} (hc : 1 / R < c) :
    Continuous (psiLine f a₀ c) := by
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  refine continuous_iff_continuousAt.2 fun ξ => ?_
  have hv : (vline c ξ)⁻¹ ∈ diskC R := inv_mem_diskC (by rwa [vline_re])
  have h1 : ContinuousAt f (vline c ξ)⁻¹ := (hf.differentiableAt ((isOpen_diskC hR).mem_nhds hv)).continuousAt
  have h2 : ContinuousAt (fun ξ => (vline c ξ)⁻¹) ξ :=
    ((continuous_vline c).continuousAt).inv₀ (vline_ne_zero hc0 ξ)
  unfold psiLine
  exact ((ContinuousAt.comp (f := fun ξ => (vline c ξ)⁻¹) h1 h2).sub continuousAt_const).div (continuous_vline c).continuousAt (vline_ne_zero hc0 ξ)

lemma integrable_psiLine (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) {c : ℝ} (hc : 1 / R < c) : Integrable (psiLine f a₀ c) := by
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  refine ((integrable_inv_norm_vline_pow hc0 (n := 2) le_rfl).const_mul M).mono'
    (continuous_psiLine hR hf hc).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 := hM _ (inv_mem_diskC (w := vline c ξ) (by rwa [vline_re]))
  rw [norm_inv] at h1
  have hpos : 0 < ‖vline c ξ‖ := norm_pos_iff.2 (vline_ne_zero hc0 ξ)
  unfold psiLine
  rw [norm_div]
  calc ‖f (vline c ξ)⁻¹ - a₀‖ / ‖vline c ξ‖ ≤ M * ‖vline c ξ‖⁻¹ / ‖vline c ξ‖ := by gcongr
    _ = M * (‖vline c ξ‖ ^ 2)⁻¹ := by field_simp

/-- The inverse Fourier transform of `ψ` is `e^{-cx} (b₀(x) - a₀)`. -/
lemma fourierInv_psiLine (f : ℂ → ℂ) (a₀ : ℂ) (c x : ℝ) :
    𝓕⁻ (psiLine f a₀ c) x = cexp (-((c : ℂ) * x)) * (borelZero f a₀ x c - a₀) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, borelZero_sub_eq,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, borelIntegrand, psiLine]
  have h1 : cexp (↑x * vline c ξ) = cexp (↑c * ↑x) * cexp (↑(-2 * π * ξ * -x) * I) := by
    rw [← Complex.exp_add]; congr 1; simp only [vline]; push_cast; ring
  rw [h1, mul_div_assoc]
  have : cexp (-((c : ℂ) * x)) * (cexp (↑c * ↑x) * cexp (↑(-2 * π * ξ * -x) * I) *
      ((f (vline c ξ)⁻¹ - a₀) / vline c ξ)) =
      (cexp (-((c : ℂ) * x)) * cexp (↑c * ↑x)) * cexp (↑(-2 * π * ξ * -x) * I) *
      ((f (vline c ξ)⁻¹ - a₀) / vline c ξ) := by ring
  rw [this, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

lemma continuous_fourierInv_psiLine (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) {c : ℝ} (hc : 1 / R < c) :
    Continuous (𝓕⁻ (psiLine f a₀ c)) := by
  have h : 𝓕⁻ (psiLine f a₀ c) = fun x => 𝓕 (psiLine f a₀ c) (-x) :=
    funext fun x => Real.fourierInv_eq_fourier_neg _ _
  rw [h]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (integrable_psiLine hR hf hM hc)).comp continuous_neg

/-- `e^{-cx} (b₀(x) - a₀)` is integrable on `ℝ`. -/
lemma integrable_fourierInv_psiLine (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (hM0 : 0 ≤ M) {c : ℝ} (hc : 1 / R < c) :
    Integrable (𝓕⁻ (psiLine f a₀ c)) := by
  have hR' : 0 < 1 / R := one_div_pos.2 hR
  set c' : ℝ := (1 / R + c) / 2 with hc'
  have h1 : 1 / R < c' := by rw [hc']; linarith
  have h2 : 0 < c - c' := by rw [hc']; linarith
  have hc'0 : 0 < c' := hR'.trans h1
  have hI : IntegrableOn (𝓕⁻ (psiLine f a₀ c)) (Ioi 0) := by
    refine ((integrableOn_pow_mul_exp_neg 0 h2).const_mul (M / (2 * c'))).mono'
      (continuous_fourierInv_psiLine hR hf hM hc).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [fourierInv_psiLine, norm_mul, Complex.norm_exp, borelZero_indep hR hf hM hM0 x hc h1]
    have hre : (-((c : ℂ) * x)).re = -(c * x) := by simp
    rw [hre]
    have hb := norm_borelZero_sub_le hR hM x h1
    calc Real.exp (-(c * x)) * ‖borelZero f a₀ x c' - a₀‖
        ≤ Real.exp (-(c * x)) * (Real.exp (x * c') * M / (2 * c')) := by gcongr
      _ = M / (2 * c') * (x ^ 0 * Real.exp (-((c - c') * x))) := by
        have e : Real.exp (-(c * x)) * Real.exp (x * c') = Real.exp (-((c - c') * x)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [pow_zero, one_mul, ← e]
        ring
  refine hI.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  rw [fourierInv_psiLine, borelZero_of_nonpos hR hf hM hM0 (not_lt.1 hx) hc, sub_self, mul_zero]

/-- **Laplace transform of `b₀ - a₀` on the line**: for `c > 1/R` and `w = c + 2πiξ`,
`∫_0^∞ e^{-xw} (b₀(x) - a₀) dx = (f(w⁻¹) - a₀)/w`, by Fourier inversion. -/
lemma laplace_line (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (hM0 : 0 ≤ M) {c : ℝ} (hc : 1 / R < c) (ξ : ℝ) :
    ∫ x in Ioi (0 : ℝ), cexp (-((x : ℂ) * vline c ξ)) * (borelZero f a₀ x c - a₀) =
      (f (vline c ξ)⁻¹ - a₀) / vline c ξ := by
  have hint : Integrable (𝓕 (psiLine f a₀ c)) := by
    have h := (integrable_fourierInv_psiLine hR hf hM hM0 hc).comp_neg
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    show 𝓕⁻ (psiLine f a₀ c) (-x) = _
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hψ := (continuous_psiLine (a₀ := a₀) hR hf hc).fourier_fourierInv_eq (integrable_psiLine hR hf hM hc) hint
  have hx := congrFun hψ ξ
  rw [Real.fourier_real_eq_integral_exp_smul] at hx
  simp_rw [fourierInv_psiLine, smul_eq_mul] at hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) (fun x hx' => by
    rw [borelZero_of_nonpos hR hf hM hM0 (not_lt.1 hx') hc, sub_self, mul_zero, mul_zero])] at hx
  unfold psiLine at hx
  rw [← hx]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 3
  simp only [vline]
  push_cast
  ring

/-- **`f` is the Laplace transform of `b_0`** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B,
eq. (B.8), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem, for `z` in the disk `C_R` and any line
`Re w = c > 1/R`, `f(z) = (1/z) ∫_0^∞ e^{-x/z} b_0(x) dx`.

The source takes the line `Re w = c` with `Re z⁻¹ > c`; here any `c > 1/R` is allowed, `b_0` not depending on the
line (`borelZero_indep`) (kind: representation). Non-vacuous: `sokalHyp_const`. Serves task T-GF7-P5; the statement
is copied word for word from the closed task `T-GF7-P5`. -/
theorem SokalHyp.eq_laplace_borelZero {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) {z : ℂ} (hz : z ∈ diskC R) :
    f z = z⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * borelZero f (a 0) x c := by
  have hR := h.R_pos
  have hM : ∀ z ∈ diskC R, ‖f z - a 0‖ ≤ K / ρ * ‖z‖ := fun z hz => by
    have := h.rem 1 z hz
    simpa using this
  have hM0 : 0 ≤ K / ρ := div_nonneg h.K_nonneg h.ρ_pos.le
  set w : ℂ := z⁻¹ with hw
  have hwre : 1 / R < w.re := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hw] at hwre
    linarith [one_div_pos.2 hR]
  have hw0 : w ≠ 0 := inv_ne_zero hz0
  have hwz : w⁻¹ = z := inv_inv z
  set c0 : ℝ := w.re with hc0
  have hline : vline c0 (w.im / (2 * π)) = w := by
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have h2 : (2 : ℂ) * π * ((w.im / (2 * π) : ℝ) : ℂ) = (w.im : ℂ) := by
      push_cast; field_simp
    rw [vline, h2, hc0]
    exact Complex.re_add_im w
  have hL := laplace_line (a₀ := a 0) hR h.analytic hM hM0 hwre (w.im / (2 * π))
  rw [hline, hwz] at hL
  have hpos : 0 < c0 := (one_div_pos.2 hR).trans hwre
  -- integrability of the two pieces
  have hrw : ∀ x : ℝ, cexp (-((x : ℂ) * w)) * (borelZero f (a 0) x c0 - a 0) =
      cexp (-(((x * w.im : ℝ) : ℂ) * I)) * 𝓕⁻ (psiLine f (a 0) c0) x := fun x => by
    rw [fourierInv_psiLine, ← mul_assoc, ← Complex.exp_add]
    congr 3
    conv_lhs => rw [← Complex.re_add_im w]
    rw [hc0]
    push_cast
    ring
  have hI1 : IntegrableOn (fun x : ℝ => cexp (-((x : ℂ) * w)) * (borelZero f (a 0) x c0 - a 0)) (Ioi 0) := by
    have hint := (integrable_fourierInv_psiLine hR h.analytic hM hM0 hwre).norm.integrableOn (s := Ioi 0)
    refine hint.mono' ?_ ?_
    · simp_rw [hrw]
      exact ((by fun_prop : Continuous fun x : ℝ => cexp (-(((x * w.im : ℝ) : ℂ) * I))).mul
        (continuous_fourierInv_psiLine hR h.analytic hM hwre)).aestronglyMeasurable.restrict
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [hrw, norm_mul]
      have : ‖cexp (-(((x * w.im : ℝ) : ℂ) * I))‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, one_mul]
  have hI2 : IntegrableOn (fun x : ℝ => cexp (-((x : ℂ) * w)) * a 0) (Ioi 0) := by
    have := integrableOn_pow_mul_cexp_neg 0 (s := w) hpos
    simp only [pow_zero, one_mul] at this
    simp_rw [mul_comm w] at this
    exact MeasureTheory.Integrable.mul_const this _
  have hI2' : ∫ x in Ioi (0 : ℝ), cexp (-((x : ℂ) * w)) * a 0 = a 0 * z := by
    rw [integral_mul_const]
    have := integral_pow_mul_cexp_neg 0 (s := w) hpos
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one] at this
    simp_rw [mul_comm w] at this
    rw [this, ← hwz, mul_comm]
    simp [hw]
  have hsplit : ∫ x in Ioi (0 : ℝ), cexp (-(x / z)) * borelZero f (a 0) x c =
      ∫ x in Ioi (0 : ℝ), (cexp (-((x : ℂ) * w)) * (borelZero f (a 0) x c0 - a 0) +
        cexp (-((x : ℂ) * w)) * a 0) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [borelZero_indep hR h.analytic hM hM0 x hc hwre, hw, div_eq_mul_inv]
    ring
  rw [hsplit, integral_add hI1 hI2, hL, hI2']
  rw [← hwz] at hz0 ⊢
  field_simp
  ring

end Lightlike.FieldTheory.Borel
