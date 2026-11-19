import Lightlike.FieldTheory.Borel.Hankel
import Lightlike.FieldTheory.ZeroDim.QuarticComplex

/-!
# Shifting a vertical line of integration

A function analytic on a closed vertical strip `c₁ ≤ Re w ≤ c₂` (`0 < c₁`) and bounded there by `C/|w|²` has the same
integral along the two boundary lines (`integral_vertical_eq`), by Cauchy's theorem on rectangles and the decay on
their horizontal sides.

This gives the function `b_0` of the proof of the Nevanlinna–Sokal theorem (Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776, eq. (B.3), p. 25): for `f` analytic in the disk `C_R = {Re z⁻¹ > 1/R}` with `|f(z) - a₀| ≤ M|z|`,
`b₀(x) = a₀ + (1/2π) ∫_ℝ e^{x(c + iy)} (f((c + iy)⁻¹) - a₀)/(c + iy) dy` does not depend on `c > 1/R`
(`borelZero_indep`). The source's integral `(1/2πi) ∮ e^{x/z} z⁻¹ f(z) dz` over the circle `Re z⁻¹ = 1/c` is this
integral in `w = z⁻¹` plus `a₀ (1/2πi) ∫ e^{xw} dw/w = a₀`; the term `a₀` is taken out so that the integral converges
absolutely.

## Main results

* `integral_vertical_eq`: the integrals along two vertical lines of a function analytic and `O(|w|⁻²)` between them
  agree.
* `borelZero_indep`: `b₀` does not depend on the line `Re w = c`, `c > 1/R`.
-/

open MeasureTheory Set Filter Complex
open scoped Topology Real Interval

namespace Lightlike.FieldTheory.Borel

/-- `y ↦ (c² + y²)⁻¹` is integrable. -/
lemma integrable_inv_sq_add {c : ℝ} (hc : 0 < c) : Integrable fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹ := by
  have h := (integrable_inv_one_add_sq.comp_mul_left' (R := c⁻¹) (by positivity)).const_mul (c ^ 2)⁻¹
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  field_simp

lemma sq_norm_add_mul_I (c y : ℝ) : ‖(c : ℂ) + y * I‖ ^ 2 = c ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- A function bounded by `C/|w|²` on the line `Re w = c > 0` is integrable along it. -/
lemma integrable_vertical_of_bound {F : ℂ → ℂ} {c C : ℝ} (hc : 0 < c) (hF : Continuous fun y : ℝ => F (c + y * I))
    (hb : ∀ y : ℝ, ‖F (c + y * I)‖ ≤ C / ‖(c : ℂ) + y * I‖ ^ 2) : Integrable fun y : ℝ => F (c + y * I) := by
  refine ((integrable_inv_sq_add hc).const_mul C).mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have h := hb y
  rw [sq_norm_add_mul_I] at h
  simpa [div_eq_mul_inv] using h

/-- **Shifting a vertical line of integration**: for `F` analytic on the closed strip `c₁ ≤ Re w ≤ c₂` (`0 < c₁`)
with `|F(w)| ≤ C/|w|²` there, `∫ F(c₁ + iy) dy = ∫ F(c₂ + iy) dy`. -/
theorem integral_vertical_eq {F : ℂ → ℂ} {c₁ c₂ C : ℝ} (hc : c₁ ≤ c₂) (h0 : 0 < c₁) (hC : 0 ≤ C)
    (hF : DifferentiableOn ℂ F {w | c₁ ≤ w.re ∧ w.re ≤ c₂})
    (hb : ∀ w : ℂ, c₁ ≤ w.re → w.re ≤ c₂ → ‖F w‖ ≤ C / ‖w‖ ^ 2) :
    ∫ y : ℝ, F (c₁ + y * I) = ∫ y : ℝ, F (c₂ + y * I) := by
  have hcont : ∀ c, c₁ ≤ c → c ≤ c₂ → Continuous fun y : ℝ => F (c + y * I) := fun c h1 h2 => by
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ((hF.continuousOn).comp_continuous (by fun_prop) fun y' => by simp [h1, h2]).continuousAt
  have hint : ∀ c, c₁ ≤ c → c ≤ c₂ → Integrable fun y : ℝ => F (c + y * I) := fun c h1 h2 =>
    integrable_vertical_of_bound (h0.trans_le h1) (hcont c h1 h2) fun y => hb _ (by simpa using h1) (by simpa using h2)
  -- the rectangle `[c₁, c₂] × [-T, T]`
  have hrect : ∀ T : ℝ,
      (∫ x : ℝ in c₁..c₂, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in c₁..c₂, F (x + (T : ℂ) * I)) +
        I • (∫ y : ℝ in (-T)..T, F (c₂ + y * I)) - I • (∫ y : ℝ in (-T)..T, F (c₁ + y * I)) = 0 := by
    intro T
    refine integral_boundary_rect_eq_zero_of_differentiableOn F ⟨c₁, -T⟩ ⟨c₂, T⟩ (hF.mono fun w hw => ?_)
    obtain ⟨hre, -⟩ := hw
    have hre' : w.re ∈ [[c₁, c₂]] := hre
    rw [uIcc_of_le hc] at hre'
    exact ⟨hre'.1, hre'.2⟩
  -- the horizontal sides vanish
  have hbd : ∀ y : ℝ, y ≠ 0 → ‖∫ x : ℝ in c₁..c₂, F (x + (y : ℂ) * I)‖ ≤ C / y ^ 2 * |c₂ - c₁| := by
    intro y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hc] at hx
    refine (hb _ (by simpa using hx.1.le) (by simpa using hx.2)).trans ?_
    have him : |y| ≤ ‖(x : ℂ) + (y : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm ((x : ℂ) + (y : ℂ) * I)
      simpa using this
    have hsq : y ^ 2 ≤ ‖(x : ℂ) + (y : ℂ) * I‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) him 2
    exact div_le_div_of_nonneg_left hC (by positivity) hsq
  have hlim : Tendsto (fun T : ℝ => C / T ^ 2 * |c₂ - c₁|) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop (two_ne_zero)).inv_tendsto_atTop).const_mul C
    simpa [div_eq_mul_inv] using this.mul_const |c₂ - c₁|
  have hlim' : Tendsto (fun T : ℝ => C / (-T) ^ 2 * |c₂ - c₁|) atTop (𝓝 0) := by
    simpa only [neg_sq] using hlim
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in c₁..c₂, F (x + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with T hT using hbd T hT.ne'
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in c₁..c₂, F (x + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim'
    filter_upwards [eventually_gt_atTop 0] with T hT using hbd (-T) (neg_ne_zero.2 hT.ne')
  have hv : ∀ c, c₁ ≤ c → c ≤ c₂ → Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, F (c + y * I)) atTop
      (𝓝 (∫ y : ℝ, F (c + y * I))) := fun c h1 h2 =>
    intervalIntegral_tendsto_integral (hint c h1 h2) tendsto_neg_atTop_atBot tendsto_id
  have hlimit := ((hbot.sub htop).add ((hv c₂ hc le_rfl).const_smul I)).sub ((hv c₁ le_rfl hc).const_smul I)
  have hzero := tendsto_nhds_unique hlimit (tendsto_const_nhds.congr fun T => (hrect T).symm)
  rw [sub_zero, zero_add, ← smul_sub, smul_eq_mul, mul_eq_zero, sub_eq_zero] at hzero
  rcases hzero with h | h
  · exact absurd h I_ne_zero
  · exact h.symm

lemma inv_mem_diskC {R : ℝ} {w : ℂ} (hw : 1 / R < w.re) : w⁻¹ ∈ diskC R := by
  show 1 / R < ((w⁻¹)⁻¹).re
  rwa [inv_inv]

lemma ne_zero_of_re_gt {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : 1 / R < w.re) : w ≠ 0 := by
  rintro rfl; simp at hw; linarith [one_div_pos.2 hR]

/-- The integrand `e^{xw} (f(w⁻¹) - a₀)/w` of `b₀`. -/
noncomputable def borelIntegrand (f : ℂ → ℂ) (a₀ : ℂ) (x : ℝ) (w : ℂ) : ℂ := cexp (x * w) * (f w⁻¹ - a₀) / w

/-- **The function `b₀`** of the proof of the Nevanlinna–Sokal theorem (Benedetti–Gurau–Keppler–Lettera,
eq. (B.3)) along the line `Re w = c`: `b₀(x) = a₀ + (1/2π) ∫ e^{x(c+iy)} (f((c+iy)⁻¹) - a₀)/(c+iy) dy`. -/
noncomputable def borelZero (f : ℂ → ℂ) (a₀ : ℂ) (x c : ℝ) : ℂ :=
  a₀ + ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, borelIntegrand f a₀ x (c + y * I)

variable {f : ℂ → ℂ} {R : ℝ} {a₀ : ℂ} {M : ℝ}

lemma isOpen_diskC (hR : 0 < R) : IsOpen (diskC R) := by
  have h : IsOpen ({z : ℂ | z ≠ 0} ∩ (fun z : ℂ => (z⁻¹).re) ⁻¹' Ioi (1 / R)) :=
    (continuous_re.comp_continuousOn continuousOn_inv₀).isOpen_inter_preimage isOpen_ne isOpen_Ioi
  convert h using 1
  ext z
  simp only [diskC, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi]
  constructor
  · intro hz
    refine ⟨fun h0 => ?_, hz⟩
    rw [h0] at hz; simp at hz; linarith [one_div_pos.2 hR]
  · exact fun h => h.2

lemma differentiableOn_borelIntegrand (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R)) (x : ℝ) :
    DifferentiableOn ℂ (borelIntegrand f a₀ x) {w | 1 / R < w.re} := by
  intro w hw
  have hw0 := ne_zero_of_re_gt hR hw
  have hfw : DifferentiableAt ℂ (fun w : ℂ => f w⁻¹) w :=
    (hf.differentiableAt ((isOpen_diskC hR).mem_nhds (inv_mem_diskC hw))).comp w (differentiableAt_inv hw0)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold borelIntegrand
  exact (((differentiableAt_const _).mul differentiableAt_id).cexp.mul (hfw.sub_const a₀)).div
    differentiableAt_id hw0

lemma norm_borelIntegrand_le (hR : 0 < R) (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (x : ℝ) {w : ℂ}
    (hw : 1 / R < w.re) : ‖borelIntegrand f a₀ x w‖ ≤ Real.exp (x * w.re) * M / ‖w‖ ^ 2 := by
  have hw0 := ne_zero_of_re_gt hR hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  unfold borelIntegrand
  rw [norm_div, norm_mul, Complex.norm_exp]
  have hre : (↑x * w).re = x * w.re := by simp
  rw [hre]
  have h1 := hM _ (inv_mem_diskC hw)
  rw [norm_inv] at h1
  calc Real.exp (x * w.re) * ‖f w⁻¹ - a₀‖ / ‖w‖ ≤ Real.exp (x * w.re) * (M * ‖w‖⁻¹) / ‖w‖ := by
        gcongr
    _ = Real.exp (x * w.re) * M / ‖w‖ ^ 2 := by field_simp

/-- **`b₀` does not depend on the line** `Re w = c`, `c > 1/R`. -/
theorem borelZero_indep (hR : 0 < R) (hf : DifferentiableOn ℂ f (diskC R))
    (hM : ∀ z ∈ diskC R, ‖f z - a₀‖ ≤ M * ‖z‖) (hM0 : 0 ≤ M) (x : ℝ) {c₁ c₂ : ℝ} (h1 : 1 / R < c₁)
    (h2 : 1 / R < c₂) : borelZero f a₀ x c₁ = borelZero f a₀ x c₂ := by
  wlog hle : c₁ ≤ c₂ generalizing c₁ c₂
  · exact (this h2 h1 (le_of_not_ge hle)).symm
  unfold borelZero
  congr 2
  have hR' : 0 < 1 / R := one_div_pos.2 hR
  refine integral_vertical_eq (C := Real.exp (|x| * c₂) * M) hle (hR'.trans h1) (by positivity)
    ((differentiableOn_borelIntegrand hR hf x).mono fun w hw => h1.trans_le hw.1) fun w hw1 hw2 => ?_
  refine (norm_borelIntegrand_le hR hM x (h1.trans_le hw1)).trans ?_
  have he : Real.exp (x * w.re) ≤ Real.exp (|x| * c₂) := Real.exp_le_exp.2 <| by
    calc x * w.re ≤ |x| * w.re := mul_le_mul_of_nonneg_right (le_abs_self x) (hR'.trans (h1.trans_le hw1)).le
      _ ≤ |x| * c₂ := mul_le_mul_of_nonneg_left hw2 (abs_nonneg x)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hM0) (by positivity)

end Lightlike.FieldTheory.Borel
