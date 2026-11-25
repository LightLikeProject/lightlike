import Mathlib

/-!
# Laplace transforms on the strip `-2π ≤ Re w ≤ 0`

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

For `φ ∈ L¹(ℝ)` such that `k ↦ φ k * e^{-2π k}` is also integrable, the Laplace transform
`laplace φ w = ∫ φ(k) e^{w k} dk` is continuous on the closed strip `-2π ≤ Re w ≤ 0` and
holomorphic in its interior. This is the analytic input for the KMS condition of the modular group
in the momentum model (`Δ^{iz} = e^{-2π i z k}`, so `z = t - i s` with `0 ≤ s ≤ 1` is `Re w = -2π s`).

## Main results

* `laplace_continuousOn` — continuity on the closed strip.
* `laplace_differentiableAt` — holomorphy at every point of the open strip.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

namespace Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-- The Laplace transform `∫ φ(k) e^{w k} dk` of a function `φ : ℝ → ℂ`. -/
noncomputable def laplace (φ : ℝ → ℂ) (w : ℂ) : ℂ := ∫ k : ℝ, φ k * cexp (w * k)

/-- `e^{ρ k} ≤ 1 + e^{-2π k}` for `-2π ≤ ρ ≤ 0`. -/
lemma exp_le_one_add {ρ k : ℝ} (h0 : ρ ≤ 0) (h1 : -(2 * π) ≤ ρ) :
    Real.exp (ρ * k) ≤ 1 + Real.exp (-(2 * π) * k) := by
  rcases le_or_gt 0 k with hk | hk
  · have : Real.exp (ρ * k) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have := Real.exp_pos (-(2 * π) * k)
    linarith
  · have : Real.exp (ρ * k) ≤ Real.exp (-(2 * π) * k) := by
      apply Real.exp_le_exp.mpr; nlinarith
    linarith [Real.exp_pos (ρ * k)]

/-- `|k| e^{ρ k} ≤ a⁻¹ (e^{(ρ+a)k} + e^{(ρ-a)k})` for `a > 0`. -/
lemma abs_mul_exp_le {a ρ k : ℝ} (ha : 0 < a) :
    |k| * Real.exp (ρ * k) ≤ (1 / a) * (Real.exp ((ρ + a) * k) + Real.exp ((ρ - a) * k)) := by
  have h1 : a * |k| + 1 ≤ Real.exp (a * |k|) := by
    simpa [add_comm] using Real.add_one_le_exp (a * |k|)
  have h2 : Real.exp (a * |k|) ≤ Real.exp (a * k) + Real.exp (-(a * k)) := by
    rcases le_or_gt 0 k with hk | hk
    · rw [abs_of_nonneg hk]; linarith [Real.exp_pos (-(a * k))]
    · rw [abs_of_neg hk]
      have : a * -k = -(a * k) := by ring
      rw [this]; linarith [Real.exp_pos (a * k)]
  have h3 : |k| ≤ (1 / a) * (Real.exp (a * k) + Real.exp (-(a * k))) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ha]
    nlinarith [abs_nonneg k]
  calc |k| * Real.exp (ρ * k)
      ≤ (1 / a) * (Real.exp (a * k) + Real.exp (-(a * k))) * Real.exp (ρ * k) := by
        gcongr
    _ = (1 / a) * (Real.exp ((ρ + a) * k) + Real.exp ((ρ - a) * k)) := by
        have e1 : Real.exp ((ρ + a) * k) = Real.exp (a * k) * Real.exp (ρ * k) := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp ((ρ - a) * k) = Real.exp (-(a * k)) * Real.exp (ρ * k) := by
          rw [← Real.exp_add]; ring_nf
        rw [e1, e2]; ring

variable {φ : ℝ → ℂ}

/-- The dominating function `‖φ‖ (1 + e^{-2π k})` is integrable. -/
lemma integrable_bound (h0 : Integrable φ)
    (h1 : Integrable (fun k : ℝ => φ k * (Real.exp (-(2 * π) * k) : ℂ))) :
    Integrable (fun k : ℝ => ‖φ k‖ * (1 + Real.exp (-(2 * π) * k))) := by
  have := h0.norm.add h1.norm
  refine this.congr (Filter.Eventually.of_forall fun k => ?_)
  simp only [Pi.add_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  ring

/-- `‖e^{w k}‖ = e^{Re w · k}`. -/
lemma norm_cexp_mul (w : ℂ) (k : ℝ) : ‖cexp (w * k)‖ = Real.exp (w.re * k) := by
  rw [Complex.norm_exp]; simp

/-- **Continuity of the Laplace transform on the closed strip** `-2π ≤ Re w ≤ 0`. -/
theorem laplace_continuousOn (h0 : Integrable φ)
    (h1 : Integrable (fun k : ℝ => φ k * (Real.exp (-(2 * π) * k) : ℂ))) :
    ContinuousOn (laplace φ) {w : ℂ | -(2 * π) ≤ w.re ∧ w.re ≤ 0} := by
  unfold laplace
  refine continuousOn_of_dominated (bound := fun k : ℝ => ‖φ k‖ * (1 + Real.exp (-(2 * π) * k)))
    (fun w _ => ?_) (fun w hw => Filter.Eventually.of_forall fun k => ?_)
    (integrable_bound h0 h1) (Filter.Eventually.of_forall fun k => ?_)
  · exact h0.aestronglyMeasurable.mul (by fun_prop)
  · rw [norm_mul, norm_cexp_mul]
    exact mul_le_mul_of_nonneg_left (exp_le_one_add hw.2 hw.1) (norm_nonneg _)
  · exact continuousOn_const.mul (by fun_prop)

/-- **Holomorphy of the Laplace transform in the open strip** `-2π < Re w < 0`. -/
theorem laplace_differentiableAt (h0 : Integrable φ)
    (h1 : Integrable (fun k : ℝ => φ k * (Real.exp (-(2 * π) * k) : ℂ)))
    {w₀ : ℂ} (hw0 : -(2 * π) < w₀.re) (hw1 : w₀.re < 0) :
    DifferentiableAt ℂ (laplace φ) w₀ := by
  set a : ℝ := min (-w₀.re) (w₀.re + 2 * π) / 2 with ha_def
  have ha : 0 < a := by
    have : 0 < min (-w₀.re) (w₀.re + 2 * π) := lt_min (by linarith) (by linarith)
    positivity
  have ha1 : 2 * a ≤ -w₀.re := by
    have := min_le_left (-w₀.re) (w₀.re + 2 * π); rw [ha_def]; linarith
  have ha2 : 2 * a ≤ w₀.re + 2 * π := by
    have := min_le_right (-w₀.re) (w₀.re + 2 * π); rw [ha_def]; linarith
  set B : ℝ → ℝ := fun k => (2 / a) * (‖φ k‖ * (1 + Real.exp (-(2 * π) * k))) with hB
  have hBint : Integrable B := (integrable_bound h0 h1).const_mul _
  have hs : Metric.ball w₀ a ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ ha
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (fun k : ℝ => φ k * cexp (w * k)) volume :=
    fun w => h0.aestronglyMeasurable.mul (by fun_prop)
  have hint : Integrable (fun k : ℝ => φ k * cexp (w₀ * k)) := by
    refine (integrable_bound h0 h1).mono' (hmeas w₀) (Filter.Eventually.of_forall fun k => ?_)
    rw [norm_mul, norm_cexp_mul]
    exact mul_le_mul_of_nonneg_left (exp_le_one_add hw1.le hw0.le) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := volume)
    (F := fun (w : ℂ) (k : ℝ) => φ k * cexp (w * k))
    (F' := fun (w : ℂ) (k : ℝ) => φ k * ((k : ℂ) * cexp (w * k))) (bound := B) hs
    (Filter.Eventually.of_forall hmeas) hint
    (h0.aestronglyMeasurable.mul (by fun_prop)) ?_ hBint ?_
  · exact key.2.differentiableAt
  · refine Filter.Eventually.of_forall fun k w hw => ?_
    have hre : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
      simpa using Complex.abs_re_le_norm (w - w₀)
    have hd : ‖w - w₀‖ < a := by simpa [dist_eq_norm] using hw
    have hl := abs_le.mp (hre.trans hd.le)
    have hmono1 : Real.exp (w.re * k) ≤ Real.exp ((w.re + a) * k) + Real.exp ((w.re - a) * k) := by
      have := Real.exp_pos ((w.re + a) * k)
      have := Real.exp_pos ((w.re - a) * k)
      rcases le_or_gt 0 k with hk | hk
      · have : Real.exp (w.re * k) ≤ Real.exp ((w.re + a) * k) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
      · have : Real.exp (w.re * k) ≤ Real.exp ((w.re - a) * k) :=
          Real.exp_le_exp.mpr (by nlinarith)
        linarith
    have e1 : Real.exp ((w.re + a) * k) ≤ 1 + Real.exp (-(2 * π) * k) :=
      exp_le_one_add (by linarith) (by linarith)
    have e2 : Real.exp ((w.re - a) * k) ≤ 1 + Real.exp (-(2 * π) * k) :=
      exp_le_one_add (by linarith) (by linarith)
    have hk := abs_mul_exp_le (a := a) (ρ := w.re) (k := k) ha
    simp only [hB, norm_mul, Complex.norm_real, norm_cexp_mul, Real.norm_eq_abs]
    calc ‖φ k‖ * (|k| * Real.exp (w.re * k))
        ≤ ‖φ k‖ * ((1 / a) * (Real.exp ((w.re + a) * k) + Real.exp ((w.re - a) * k))) :=
          mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ ≤ ‖φ k‖ * ((1 / a) * (2 * (1 + Real.exp (-(2 * π) * k)))) := by
          gcongr; linarith
      _ = 2 / a * (‖φ k‖ * (1 + Real.exp (-(2 * π) * k))) := by ring
  · refine Filter.Eventually.of_forall fun k w _ => ?_
    have h := ((hasDerivAt_id w).mul_const (k : ℂ)).cexp
    have h2 := h.const_mul (φ k)
    refine h2.congr_deriv ?_
    simp only [id]; ring

end Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.abs_mul_exp_le := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.abs_mul_exp_le
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.exp_le_one_add := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.exp_le_one_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.integrable_bound := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.integrable_bound
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.laplace := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.laplace
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.laplace_continuousOn := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.laplace_continuousOn
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.laplace_differentiableAt := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.laplace_differentiableAt
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_054.norm_cexp_mul := _root_.Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.norm_cexp_mul
