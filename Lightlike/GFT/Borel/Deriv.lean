import Lightlike.FieldTheory.Borel.Strip

/-!
# The functions `b_m` are the derivatives of `b_0` (task T-GF7-P1)

Serves task T-GF7-P1 (Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B,
eq. (B.6)): `SokalHyp.hasDerivAt_borelDeriv`, with the statement copied word for word from
the closed task `T-GF7-P1`. The proof writes `R_{m+1}(z) = a_{m+1} z^{m+1} + R_{m+2}(z)`, evaluates the
first part by Hankel's formula (`hankel_vertical_y`, `k = 1`) and differentiates the second under the
integral sign.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

/-- On the line `Re w = c > 1/R`: `|w^m R_{m+2}(w⁻¹)| ≤ K (m+2)! ρ^{-m-2} / |w|²`. -/
lemma SokalHyp.norm_pow_mul_taylorRem_le (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) (m : ℕ) (y : ℝ) :
    ‖((c : ℂ) + y * I) ^ m * taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹‖ ≤
      K * (m + 2) ! / ρ ^ (m + 2) / ‖(c : ℂ) + y * I‖ ^ 2 := by
  have hwre : 1 / R < ((c : ℂ) + y * I).re := by simpa using hc
  have hw0 := ne_zero_of_re_gt h.R_pos hwre
  have hr := h.rem (m + 2) _ (inv_mem_diskC hwre)
  set w : ℂ := (c : ℂ) + y * I with hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  rw [norm_inv] at hr
  unfold taylorRem
  rw [norm_mul, norm_pow]
  calc ‖w‖ ^ m * ‖f w⁻¹ - ∑ k ∈ range (m + 2), a k * w⁻¹ ^ k‖
      ≤ ‖w‖ ^ m * (K * (m + 2) ! / ρ ^ (m + 2) * ‖w‖⁻¹ ^ (m + 2)) := by gcongr
    _ = _ := by rw [inv_pow]; field_simp; ring

/-- The remainder is continuous along the line. -/
lemma SokalHyp.continuous_taylorRem_line (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) (q : ℕ) :
    Continuous fun y : ℝ => taylorRem f a q ((c : ℂ) + y * I)⁻¹ := by
  have hwre : ∀ y : ℝ, 1 / R < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hw0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_gt h.R_pos (hwre y)
  have hcont : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
  have hi : Continuous fun y : ℝ => ((c : ℂ) + y * I)⁻¹ := hcont.inv₀ hw0
  unfold taylorRem
  refine Continuous.sub ?_ (continuous_finsetSum _ fun k _ => continuous_const.mul (hi.pow k))
  exact (h.analytic.continuousOn).comp_continuous hi fun y => inv_mem_diskC (hwre y)

/-- The integrand of the derivative: `e^{xw} w^m R_{m+2}(w⁻¹)`. -/
lemma SokalHyp.integrable_deriv_integrand (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) (m : ℕ) (x : ℝ) :
    Integrable fun y : ℝ => cexp (x * ((c : ℂ) + y * I)) * (((c : ℂ) + y * I) ^ m *
      taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹) := by
  have hc0 : 0 < c := (one_div_pos.2 h.R_pos).trans hc
  refine integrable_vertical_of_bound
    (F := fun w => cexp (x * w) * (w ^ m * taylorRem f a (m + 2) w⁻¹))
    (C := Real.exp (x * c) * (K * (m + 2) ! / ρ ^ (m + 2))) hc0 ?_ fun y => ?_
  · exact (by fun_prop : Continuous fun y : ℝ => cexp (x * ((c : ℂ) + y * I))).mul
      ((by fun_prop : Continuous fun y : ℝ => ((c : ℂ) + y * I) ^ m).mul (h.continuous_taylorRem_line hc _))
  · rw [norm_mul, norm_cexp_mul_vertical, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (h.norm_pow_mul_taylorRem_le hc m y) (Real.exp_pos _).le

/-- **The functions `b_m` are the successive derivatives of `b_0`** (Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776v2, Appendix B, eq. (B.6), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem,
along any line `Re w = c > 1/R`, `b_m'(x) = b_{m+1}(x)` for `x > 0`.

The source defines `b_m(x) = d^m b_0(x)/dx^m` and derives the formula (B.6); here `b_m` is defined by the formula
(`borelDeriv`, with `b_0 = borelZero` by `borelDeriv_zero`) and the statement is that these are the derivatives
(kind: representation). Non-vacuous: `sokalHyp_const`. Serves task T-GF7-P1. -/
theorem SokalHyp.hasDerivAt_borelDeriv {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => borelDeriv f a m x c) (borelDeriv f a (m + 1) x c) x := by
  have hR := h.R_pos
  have hρ := h.ρ_pos
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  have hwre : ∀ y : ℝ, 1 / R < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hw0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_gt hR (hwre y)
  have hcont : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
  -- the integrand `H` of the remainder part
  set H : ℝ → ℝ → ℂ := fun x y => cexp (x * ((c : ℂ) + y * I)) * (((c : ℂ) + y * I) ^ m *
      taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹) / ((c : ℂ) + y * I) with hH
  have hHint : ∀ x : ℝ, Integrable (H x) := by
    intro x
    refine integrable_vertical_of_bound
      (F := fun w => cexp (x * w) * (w ^ m * taylorRem f a (m + 2) w⁻¹) / w)
      (C := Real.exp (x * c) * (K * (m + 2) ! / ρ ^ (m + 2)) / c) hc0 ?_ fun y => ?_
    · exact ((by fun_prop : Continuous fun y : ℝ => cexp (x * ((c : ℂ) + y * I))).mul
        ((by fun_prop : Continuous fun y : ℝ => ((c : ℂ) + y * I) ^ m).mul
          (h.continuous_taylorRem_line hc _))).div hcont hw0
    · have hn : 0 < ‖(c : ℂ) + y * I‖ := norm_pos_iff.2 (hw0 y)
      have hcn : c ≤ ‖(c : ℂ) + y * I‖ := by
        have := Complex.abs_re_le_norm ((c : ℂ) + y * I)
        simpa [abs_of_nonneg hc0.le] using this
      rw [norm_div, norm_mul, norm_cexp_mul_vertical]
      have hb := h.norm_pow_mul_taylorRem_le hc m y
      have hK := h.K_nonneg
      calc Real.exp (x * c) * ‖((c : ℂ) + y * I) ^ m * taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹‖ /
            ‖(c : ℂ) + y * I‖ ≤ Real.exp (x * c) * (K * (m + 2) ! / ρ ^ (m + 2) / ‖(c : ℂ) + y * I‖ ^ 2) /
            ‖(c : ℂ) + y * I‖ := by gcongr
        _ ≤ Real.exp (x * c) * (K * (m + 2) ! / ρ ^ (m + 2) / ‖(c : ℂ) + y * I‖ ^ 2) / c := by
            gcongr
        _ = _ := by ring
  -- decomposition of `b_m`
  have hdec : ∀ x : ℝ, 0 < x → borelDeriv f a m x c =
      a m + a (m + 1) * x + ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, H x y := by
    intro x hx'
    have hT : Integrable fun y : ℝ => cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (1 + 1) := by
      refine integrable_vertical_of_bound
        (F := fun w => cexp (x * w) / w ^ (1 + 1)) (C := Real.exp (x * c)) hc0
        ((by fun_prop : Continuous fun y : ℝ => cexp (x * ((c : ℂ) + y * I))).div (hcont.pow _)
          fun y => pow_ne_zero _ (hw0 y)) fun y => ?_
      rw [norm_div, norm_pow, norm_cexp_mul_vertical]
    have hpt : ∀ y : ℝ, cexp (x * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) *
        taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹ =
        a (m + 1) * (cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (1 + 1)) + H x y := by
      intro y
      have hw := hw0 y
      have e : taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹ =
          a (m + 1) * ((c : ℂ) + y * I)⁻¹ ^ (m + 1) + taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹ := by
        unfold taylorRem
        rw [show m + 2 = (m + 1) + 1 from rfl, sum_range_succ _ (m + 1)]; ring
      rw [e, zpow_sub₀ hw, zpow_natCast, zpow_one, hH]
      simp only [inv_pow]
      field_simp
      ring
    unfold borelDeriv
    simp_rw [hpt]
    rw [integral_add (hT.const_mul _) (hHint x), integral_const_mul, hankel_vertical_y (le_refl 1) hx' hc0]
    push_cast
    field_simp
    ring
  -- the derivative of the remainder part
  set F' : ℝ → ℝ → ℂ := fun x y => cexp (x * ((c : ℂ) + y * I)) * (((c : ℂ) + y * I) ^ m *
      taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹) with hF'
  have hbd : ∀ y : ℝ, ∀ x' ∈ Metric.ball x (1 : ℝ),
      ‖F' x' y‖ ≤ Real.exp ((x + 1) * c) * (K * (m + 2) ! / ρ ^ (m + 2)) * (c ^ 2 + y ^ 2)⁻¹ := by
    intro y x' hx'
    have hx1 : x' ≤ x + 1 := by
      have := Metric.mem_ball.1 hx'
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.2]
    simp only [hF']
    rw [norm_mul, norm_cexp_mul_vertical]
    have hb := h.norm_pow_mul_taylorRem_le hc m y
    rw [sq_norm_add_mul_I, div_eq_mul_inv] at hb
    have hK := h.K_nonneg
    calc Real.exp (x' * c) * _ ≤ Real.exp ((x + 1) * c) * (K * (m + 2) ! / ρ ^ (m + 2) * (c ^ 2 + y ^ 2)⁻¹) := by
          gcongr
      _ = _ := by ring
  have hder : ∀ y : ℝ, ∀ x' ∈ Metric.ball x (1 : ℝ), HasDerivAt (fun x : ℝ => H x y) (F' x' y) x' := by
    intro y x' _
    have hw := hw0 y
    have h1 : HasDerivAt (fun x : ℝ => cexp (x * ((c : ℂ) + y * I)))
        (cexp (x' * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I)) x' := by
      have := ((hasDerivAt_id x').ofReal_comp.mul_const ((c : ℂ) + y * I)).cexp
      simpa using this
    have h2 := (h1.mul_const ((((c : ℂ) + y * I) ^ m *
      taylorRem f a (m + 2) ((c : ℂ) + y * I)⁻¹))).div_const ((c : ℂ) + y * I)
    refine h2.congr_deriv ?_
    simp only [hF']
    field_simp
  obtain ⟨_, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ) (x₀ := x)
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos) (F := H) (F' := F')
    (Filter.Eventually.of_forall fun x => (hHint x).aestronglyMeasurable) (hHint x)
    (h.integrable_deriv_integrand hc m x).aestronglyMeasurable
    (Filter.Eventually.of_forall hbd) ((integrable_inv_sq_add hc0).const_mul _)
    (Filter.Eventually.of_forall hder)
  have hfun : (fun x : ℝ => borelDeriv f a m x c) =ᶠ[𝓝 x]
      fun x : ℝ => a m + a (m + 1) * x + ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, H x y := by
    filter_upwards [Ioi_mem_nhds hx] with x' hx' using hdec x' hx'
  have hlin : HasDerivAt (fun x : ℝ => a m + a (m + 1) * (x : ℂ)) (a (m + 1)) x := by
    have := ((hasDerivAt_id x).ofReal_comp.const_mul (a (m + 1))).const_add (a m)
    simpa using this
  have hall := (hlin.add (hD.const_mul (((2 * π : ℝ) : ℂ)⁻¹)))
  refine (hall.congr_of_eventuallyEq hfun).congr_deriv ?_
  unfold borelDeriv
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hF']
  push_cast
  rw [show ((m : ℤ) + 1 - 1) = (m : ℤ) by ring, zpow_natCast]
  ring

end Lightlike.FieldTheory.Borel
