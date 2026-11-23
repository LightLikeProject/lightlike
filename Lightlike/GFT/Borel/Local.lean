import Lightlike.GFT.Borel.NormBound
import Mathlib.Analysis.Analytic.OfScalars

/-!
# The local Borel transform is analytic (task T-GF7-P3)

Serves task T-GF7-P3 (Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B,
eq. (B.7)): `SokalHyp.analyticOnNhd_borelLocal`, with the statement copied word for word from
the closed task `T-GF7-P3`. By the bound of `SokalHyp.norm_borelDeriv_le` the coefficients `b_m(x)/m!` are at most
`C (m+1) ρ^{-m-1}`, so the power series `ofScalars` of these coefficients has radius at least `ρ`, and
`borelLocal` is its sum at `t - x`.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat NNReal ENNReal

namespace Lightlike.FieldTheory.Borel

/-- **The local Borel transform `B_x` is analytic in the disk of radius `ρ` about `x`** (Benedetti–Gurau–Keppler–
Lettera, arXiv:2210.14776v2, Appendix B, eq. (B.7), p. 25): under the hypotheses of the Nevanlinna–Sokal theorem,
for `x > 0` and any line `Re w = c > 1/R`, `B_x(t) = ∑_m b_m(x) (t - x)^m/m!` is analytic for `|t - x| < ρ`.

Non-vacuous: `sokalHyp_const`. Serves task T-GF7-P3. -/
theorem SokalHyp.analyticOnNhd_borelLocal {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (borelLocal f a x c) (Metric.ball (x : ℂ) ρ) := by
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hR := h.R_pos
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  set A : ℝ := K * (ρ + 1 / (2 * c)) * Real.exp (c * x) with hA
  have hA0 : 0 ≤ A := by positivity
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => borelDeriv f a m x c / (m ! : ℂ)) with hp
  have key : ∀ n : ℕ, ‖p n‖ ≤ A * (n + 1) / ρ ^ (n + 1) := by
    intro n
    have hb := h.norm_borelDeriv_le hc n hx.le
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    simp only [hp, FormalMultilinearSeries.ofScalars_norm, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hfac]
    refine hb.trans (le_of_eq ?_)
    rw [Nat.factorial_succ]
    push_cast
    rw [hA]
    ring
  have hrad : ENNReal.ofReal ρ ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hrρ : (r : ℝ) < ρ := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).1 hr
      simpa using this
    have hq0 : 0 ≤ (r : ℝ) / ρ := by positivity
    have hq1 : (r : ℝ) / ρ < 1 := (div_lt_one hρ).2 hrρ
    have hs : Summable fun n : ℕ => ((n : ℝ) + 1) * ((r : ℝ) / ρ) ^ n := by
      have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (r : ℝ) / ρ)
        (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
      have h2 := summable_geometric_of_lt_one hq0 hq1
      simpa [add_mul] using h1.add h2
    refine p.le_radius_of_summable ?_
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left (A / ρ))
    calc ‖p n‖ * (r : ℝ) ^ n ≤ A * (n + 1) / ρ ^ (n + 1) * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (key n) (by positivity)
      _ = A / ρ * (((n : ℝ) + 1) * ((r : ℝ) / ρ) ^ n) := by
          rw [div_pow, pow_succ]
          field_simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simpa using hρ) hrad
  have hball := (p.hasFPowerSeriesOnBall hpos).mono (r' := ENNReal.ofReal ρ) (by simpa using hρ) hrad
  have heq : borelLocal f a x c = fun t => p.sum (t - x) := by
    funext t
    unfold borelLocal
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr fun m => ?_
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    ring
  rw [heq]
  intro t ht
  have hmem : t - x ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal ρ) := by
    rw [Metric.mem_ball] at ht
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 (by simpa [dist_eq_norm] using ht)
  have h1 : AnalyticAt ℂ p.sum (t - x) := hball.analyticAt_of_mem hmem
  exact h1.comp (f := fun t : ℂ => t - x) (analyticAt_id.sub analyticAt_const)

end Lightlike.FieldTheory.Borel
