import Lightlike.GFT.Borel.Taylor

/-!
# Gluing the local Borel transforms (supports task T-GF7-P4)

Supports `SokalHyp.exists_continuation` (task T-GF7-P4, Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776v2, Appendix B, proof of Theorem 1): the Borel transform `borelT` is analytic on `|t| < ρ`, and the
local transforms `B_x` agree with it, and with each other, on the overlaps of their disks (identity theorem,
using `SokalHyp.borelLocal_real` on the real axis).
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

/-- The Borel transform is analytic on the disk `|t| < ρ`. -/
lemma SokalHyp.analyticOnNhd_borelT (h : SokalHyp f a R K ρ) :
    AnalyticOnNhd ℂ (borelT a) (Metric.ball (0 : ℂ) ρ) := by
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => a m / (m ! : ℂ)) with hp
  have key : ∀ n : ℕ, ‖p n‖ ≤ K / ρ ^ n := by
    intro n
    have hb := h.norm_coeff_le n
    have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    simp only [hp, FormalMultilinearSeries.ofScalars_norm, norm_div, Complex.norm_natCast]
    rw [div_le_iff₀ hfac]
    refine hb.trans (le_of_eq ?_)
    ring
  have hrad : ENNReal.ofReal ρ ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hrρ : (r : ℝ) < ρ := by
      have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).1 hr
      simpa using this
    have hq0 : 0 ≤ (r : ℝ) / ρ := by positivity
    have hq1 : (r : ℝ) / ρ < 1 := (div_lt_one hρ).2 hrρ
    have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left K
    refine p.le_radius_of_summable ?_
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    calc ‖p n‖ * (r : ℝ) ^ n ≤ K / ρ ^ n * (r : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (key n) (by positivity)
      _ = K * ((r : ℝ) / ρ) ^ n := by
          rw [div_pow]
          field_simp
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simpa using hρ) hrad
  have hball := (p.hasFPowerSeriesOnBall hpos).mono (r' := ENNReal.ofReal ρ) (by simpa using hρ) hrad
  have heq : borelT a = fun t => p.sum t := by
    funext t
    unfold borelT
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr fun m => ?_
    simp only [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
    ring
  rw [heq]
  intro t ht
  have hmem : t - 0 ∈ Metric.eball (0 : ℂ) (ENNReal.ofReal ρ) := by
    rw [Metric.mem_ball] at ht
    rw [Metric.mem_eball, sub_zero, edist_zero_right, ← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 (by simpa [dist_eq_norm] using ht)
  rw [sub_zero] at hmem
  exact hball.analyticAt_of_mem hmem

/-- Two functions analytic on two disks that agree on real points near a real point of the overlap agree on the
whole overlap (identity theorem). -/
lemma eqOn_ball_inter_of_real {F G : ℂ → ℂ} {z z' : ℂ} {r r' : ℝ} {s : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball z r)) (hG : AnalyticOnNhd ℂ G (Metric.ball z' r'))
    (hs : (s : ℂ) ∈ Metric.ball z r ∩ Metric.ball z' r') (hev : ∀ᶠ u : ℝ in 𝓝 s, F u = G u) :
    EqOn F G (Metric.ball z r ∩ Metric.ball z' r') := by
  refine (hF.mono inter_subset_left).eqOn_of_preconnected_of_frequently_eq (hG.mono inter_subset_right)
    ((convex_ball z r).inter (convex_ball z' r')).isPreconnected hs ?_
  have h1 : ∃ᶠ u : ℝ in 𝓝[≠] s, F u = G u := (hev.filter_mono nhdsWithin_le_nhds).frequently
  have ht : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[≠] s) (𝓝[≠] (s : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto s).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun u hu => Set.mem_compl_singleton_iff.2
        fun h => hu (Complex.ofReal_injective h)⟩
  exact ht.frequently h1

/-- On the overlap of the disks `|t| < ρ` and `|t - x| < ρ`, `borelT` equals the local transform `B_x`. -/
lemma SokalHyp.borelT_eq_borelLocal (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x : ℝ} (hx : 0 < x)
    {t : ℂ} (ht0 : ‖t‖ < ρ) (htx : ‖t - x‖ < ρ) : borelT a t = borelLocal f a x c t := by
  have hρ := h.ρ_pos
  have hx2 : x < 2 * ρ := by
    have : ‖(x : ℂ)‖ ≤ ‖t‖ + ‖t - x‖ := by
      calc ‖(x : ℂ)‖ = ‖t - (t - x)‖ := by ring_nf
        _ ≤ ‖t‖ + ‖t - x‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hx.le] at this
    linarith
  have hs : ((x / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ ∩ Metric.ball (x : ℂ) ρ := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      linarith
  have hev : ∀ᶠ u : ℝ in 𝓝 (x / 2), borelT a u = borelLocal f a x c u := by
    filter_upwards [Ioo_mem_nhds (a := 0) (b := ρ) (show (0 : ℝ) < x / 2 by positivity) (by linarith),
      Ioo_mem_nhds (a := x - ρ) (b := x + ρ) (by linarith) (by linarith)] with u hu hu'
    rw [h.borelLocal_real hc hx hu.1 (abs_sub_lt_iff.2 ⟨by linarith [hu'.2], by linarith [hu'.1]⟩),
      borelDeriv_zero, ← h.borelZero_eq_borelT hu.1 hu.2 hc]
  exact eqOn_ball_inter_of_real h.analyticOnNhd_borelT (h.analyticOnNhd_borelLocal hc hx) hs hev
    ⟨by rwa [mem_ball_zero_iff], by rwa [Metric.mem_ball, dist_eq_norm]⟩

/-- On the overlap of the disks about `x` and `x'`, the local transforms agree. -/
lemma SokalHyp.borelLocal_eq_borelLocal (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x x' : ℝ}
    (hx : 0 < x) (hx' : 0 < x') {t : ℂ} (htx : ‖t - x‖ < ρ) (htx' : ‖t - x'‖ < ρ) :
    borelLocal f a x c t = borelLocal f a x' c t := by
  have hρ := h.ρ_pos
  have hxx : |x - x'| < 2 * ρ := by
    have : ‖((x - x' : ℝ) : ℂ)‖ ≤ ‖t - x'‖ + ‖t - x‖ := by
      calc ‖((x - x' : ℝ) : ℂ)‖ = ‖(t - x') - (t - x)‖ := by push_cast; ring_nf
        _ ≤ ‖t - x'‖ + ‖t - x‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  have hd := abs_lt.1 hxx
  have hs : (((x + x') / 2 : ℝ) : ℂ) ∈ Metric.ball (x : ℂ) ρ ∩ Metric.ball (x' : ℂ) ρ := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith
    · rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_lt]
      constructor <;> linarith
  have hev : ∀ᶠ u : ℝ in 𝓝 ((x + x') / 2), borelLocal f a x c u = borelLocal f a x' c u := by
    filter_upwards [Ioo_mem_nhds (a := 0) (b := (x + x') / 2 + 1) (by positivity) (by linarith),
      Ioo_mem_nhds (a := x - ρ) (b := x + ρ) (by linarith) (by linarith),
      Ioo_mem_nhds (a := x' - ρ) (b := x' + ρ) (by linarith) (by linarith)] with u hu hu' hu''
    rw [h.borelLocal_real hc hx hu.1 (abs_sub_lt_iff.2 ⟨by linarith [hu'.2], by linarith [hu'.1]⟩),
      h.borelLocal_real hc hx' hu.1 (abs_sub_lt_iff.2 ⟨by linarith [hu''.2], by linarith [hu''.1]⟩)]
  exact eqOn_ball_inter_of_real (h.analyticOnNhd_borelLocal hc hx) (h.analyticOnNhd_borelLocal hc hx') hs hev
    ⟨by rwa [Metric.mem_ball, dist_eq_norm], by rwa [Metric.mem_ball, dist_eq_norm]⟩

end Lightlike.FieldTheory.Borel
