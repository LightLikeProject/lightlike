import Lightlike.GFT.Borel.Continuation

/-!
# The Borel transform continues to the strip (task T-GF7-P4)

`SokalHyp.exists_continuation` (task T-GF7-P4, Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera,
arXiv:2210.14776v2, Theorem 1 second item and Appendix B): the local transforms `B_x` are glued into one function
`B(t) = borelT a t` for `|t| < ρ`, `B(t) = B_{Re t}(t)` otherwise, which is analytic on the strip, equals `b_0` on
`(0, ∞)`, and satisfies the exponential bound on every smaller strip (the line `Re w = c` is chosen depending on the
centre `x`, which is allowed because `B_x` does not depend on `c`).
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

/-- `b_0` does not depend on the line, in the form needed for the Nevanlinna–Sokal hypotheses. -/
lemma SokalHyp.borelZero_indep' (h : SokalHyp f a R K ρ) (x : ℝ) {c₁ c₂ : ℝ} (h1 : 1 / R < c₁)
    (h2 : 1 / R < c₂) : borelZero f (a 0) x c₁ = borelZero f (a 0) x c₂ := by
  have hR := h.R_pos
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hM : ∀ z ∈ diskC R, ‖f z - a 0‖ ≤ K * 1 ! / ρ ^ 1 * ‖z‖ := fun z hz => by simpa using h.rem 1 z hz
  have hM0 : 0 ≤ K * 1 ! / ρ ^ 1 := by positivity
  exact borelZero_indep hR h.analytic hM hM0 x h1 h2

/-- `B_x` does not depend on the line `Re w = c`. -/
lemma SokalHyp.borelLocal_indep (h : SokalHyp f a R K ρ) {c c' : ℝ} (hc : 1 / R < c) (hc' : 1 / R < c')
    {x : ℝ} (hx : 0 < x) {t : ℂ} (ht : ‖t - x‖ < ρ) : borelLocal f a x c t = borelLocal f a x c' t := by
  have hρ := h.ρ_pos
  have hs : (x : ℂ) ∈ Metric.ball (x : ℂ) ρ ∩ Metric.ball (x : ℂ) ρ := by
    simpa using hρ
  have hev : ∀ᶠ u : ℝ in 𝓝 x, borelLocal f a x c u = borelLocal f a x c' u := by
    filter_upwards [Ioo_mem_nhds (a := x / 2) (b := x + 1) (by linarith) (by linarith),
      Ioo_mem_nhds (a := x - ρ) (b := x + ρ) (by linarith) (by linarith)] with u hu hu'
    have hu0 : 0 < u := by linarith [hu.1]
    have hux : |u - x| < ρ := abs_sub_lt_iff.2 ⟨by linarith [hu'.2], by linarith [hu'.1]⟩
    rw [h.borelLocal_real hc hx hu0 hux, h.borelLocal_real hc' hx hu0 hux, borelDeriv_zero, borelDeriv_zero,
      h.borelZero_indep' u hc hc']
  exact eqOn_ball_inter_of_real (h.analyticOnNhd_borelLocal hc hx) (h.analyticOnNhd_borelLocal hc' hx) hs hev
    ⟨by rwa [Metric.mem_ball, dist_eq_norm], by rwa [Metric.mem_ball, dist_eq_norm]⟩

/-- A point of the disk about `x > 0` that is outside the disk about `0` has positive real part, and lies in the
disk about its own real part. -/
lemma re_pos_of_mem_ball {x ρ : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : ρ ≤ ‖s‖) (hsx : ‖s - x‖ < ρ) :
    0 < s.re ∧ ‖s - (s.re : ℂ)‖ < ρ := by
  have h1 : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h2 : ‖s - (x : ℂ)‖ ^ 2 = (s.re - x) ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h3 : ‖s - (s.re : ℂ)‖ ^ 2 = s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hn := norm_nonneg (s - (x : ℂ))
  have hn3 := norm_nonneg (s - (s.re : ℂ))
  refine ⟨?_, ?_⟩
  · by_contra hre
    have hre := not_lt.1 hre
    nlinarith
  · by_contra hge
    have hge := not_lt.1 hge
    nlinarith

/-- The glued function: `borelT` on `|t| < ρ`, the local transform about `Re t` (line `c`) elsewhere. -/
noncomputable def borelGlue (f : ℂ → ℂ) (a : ℕ → ℂ) (ρ c : ℝ) (t : ℂ) : ℂ :=
  if ‖t‖ < ρ then borelT a t else borelLocal f a t.re c t

/-- The glued function equals `B_x` on the whole disk about every `x > 0`. -/
lemma SokalHyp.borelGlue_eq_local (h : SokalHyp f a R K ρ) {c : ℝ} (hc : 1 / R < c) {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : ‖s - x‖ < ρ) : borelGlue f a ρ c s = borelLocal f a x c s := by
  unfold borelGlue
  by_cases h0 : ‖s‖ < ρ
  · simp only [h0, ↓reduceIte]; exact h.borelT_eq_borelLocal hc hx h0 hs
  · simp only [h0, ↓reduceIte]
    obtain ⟨hre, hd⟩ := re_pos_of_mem_ball hx (not_lt.1 h0) hs
    exact h.borelLocal_eq_borelLocal hc hre hx hd hs

/-- The bound on a point of a smaller strip, with the line chosen from the centre. -/
lemma SokalHyp.norm_borelGlue_le (h : SokalHyp f a R K ρ) {ρ' : ℝ} (hρ'0 : 0 < ρ') (hρ' : ρ' < ρ) {c0 : ℝ}
    (hc0 : 1 / R < c0) {t : ℂ} (ht : t ∈ sokalStrip ρ') :
    ‖borelGlue f a ρ c0 t‖ ≤ K * (ρ + R / 2) * Real.exp 1 * Real.exp (ρ' / R) / ρ *
      (∑' m : ℕ, ((m : ℝ) + 1) * (ρ' / ρ) ^ m) * Real.exp (‖t‖ / R) := by
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hR := h.R_pos
  obtain ⟨x, hx0, hx⟩ := ht
  set δ := (ρ' - ‖t - x‖) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set x' : ℝ := x + δ with hx'
  have hx'0 : 0 < x' := by rw [hx']; linarith
  have htx' : ‖t - (x' : ℂ)‖ < ρ' := by
    have : t - (x' : ℂ) = (t - x) - (δ : ℂ) := by rw [hx']; push_cast; ring
    rw [this]
    calc ‖(t - x) - (δ : ℂ)‖ ≤ ‖t - x‖ + ‖(δ : ℂ)‖ := norm_sub_le _ _
      _ = ‖t - x‖ + δ := by rw [Complex.norm_real, Real.norm_of_nonneg hδ0.le]
      _ < ρ' := by rw [hδ]; linarith
  have hx'le : x' < ‖t‖ + ρ' := by
    have : ‖(x' : ℂ)‖ ≤ ‖t‖ + ‖t - x'‖ := by
      calc ‖(x' : ℂ)‖ = ‖t - (t - x')‖ := by ring_nf
        _ ≤ ‖t‖ + ‖t - x'‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hx'0.le] at this
    linarith
  set c : ℝ := 1 / R + 1 / (x' + 1) with hcdef
  have hc : 1 / R < c := by rw [hcdef]; have : 0 < 1 / (x' + 1) := by positivity
                            linarith
  have hc2 : 1 / (2 * c) ≤ R / 2 := by
    have hc1 : 1 / R ≤ c := hc.le
    have hcp : 0 < 1 / R := by positivity
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 1 ≤ R * c := by
      have := mul_le_mul_of_nonneg_left hc1 hR.le
      rwa [mul_one_div_cancel hR.ne'] at this
    linarith
  have hE : Real.exp (c * x') ≤ Real.exp 1 * Real.exp (ρ' / R) * Real.exp (‖t‖ / R) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : x' / (x' + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : c * x' = x' / R + x' / (x' + 1) := by rw [hcdef]; field_simp
    have h3 : x' / R ≤ (‖t‖ + ρ') / R := div_le_div_of_nonneg_right hx'le.le hR.le
    have h4 : (‖t‖ + ρ') / R = ρ' / R + ‖t‖ / R := by ring
    linarith
  have hq0 : 0 ≤ ρ' / ρ := by positivity
  have hq1 : ρ' / ρ < 1 := (div_lt_one hρ).2 hρ'
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1) * (ρ' / ρ) ^ n := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ' / ρ)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])
    have h2 := summable_geometric_of_lt_one hq0 hq1
    simpa [add_mul] using h1.add h2
  have hSn : 0 ≤ ∑' m : ℕ, ((m : ℝ) + 1) * (ρ' / ρ) ^ m := tsum_nonneg fun m => by positivity
  have hBt : borelGlue f a ρ c0 t = borelLocal f a x' c t := by
    have hm : ‖t - (x' : ℂ)‖ < ρ := htx'.trans hρ'
    rw [h.borelGlue_eq_local hc0 hx'0 hm]
    exact h.borelLocal_indep hc0 hc hx'0 hm
  rw [hBt]
  unfold borelLocal
  have hterm : ∀ m : ℕ, ‖borelDeriv f a m x' c * (t - x') ^ m / (m ! : ℂ)‖ ≤
      K * (ρ + 1 / (2 * c)) * Real.exp (c * x') / ρ * (((m : ℝ) + 1) * (ρ' / ρ) ^ m) := by
    intro m
    refine (h.norm_borelLocal_term_le hc hx'0.le m t).trans ?_
    have : ‖t - (x' : ℂ)‖ / ρ ≤ ρ' / ρ := div_le_div_of_nonneg_right htx'.le hρ.le
    have hpow : (‖t - (x' : ℂ)‖ / ρ) ^ m ≤ (ρ' / ρ) ^ m := pow_le_pow_left₀ (by positivity) this m
    have hA : 0 ≤ K * (ρ + 1 / (2 * c)) * Real.exp (c * x') / ρ := by
      have : 0 < c := lt_trans (by positivity) hc
      positivity
    gcongr
  have hsum := (hs.hasSum.mul_left (K * (ρ + 1 / (2 * c)) * Real.exp (c * x') / ρ))
  have h1 := tsum_of_norm_bounded hsum hterm
  refine h1.trans ?_
  have hcpos : 0 < c := lt_trans (by positivity) hc
  calc K * (ρ + 1 / (2 * c)) * Real.exp (c * x') / ρ * ∑' m : ℕ, ((m : ℝ) + 1) * (ρ' / ρ) ^ m
      ≤ K * (ρ + R / 2) * (Real.exp 1 * Real.exp (ρ' / R) * Real.exp (‖t‖ / R)) / ρ *
          ∑' m : ℕ, ((m : ℝ) + 1) * (ρ' / ρ) ^ m := by gcongr
    _ = _ := by ring

/-- **The Borel transform continues to the strip** (task T-GF7-P4); statement copied from
`Tasks/GF/T_GF7_P4.lean`. -/
theorem SokalHyp.exists_continuation {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) :
    ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧ (∀ t : ℂ, ‖t‖ < ρ → B t = borelT a t) ∧
      (∀ c : ℝ, 1 / R < c → ∀ x : ℝ, 0 < x → B x = borelZero f (a 0) x c) ∧
      ∀ ρ' : ℝ, ρ' < ρ → ∃ C : ℝ, ∀ t ∈ sokalStrip ρ', ‖B t‖ ≤ C * Real.exp (‖t‖ / R) := by
  have hρ := h.ρ_pos
  have hR := h.R_pos
  have hc0 : 1 / R < 1 / R + 1 := by linarith
  set c0 : ℝ := 1 / R + 1 with hc0def
  refine ⟨borelGlue f a ρ c0, ?_, ?_, ?_, ?_⟩
  · intro t ⟨x, hx0, hx⟩
    by_cases h0 : ‖t‖ < ρ
    · have hev : borelGlue f a ρ c0 =ᶠ[𝓝 t] borelT a := by
        filter_upwards [(Metric.isOpen_ball (x := (0 : ℂ)) (ε := ρ)).mem_nhds (by simpa using h0)] with s hs
        rw [mem_ball_zero_iff] at hs
        simp [borelGlue, hs]
      exact (h.analyticOnNhd_borelT t (by simpa using h0)).congr hev.symm
    · have hxpos : 0 < x := by
        rcases hx0.eq_or_lt with h' | h'
        · exfalso; apply h0; simpa [← h'] using hx
        · exact h'
      have hev : borelGlue f a ρ c0 =ᶠ[𝓝 t] borelLocal f a x c0 := by
        filter_upwards [(Metric.isOpen_ball (x := (x : ℂ)) (ε := ρ)).mem_nhds
          (by rwa [Metric.mem_ball, dist_eq_norm])] with s hs
        exact h.borelGlue_eq_local hc0 hxpos (by rwa [Metric.mem_ball, dist_eq_norm] at hs)
      exact (h.analyticOnNhd_borelLocal hc0 hxpos t (by rwa [Metric.mem_ball, dist_eq_norm])).congr hev.symm
  · intro t ht
    simp [borelGlue, ht]
  · intro c hc x hx
    by_cases hxρ : x < ρ
    · have : ‖(x : ℂ)‖ < ρ := by rwa [Complex.norm_real, Real.norm_of_nonneg hx.le]
      simp only [borelGlue, this, ↓reduceIte]
      exact (h.borelZero_eq_borelT hx hxρ hc).symm
    · have : ¬ ‖(x : ℂ)‖ < ρ := by rwa [Complex.norm_real, Real.norm_of_nonneg hx.le]
      simp only [borelGlue, this, ↓reduceIte, Complex.ofReal_re]
      rw [h.borelLocal_real hc0 hx hx (by simpa using hρ), borelDeriv_zero]
      exact h.borelZero_indep' x hc0 hc
  · intro ρ' hρ'
    by_cases hρ'0 : 0 < ρ'
    · refine ⟨_, fun t ht => h.norm_borelGlue_le hρ'0 hρ' hc0 ht⟩
    · refine ⟨0, fun t ⟨x, _, hx⟩ => ?_⟩
      exfalso
      linarith [norm_nonneg (t - (x : ℂ))]

end Lightlike.FieldTheory.Borel
