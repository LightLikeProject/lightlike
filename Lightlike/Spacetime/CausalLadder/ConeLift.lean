import Lightlike.Spacetime.CausalLadder.ConeStability

/-!
# A causal vector plus a large timelike push lies in the cone with a margin

Let `a q` be the Gram matrix and `b q` the pairing with the time orientation, continuous at `p` as in `ConeTransfer`, and `e` a vector that is
future-directed timelike at `p`. A future-directed causal vector `w` at a point `q` near `p` has `‖w‖ ≤ c · (-(b p ⬝ w))`
(`uniform_cone_bound`). If `s` is at least `Θ · (-(b p ⬝ w))` for a constant `Θ` (depending on `c` and the stability constant of
`cone_margin_stable`), then `s e` is a vector with a margin at `p` and `w` is a perturbation of relative size at most `θ`, so
`w + s e` lies in the cone with a margin at every point `q'` near `p`, with a margin independent of `w` and `s`. In a chart this is the
estimate behind lifting a causal curve to a timelike curve by adding a displacement along `e` whose rate is proportional to the
`-(b p ⬝ ·)`-rate of the curve (the push-up lemma of causality theory).

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Filter Topology

namespace Lightlike.Causal

/-- **A causal vector plus a large timelike push has a margin.** See the module docstring. -/
theorem cone_lift_margin {Q : Type*} [TopologicalSpace Q] {n : ℕ} {p : Q}
    {a : Q → Fin n → Fin n → ℝ} {b : Q → Fin n → ℝ} (ha : ContinuousAt a p)
    (hb : ContinuousAt b p)
    (h0 : ∀ w : Fin n → ℝ, w ≠ 0 → quadForm (a p) w ≤ 0 → linForm (b p) w ≠ 0)
    {e : Fin n → ℝ} (hQ : quadForm (a p) e < 0) (hL : linForm (b p) e < 0) :
    ∃ W ∈ 𝓝 p, ∃ Θ > 0, ∃ ε > 0, ∀ q ∈ W, ∀ q' ∈ W, ∀ w : Fin n → ℝ, ∀ s : ℝ,
      quadForm (a q) w ≤ 0 → linForm (b q) w < 0 → 0 < s → Θ * (-(linForm (b p) w)) ≤ s →
        quadForm (a q') (w + s • e) ≤ -ε * (linForm (b q') (w + s • e)) ^ 2 ∧
          linForm (b q') (w + s • e) < 0 := by
  have hL2 : 0 < linForm (b p) e ^ 2 := by nlinarith [mul_pos_of_neg_of_neg hL hL]
  set ε₀ : ℝ := -quadForm (a p) e / linForm (b p) e ^ 2 with hε₀
  have hε₀pos : 0 < ε₀ := div_pos (by linarith) hL2
  have he0 : e ≠ 0 := by
    rintro rfl
    simp [linForm] at hL
  have hen : 0 < ‖e‖ := norm_pos_iff.2 he0
  obtain ⟨W1, hW1, c, hc, hcone⟩ := uniform_cone_bound ha hb h0
  obtain ⟨W2, hW2, θ, hθ, hstab⟩ := cone_margin_stable ha hb h0 hε₀pos
  have hpW1 : p ∈ W2 := mem_of_mem_nhds hW2
  refine ⟨W1 ∩ W2, inter_mem hW1 hW2, c / (θ * ‖e‖), by positivity, ε₀ / 2, by positivity, ?_⟩
  intro q hq q' hq' w s hqw hbw hs hsΘ
  have hmargin : quadForm (a p) (s • e) ≤ -ε₀ * (linForm (b p) (s • e)) ^ 2 := by
    rw [quadForm_smul, linForm_smul]
    have : quadForm (a p) e = -ε₀ * linForm (b p) e ^ 2 := by
      have hLne : linForm (b p) e ≠ 0 := hL.ne
      rw [hε₀]; field_simp
    rw [this]; ring_nf; exact le_rfl
  have hneg : linForm (b p) (s • e) < 0 := by
    rw [linForm_smul]; exact mul_neg_of_pos_of_neg hs hL
  have hnorm : ‖w‖ ≤ θ * ‖s • e‖ := by
    have h1 := hcone q hq.1 w hqw hbw
    have h2 : c * (-(linForm (b p) w)) ≤ c * (s / (c / (θ * ‖e‖))) := by
      refine mul_le_mul_of_nonneg_left ?_ hc.le
      rw [le_div_iff₀ (by positivity)]
      calc -(linForm (b p) w) * (c / (θ * ‖e‖)) = (c / (θ * ‖e‖)) * (-(linForm (b p) w)) := by ring
        _ ≤ s := hsΘ
    have h3 : c * (s / (c / (θ * ‖e‖))) = θ * ‖s • e‖ := by
      rw [norm_smul, Real.norm_of_nonneg hs.le]; field_simp
    linarith
  have := hstab p hpW1 q' hq'.2 (s • e) w hmargin hneg hnorm
  rw [add_comm] at this
  simpa [add_comm] using this

end Lightlike.Causal
