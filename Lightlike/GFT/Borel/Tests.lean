import Lightlike.GFT.Borel.Quartic

/-!
# Trust checks for GF7 (Borel summability)

* `quartic_borelSum_vs_series`: at small real coupling `λ`, the Borel sum `λ⁻¹ ∫ e^{-t/λ} B(t) dt` of the quartic
  model differs from the first Taylor term `a₀ = √(2π)` by at most `3 √(2π) λ` (Rivasseau–Wang (III-34) with
  `M = 1`), i.e. the Borel sum is the function whose asymptotic series is the perturbative series.
* `quarticCoeff_zero`, `quarticCoeff_one`: `a₀ = √(2π)`, `a₁ = -3 √(2π)`.
* `not_sokalHyp_of_superfactorial`: a series whose coefficients grow like `(q!)²` (the growth of the unmodified
  model, which has no Nevanlinna–Sokal bound `|a_q| ≤ K q! ρ^{-q}`) does not satisfy the hypotheses of the
  Nevanlinna–Sokal theorem for any `f`, `R`, `K`, `ρ`; so the Borel route is closed to it.
* `quartic_coeff_factorial_bound`: the quartic coefficients do satisfy such a bound.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory

open Borel

/-- `a₀ = √(2π)`. -/
lemma quarticCoeff_zero : quarticCoeff 0 = (√(2 * Real.pi) : ℝ) := by
  simp [quarticCoeff]

/-- `a₁ = -3 √(2π)`. -/
lemma quarticCoeff_one : quarticCoeff 1 = ((-3 * √(2 * Real.pi) : ℝ) : ℂ) := by
  simp [quarticCoeff]
  ring

/-- The quartic coefficients satisfy the factorial bound `|a_q| ≤ K q!/ρ^q`, `ρ = 1/32`. -/
theorem quartic_coeff_factorial_bound (q : ℕ) :
    ‖quarticCoeff q‖ ≤ 16 * √(2 * Real.pi) * q ! / (1 / 32 : ℝ) ^ q :=
  (quarticZ_sokalHyp (R := 1) one_pos).norm_coeff_le q

/-- **Super-factorial growth prevents Borel summability** (in the Nevanlinna–Sokal sense): coefficients with
`(q!)² ≤ |a_q|` violate `|a_q| ≤ K q! ρ^{-q}` for every `K`, `ρ`. -/
theorem not_sokalHyp_of_superfactorial {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}
    (ha : ∀ q : ℕ, ((q ! : ℕ) : ℝ) ^ 2 ≤ ‖a q‖) : ¬ SokalHyp f a R K ρ := by
  intro h
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop (1 / ρ)
  have hev : ∀ᶠ q : ℕ in atTop, (1 / ρ) ^ q / (q ! : ℝ) < 1 / (K + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨q, hq⟩ := hev.exists
  have hf : (0 : ℝ) < (q ! : ℝ) := by positivity
  have hp : (0 : ℝ) < ρ ^ q := pow_pos hρ q
  have hb := (ha q).trans (h.norm_coeff_le q)
  rw [le_div_iff₀ hp] at hb
  have h1 : (q ! : ℝ) * ρ ^ q ≤ K := by
    have : (q ! : ℝ) * ((q ! : ℝ) * ρ ^ q) ≤ (q ! : ℝ) * K := by nlinarith
    exact le_of_mul_le_mul_left this hf
  rw [one_div_pow, div_div] at hq
  have h2 : K + 1 < ρ ^ q * (q ! : ℝ) := (one_div_lt_one_div (mul_pos hp hf) (by positivity)).1 hq
  nlinarith

/-- **Trust check, Borel sum against the series.** For every small real coupling `λ`, the Borel sum of the quartic
model is within `3 √(2π) λ` of the zeroth-order term of the perturbative series. -/
theorem quartic_borelSum_vs_series :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ B : ℂ → ℂ, AnalyticOnNhd ℂ B (sokalStrip ρ) ∧
      ∀ l : ℝ, 0 < l → ‖((l : ℂ)⁻¹ * ∫ x in Ioi (0 : ℝ), cexp (-(x / (l : ℂ))) * B x) -
        (√(2 * Real.pi) : ℝ)‖ ≤ 3 * √(2 * Real.pi) * l := by
  obtain ⟨ρ, hρ, B, hB, -, hL⟩ := quarticZ_borel_summable
  refine ⟨ρ, hρ, B, hB, fun l hl => ?_⟩
  have hz : (l : ℂ) ∈ diskC (2 * l) := ofReal_mem_diskC hl (by linarith)
  have h := norm_quarticZ_sub_le 1 (z := (l : ℂ)) (by simpa using hl.le)
  have e : ((4 * 1 - 1)‼ : ℕ) = 3 := by decide
  rw [e] at h
  have hs : ∑ n ∈ range 1, quarticCoeff n * (l : ℂ) ^ n = ((√(2 * Real.pi) : ℝ) : ℂ) := by
    simp [quarticCoeff_zero]
  have hn : ‖(l : ℂ)‖ ^ 1 = l := by simp [abs_of_pos hl]
  rw [hs, hL (2 * l) (by positivity) _ hz, hn] at h
  have key : √(2 * Real.pi) * (((3 : ℕ) : ℝ) / ((1 ! : ℕ) : ℝ)) * l = 3 * √(2 * Real.pi) * l := by
    rw [show ((1 ! : ℕ) : ℝ) = 1 by norm_num [Nat.factorial]]
    push_cast
    ring
  rw [key] at h
  exact h

end Lightlike.FieldTheory
