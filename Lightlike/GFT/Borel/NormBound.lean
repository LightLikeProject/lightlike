import Lightlike.GFT.Borel.Deriv

/-!
# The bound on `b_m` (task T-GF7-P2)

Serves task T-GF7-P2 (Nevanlinna–Sokal, Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B,
after eq. (B.6)): `SokalHyp.norm_borelDeriv_le`, with the statement copied word for word from
`Tasks/GF/T_GF7_P2.lean`. The integrand is bounded by the rest-term bound with `q = m + 1`, the integral of
`(c² + y²)⁻¹` is `π / c`, and `|a_m| ≤ K m! ρ^{-m}` handles the constant term.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

/-- **The bound on `b_m`** (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776v2, Appendix B, after eq. (B.6),
p. 25, with `β = 0`): under the hypotheses of the Nevanlinna–Sokal theorem, along the line `Re w = c > 1/R`,
`|b_m(x)| ≤ K (ρ + 1/(2c)) (m+1)! ρ^{-m-1} e^{cx}` for all `m` and `x ≥ 0`.

The source writes `|b_m(x)| ≤ K (m+1)! (m+1)^β ρ^{-m-1} e^{x/r}` with `r = 1/c` and the constant absorbed in `K`;
here the constant is explicit (kind: representation). Non-vacuous: `sokalHyp_const`. Serves task T-GF7-P2. -/
theorem SokalHyp.norm_borelDeriv_le {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ} (h : SokalHyp f a R K ρ) {c : ℝ}
    (hc : 1 / R < c) (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖borelDeriv f a m x c‖ ≤ K * (ρ + 1 / (2 * c)) * (m + 1) ! / ρ ^ (m + 1) * Real.exp (c * x) := by
  have hR := h.R_pos
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  have hwre : ∀ y : ℝ, 1 / R < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hw0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_gt hR (hwre y)
  set C : ℝ := Real.exp (x * c) * (K * (m + 1) ! / ρ ^ (m + 1)) with hC
  have hbd : ∀ y : ℝ, ‖cexp (x * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) *
      taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖ ≤ C * (c ^ 2 + y ^ 2)⁻¹ := by
    intro y
    have hn : 0 < ‖(c : ℂ) + y * I‖ := norm_pos_iff.2 (hw0 y)
    have hr := h.rem (m + 1) _ (inv_mem_diskC (hwre y))
    rw [norm_inv] at hr
    rw [norm_mul, norm_mul, norm_cexp_mul_vertical, norm_zpow, ← sq_norm_add_mul_I]
    have hr' : ‖taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖ ≤
        K * (m + 1) ! / ρ ^ (m + 1) * ‖(c : ℂ) + y * I‖⁻¹ ^ (m + 1) := hr
    calc Real.exp (x * c) * ‖(c : ℂ) + y * I‖ ^ ((m : ℤ) - 1) *
          ‖taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖
        ≤ Real.exp (x * c) * ‖(c : ℂ) + y * I‖ ^ ((m : ℤ) - 1) *
          (K * (m + 1) ! / ρ ^ (m + 1) * ‖(c : ℂ) + y * I‖⁻¹ ^ (m + 1)) := by gcongr
      _ = C * (‖(c : ℂ) + y * I‖ ^ 2)⁻¹ := by
          rw [hC, zpow_sub₀ hn.ne', zpow_one, zpow_natCast, inv_pow]
          field_simp
          ring
  have hint : ‖((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) *
      taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖ ≤ C / (2 * c) := by
    have hC0 : 0 ≤ C := by positivity
    calc _ = (2 * π)⁻¹ * ‖∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) * ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) *
          taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖ := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      _ ≤ (2 * π)⁻¹ * ∫ y : ℝ, C * (c ^ 2 + y ^ 2)⁻¹ := by
          gcongr
          exact norm_integral_le_of_norm_le ((integrable_inv_sq_add hc0).const_mul C)
            (Filter.Eventually.of_forall hbd)
      _ = C / (2 * c) := by
          rw [integral_const_mul, integral_inv_sq_add hc0]
          field_simp
  have ha := h.norm_coeff_le m
  have hex : 1 ≤ Real.exp (c * x) := Real.one_le_exp (by positivity)
  have hfm : (m ! : ℝ) ≤ (m + 1) ! := by exact_mod_cast Nat.factorial_le (Nat.le_succ m)
  have hρm : 0 < ρ ^ (m + 1) := pow_pos hρ _
  have hexc : Real.exp (x * c) = Real.exp (c * x) := by rw [mul_comm]
  have h1 : ‖a m‖ ≤ K * ρ * (m + 1) ! / ρ ^ (m + 1) * Real.exp (c * x) := by
    refine ha.trans ?_
    have e : K * ρ * (m + 1) ! / ρ ^ (m + 1) = ρ * (K * (m + 1) ! / ρ ^ (m + 1)) := by ring
    have e2 : K * (m ! : ℝ) / ρ ^ m = ρ * (K * m ! / ρ ^ (m + 1)) := by
      rw [pow_succ]; field_simp
    calc K * (m ! : ℝ) / ρ ^ m = ρ * (K * m ! / ρ ^ (m + 1)) := e2
      _ ≤ ρ * (K * (m + 1) ! / ρ ^ (m + 1)) := by gcongr
      _ = K * ρ * (m + 1) ! / ρ ^ (m + 1) := e.symm
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hex
  unfold borelDeriv
  calc _ ≤ ‖a m‖ + ‖((2 * π : ℝ) : ℂ)⁻¹ * ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) *
        ((c : ℂ) + y * I) ^ ((m : ℤ) - 1) * taylorRem f a (m + 1) ((c : ℂ) + y * I)⁻¹‖ := norm_add_le _ _
    _ ≤ K * ρ * (m + 1) ! / ρ ^ (m + 1) * Real.exp (c * x) + C / (2 * c) := add_le_add h1 hint
    _ = _ := by
        rw [hC, hexc]
        field_simp

end Lightlike.FieldTheory.Borel
