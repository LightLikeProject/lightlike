import Mathlib
import Lightlike.Dirac.ModeHyper

/-!
# Classification of the decaying modes

A non-trivial solution `(a, b)` of the radial mode system with angular index `m ≥ 0` that is bounded near `0` and decays
like `1/r` at infinity exists only if `i ν / 2 = ±k` for an integer `k ≥ m + 1`.
-/

namespace Lightlike.Dirac

/-- **The quantisation of the decaying modes** (angular index `m ≥ 0`). -/
theorem mode_decay_quantized {ν : ℂ} (hν : ν ≠ 0) (m : ℕ) {a b : ℝ → ℂ} (hsol : IsModeSol ν m a b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hnz : a r₀ ≠ 0 ∨ b r₀ ≠ 0) {C₀ : ℝ}
    (hbd : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖a r‖ ≤ C₀ ∧ ‖b r‖ ≤ C₀) {C₁ : ℝ}
    (hdec : ∀ r : ℝ, 1 ≤ r → ‖a r‖ ≤ C₁ / r ∧ ‖b r‖ ≤ C₁ / r) :
    ∃ k : ℕ, m + 1 ≤ k ∧ (Complex.I * ν / 2 = k ∨ Complex.I * ν / 2 = -(k : ℂ)) := by
  set α : ℂ := Complex.I * ν / 2 with hα
  have hα2 : α ^ 2 = -ν ^ 2 / 4 := by rw [hα]; ring_nf; simp [Complex.I_sq]; ring
  obtain ⟨L, hL, hLz⟩ := hgPartial_limit α m
  by_contra hno
  have hL0 : L ≠ 0 := fun h => hno (hLz.mp h)
  have hsolA := modeHyper_isModeSol hν hα2 m
  obtain ⟨C₂, hC₂⟩ := modeHyper_bdd hν α m
  -- the Wronskian with the regular solution vanishes
  have hW := mode_wronskian_zero_of_bounded (C := max C₀ C₂) hsol hsolA (fun r hr hr1 => by
    obtain ⟨h1, h2⟩ := hbd r hr hr1
    obtain ⟨h3, h4⟩ := hC₂ r hr hr1
    exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_left _ _), h3.trans (le_max_right _ _),
      h4.trans (le_max_right _ _)⟩)
  -- A = c a for a constant c
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℂ, modeA α m r₀ = c * a r₀ ∧ modeB ν α m r₀ = c * b r₀ := by
    have hw := hW r₀ hr₀
    rcases hnz with h | h
    · refine ⟨modeA α m r₀ / a r₀, by field_simp, ?_⟩
      field_simp
      linear_combination hw
    · refine ⟨modeB ν α m r₀ / b r₀, ?_, by field_simp⟩
      field_simp
      linear_combination -hw
  have hZ := (hsolA.sub (hsol.smul c))
  have hz := mode_sol_zero hZ hr₀ (by simp [hc1]) (by simp [hc2])
  have hAeq : ∀ r : ℝ, 0 < r → modeA α m r = c * a r := fun r hr => by
    have := (hz r hr).1
    simpa [sub_eq_zero] using this
  -- A decays, contradiction with the limit
  have hAbdd := tendsto_hgSum_atTop (m := m) hL
  refine not_decay_of_limit_ne hL0 hAbdd (‖c‖ * C₁) fun r hr => ?_
  rw [hAeq r (by linarith), norm_mul]
  calc ‖c‖ * ‖a r‖ ≤ ‖c‖ * (C₁ / r) := mul_le_mul_of_nonneg_left (hdec r hr).1 (norm_nonneg _)
    _ = ‖c‖ * C₁ / r := by ring

/-- The symmetry `(a, b, m) ↦ (b, a, −m−1)` of the mode system. -/
theorem IsModeSol.swap {ν : ℂ} {m : ℤ} {a b : ℝ → ℂ} (h : IsModeSol ν m a b) :
    IsModeSol ν (-(m + 1)) b a := by
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  refine ⟨?_, ?_⟩
  · refine h2.congr_deriv ?_
    push_cast
    ring
  · refine h1.congr_deriv ?_
    push_cast
    ring

/-- **Quantisation for every angular index**: a non-trivial decaying mode with the regularity at the origin forces
`i ν / 2 = ±k` with `k ≥ 1` an integer. -/
theorem mode_decay_quantized_int {ν : ℂ} (hν : ν ≠ 0) (m : ℤ) {a b : ℝ → ℂ} (hsol : IsModeSol ν m a b)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hnz : a r₀ ≠ 0 ∨ b r₀ ≠ 0) {C₀ : ℝ}
    (hbd : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖a r‖ ≤ C₀ ∧ ‖b r‖ ≤ C₀) {C₁ : ℝ}
    (hdec : ∀ r : ℝ, 1 ≤ r → ‖a r‖ ≤ C₁ / r ∧ ‖b r‖ ≤ C₁ / r) :
    ∃ k : ℕ, 1 ≤ k ∧ (Complex.I * ν / 2 = k ∨ Complex.I * ν / 2 = -(k : ℂ)) := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    obtain ⟨k, hk, h⟩ := mode_decay_quantized hν n hsol hr₀ hnz hbd hdec
    exact ⟨k, by omega, h⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, -(m + 1) = n := ⟨(-(m + 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hsw := hsol.swap
    rw [hn] at hsw
    obtain ⟨k, hk, h⟩ := mode_decay_quantized hν n hsw hr₀ (by tauto) (fun r hr hr1 => ⟨(hbd r hr hr1).2, (hbd r hr hr1).1⟩)
      (fun r hr => ⟨(hdec r hr).2, (hdec r hr).1⟩)
    exact ⟨k, by omega, h⟩

end Lightlike.Dirac
