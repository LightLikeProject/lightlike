import Mathlib
import Lightlike.Dirac.ModeSphere

/-!
# The angular modes of a bounded `C¹` pair on the plane: boundedness, support and the case `λ = 0`

For a `C¹` pair `(g₁, g₂)` on the plane that solves the chart equations
`(1+|x|²) i (∂₀ g₁ + i ∂₁ g₁) = 2λ g₂`, `(1+|x|²) i (∂₀ g₂ − i ∂₁ g₂) = 2λ g₁` and decays like `1/|x|`, the Fourier
modes `a_m = fcoef g₁ m`, `b_m = fcoef g₂ (m+1)` solve the radial mode system, are bounded at `0` and decay like `1/r`
(`pair_mode_data`).  For `λ = ±k` with `k ≥ 1` an integer a mode can be nonzero only for `-k ≤ m ≤ k-1`
(`mode_range`: the sharp range of `mode_decay_quantized`, `2k` values of `m`).  For `λ = 0` the radial system
decouples into `a' = (n/r) a`, whose solutions `K r^n` are never bounded at `0` and decaying at `∞`
(`power_sol_zero`).
-/

namespace Lightlike.Dirac

open Complex

/-- **Boundedness and decay of the modes.** -/
theorem pair_mode_data {g₁ g₂ : E 2 → ℂ} (h₁ : ContDiff ℝ 1 g₁) (h₂ : ContDiff ℝ 1 g₂) {lam : ℂ}
    (hA : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₁ x (e (0 : Fin 2)) + Complex.I * fderiv ℝ g₁ x (e (1 : Fin 2))) = 2 * lam * g₂ x)
    (hB : ∀ x : E 2, (1 + (‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I *
      (fderiv ℝ g₂ x (e (0 : Fin 2)) - Complex.I * fderiv ℝ g₂ x (e (1 : Fin 2))) = 2 * lam * g₁ x)
    {C : ℝ} (hdec : ∀ x : E 2, 1 ≤ ‖x‖ → ‖g₁ x‖ ≤ C / ‖x‖ ∧ ‖g₂ x‖ ≤ C / ‖x‖) (m : ℤ) :
    IsModeSol (2 * lam / Complex.I) m (fun r => fcoef (polarFn g₁) m r)
        (fun r => fcoef (polarFn g₂) (m + 1) r) ∧
      (∃ C₀ : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
        ‖fcoef (polarFn g₁) m r‖ ≤ C₀ ∧ ‖fcoef (polarFn g₂) (m + 1) r‖ ≤ C₀) ∧
      (∀ r : ℝ, 1 ≤ r → ‖fcoef (polarFn g₁) m r‖ ≤ C * (2 * Real.pi) / r ∧
        ‖fcoef (polarFn g₂) (m + 1) r‖ ≤ C * (2 * Real.pi) / r) := by
  refine ⟨fourier_modes_isModeSol h₁ h₂ lam hA hB m, ?_, ?_⟩
  · obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn
      h₁.continuous.continuousOn
    obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (0 : E 2) 1).exists_bound_of_continuousOn
      h₂.continuous.continuousOn
    refine ⟨max (M₁ * (2 * Real.pi)) (M₂ * (2 * Real.pi)), fun r hr hr1 => ?_⟩
    have hn : ∀ θ : ℝ, ‖polarPt r θ‖ ≤ 1 := fun θ => by
      have := polarPt_norm_sq r θ
      nlinarith [norm_nonneg (polarPt r θ)]
    constructor
    · exact (fcoef_norm_le _ m r M₁ fun θ => hM₁ _ (by simpa using hn θ)).trans (le_max_left _ _)
    · exact (fcoef_norm_le _ (m + 1) r M₂ fun θ => hM₂ _ (by simpa using hn θ)).trans (le_max_right _ _)
  · intro r hr
    have hn : ∀ θ : ℝ, ‖polarPt r θ‖ = r := fun θ => by
      have := polarPt_norm_sq r θ
      have h0 : 0 ≤ ‖polarPt r θ‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖polarPt r θ‖ - r), sq_nonneg (‖polarPt r θ‖ + r)]
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    constructor
    · have := fcoef_norm_le (polarFn g₁) m r (C / r) fun θ => by
        have := (hdec (polarPt r θ) (by rw [hn θ]; exact hr)).1
        rwa [hn θ] at this
      calc _ ≤ C / r * (2 * Real.pi) := this
        _ = C * (2 * Real.pi) / r := by ring
    · have := fcoef_norm_le (polarFn g₂) (m + 1) r (C / r) fun θ => by
        have := (hdec (polarPt r θ) (by rw [hn θ]; exact hr)).2
        rwa [hn θ] at this
      calc _ ≤ C / r * (2 * Real.pi) := this
        _ = C * (2 * Real.pi) / r := by ring

/-- **The support of the modes.** For `λ = ±k` (`k ≥ 1`) a nonzero bounded decaying solution of the radial mode
system with angular index `m` exists only for `-k ≤ m ≤ k - 1`. -/
theorem mode_range {k : ℕ} (hk : 1 ≤ k) {lam : ℂ} (hlam : lam = (k : ℂ) ∨ lam = -(k : ℂ)) (m : ℤ)
    {a b : ℝ → ℂ} (hsol : IsModeSol (2 * lam / Complex.I) m a b) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hnz : a r₀ ≠ 0 ∨ b r₀ ≠ 0) {C₀ : ℝ}
    (hbd : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖a r‖ ≤ C₀ ∧ ‖b r‖ ≤ C₀) {C₁ : ℝ}
    (hdec : ∀ r : ℝ, 1 ≤ r → ‖a r‖ ≤ C₁ / r ∧ ‖b r‖ ≤ C₁ / r) :
    -(k : ℤ) ≤ m ∧ m ≤ (k : ℤ) - 1 := by
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlam0 : lam ≠ 0 := by
    rcases hlam with h | h
    · rw [h]; exact hk0
    · rw [h]; exact neg_ne_zero.mpr hk0
  set ν : ℂ := 2 * lam / Complex.I with hν
  have hν0 : ν ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero hlam0) Complex.I_ne_zero
  have hαlam : Complex.I * ν / 2 = lam := by rw [hν]; field_simp
  have hkk : ∀ k' : ℕ, (Complex.I * ν / 2 = k' ∨ Complex.I * ν / 2 = -(k' : ℂ)) → k' = k := by
    intro k' h
    rw [hαlam] at h
    rcases hlam with h1 | h1 <;> rcases h with h2 | h2
    · rw [h1] at h2; exact_mod_cast h2.symm
    · rw [h1] at h2
      have : ((k + k' : ℕ) : ℂ) = 0 := by push_cast; linear_combination h2
      have := Nat.cast_eq_zero.mp this
      omega
    · rw [h1] at h2
      have : ((k + k' : ℕ) : ℂ) = 0 := by push_cast; linear_combination -h2
      have := Nat.cast_eq_zero.mp this
      omega
    · rw [h1] at h2
      have h3 : (k : ℂ) = k' := by linear_combination -h2
      exact_mod_cast h3.symm
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    obtain ⟨k', hk', h⟩ := mode_decay_quantized hν0 n hsol hr₀ hnz hbd hdec
    have := hkk k' h
    omega
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, -(m + 1) = n := ⟨(-(m + 1)).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hsw := hsol.swap
    rw [hn] at hsw
    obtain ⟨k', hk', h⟩ := mode_decay_quantized hν0 n hsw hr₀ hnz.symm
      (fun r hr hr1 => ⟨(hbd r hr hr1).2, (hbd r hr hr1).1⟩)
      (fun r hr => ⟨(hdec r hr).2, (hdec r hr).1⟩)
    have := hkk k' h
    omega

/-- **The case `λ = 0`.** A solution of `a' = (n/r) a` on `r > 0` that is bounded near `0` and decays like `1/r`
at infinity is zero (`a = K r^n`). -/
theorem power_sol_zero (n : ℤ) {a : ℝ → ℂ}
    (ha : ∀ r : ℝ, 0 < r → HasDerivAt a (((n : ℂ) / r) * a r) r)
    {C₀ : ℝ} (hbd : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖a r‖ ≤ C₀)
    {C₁ : ℝ} (hdec : ∀ r : ℝ, 1 ≤ r → ‖a r‖ ≤ C₁ / r) : ∀ r : ℝ, 0 < r → a r = 0 := by
  set u : ℝ → ℂ := fun r => a r * ((r : ℂ) ^ (-n)) with hu
  have hud : ∀ r : ℝ, 0 < r → HasDerivAt u 0 r := by
    intro r hr
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2 : HasDerivAt (fun r : ℝ => ((r : ℂ) ^ (-n))) (((-n : ℤ) : ℂ) * (r : ℂ) ^ (-n - 1)) r :=
      (hasDerivAt_zpow (-n) (r : ℂ) (Or.inl hr')).comp_ofReal
    have h3 := (ha r hr).mul h2
    refine h3.congr_deriv ?_
    rw [zpow_sub₀ hr', zpow_one]
    push_cast
    field_simp
    ring
  have hconst : ∀ r : ℝ, 0 < r → u r = u 1 := by
    intro r hr
    have hdiff : DifferentiableOn ℝ u (Set.Ioi 0) := fun x hx => (hud x hx).differentiableAt.differentiableWithinAt
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (isPreconnected_Ioi) hdiff
      (fun x hx => (hud x hx).deriv) hr (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
  set K : ℂ := u 1 with hK
  have haK : ∀ r : ℝ, 0 < r → a r = K * (r : ℂ) ^ n := by
    intro r hr
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have := hconst r hr
    simp only [hu] at this
    rw [← this, mul_assoc, ← zpow_add₀ hr']
    simp
  have hnorm : ∀ r : ℝ, 0 < r → ‖a r‖ = ‖K‖ * r ^ n := by
    intro r hr
    rw [haK r hr, norm_mul, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hK0 : K = 0 := by
    by_contra hKne
    have hKpos : 0 < ‖K‖ := norm_pos_iff.mpr hKne
    rcases le_or_gt 0 n with hn | hn
    · -- decay: `‖K‖ r^(j+1) ≤ C₁` for `r ≥ 1`, but `r^(j+1) ≥ r`
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = (j : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
      set R : ℝ := max 1 (C₁ / ‖K‖ + 1) with hR
      have hR1 : 1 ≤ R := le_max_left _ _
      have hR0 : 0 < R := by linarith
      have h1 := hdec R hR1
      rw [hnorm R hR0, zpow_natCast, le_div_iff₀ hR0] at h1
      have h2 : R ≤ R ^ (j + 1) := le_self_pow₀ hR1 (by omega)
      have h3 : ‖K‖ * R ≤ C₁ := by
        calc ‖K‖ * R ≤ ‖K‖ * R ^ (j + 1) := mul_le_mul_of_nonneg_left h2 hKpos.le
          _ = ‖K‖ * R ^ j * R := by ring
          _ ≤ C₁ := h1
      have h5 : C₁ / ‖K‖ < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      rw [div_lt_iff₀ hKpos] at h5
      linarith
    · -- regular at `0`: `‖K‖ (r^(j+1))⁻¹ ≤ C₀` for `r ≤ 1`, but `(r^(j+1))⁻¹ ≥ r⁻¹`
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = -((j : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
      have hC0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hbd 1 one_pos le_rfl)
      set R : ℝ := min 1 (‖K‖ / (2 * (C₀ + 1))) with hR
      have hq : 0 < ‖K‖ / (2 * (C₀ + 1)) := by positivity
      have hR0 : 0 < R := lt_min one_pos hq
      have hR1 : R ≤ 1 := min_le_left _ _
      have hRq : R ≤ ‖K‖ / (2 * (C₀ + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at hRq
      have h1 := hbd R hR0 hR1
      have hz : R ^ (-((j : ℤ) + 1)) = (R ^ (j + 1))⁻¹ := by
        have : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [this, zpow_neg, zpow_natCast]
      rw [hnorm R hR0, hz] at h1
      have h2 : R ^ (j + 1) ≤ R := pow_le_of_le_one hR0.le hR1 (by omega)
      have h3 : R⁻¹ ≤ (R ^ (j + 1))⁻¹ := inv_anti₀ (by positivity) h2
      have h4 : ‖K‖ * R⁻¹ ≤ C₀ := le_trans (mul_le_mul_of_nonneg_left h3 hKpos.le) h1
      have h5 : ‖K‖ ≤ C₀ * R := by
        have := mul_le_mul_of_nonneg_right h4 hR0.le
        rwa [mul_assoc, inv_mul_cancel₀ hR0.ne', mul_one] at this
      nlinarith [hR0, hC0]
  intro r hr
  rw [haK r hr, hK0, zero_mul]

end Lightlike.Dirac
