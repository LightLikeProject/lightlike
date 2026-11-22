import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Basic

/-!
# Abelian-Higgs vortices: the pointwise Bogomolny identity

Row G1-047 (CO24). Normalization fixed here: for a gauge potential `A = (A₁, A₂)`, a complex Higgs field
`φ`, charge `e` and vacuum modulus `v`, with `D_j = ∂_j - i e A_j`, `B = ∂₁A₂ - ∂₂A₁`, the energy density is
`½ B² + |D₁φ|² + |D₂φ|² + (e²/2) (|φ|² - v²)²` (critical coupling `λ = e²`; see Hindmarsh–Kibble 1995,
`hindmarsh-kibble-1995`, for the model).

This file is the algebra, at one point. With `a = D₁φ`, `b = D₂φ`, the field computation
`∂₁ Im(φ̄ D₂φ) - ∂₂ Im(φ̄ D₁φ) = 2 Im(ā b) - e B |φ|²` is the hypothesis `hK` (`K` is the curl of the
current; it is proved from the derivatives in a later file). Under it the density is
* `½ (B - e(v² - |φ|²))² + |a + i b|² + e v² B + K`  (`energyDensity_eq_plus`),
* `½ (B + e(v² - |φ|²))² + |a - i b|² - e v² B - K`  (`energyDensity_eq_minus`).
Supporting lemmas; no catalogue entry.
-/

namespace Lightlike.Rows.G1_047

open Complex ComplexConjugate

/-- The Abelian-Higgs energy density at critical coupling in the normalization above, in terms of
`B`, `a = D₁φ`, `b = D₂φ`, `φ`, `e`, `v`. -/
noncomputable def energyDensity (e v B : ℝ) (a b φ : ℂ) : ℝ :=
  B ^ 2 / 2 + (‖a‖ ^ 2 + ‖b‖ ^ 2) + e ^ 2 / 2 * (‖φ‖ ^ 2 - v ^ 2) ^ 2

/-- The identity `|a|² + |b|² = |a + i b|² - 2 Im(a b̄)`. -/
theorem normSq_sum_eq_plus (a b : ℂ) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 = ‖a + I * b‖ ^ 2 + 2 * (conj a * b).im := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- The identity `|a|² + |b|² = |a - i b|² - 2 Im(ā b)`. -/
theorem normSq_sum_eq_minus (a b : ℂ) :
    ‖a‖ ^ 2 + ‖b‖ ^ 2 = ‖a - I * b‖ ^ 2 - 2 * (conj a * b).im := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **Pointwise Bogomolny identity, positive sign.** If `2 Im(ā b) = K + e B |φ|²` then
`ε = ½ (B - e(v² - |φ|²))² + |a + i b|² + e v² B + K`. -/
theorem energyDensity_eq_plus (e v B K : ℝ) (a b φ : ℂ)
    (hK : 2 * (conj a * b).im = K + e * B * ‖φ‖ ^ 2) :
    energyDensity e v B a b φ =
      (B - e * (v ^ 2 - ‖φ‖ ^ 2)) ^ 2 / 2 + ‖a + I * b‖ ^ 2 + e * v ^ 2 * B + K := by
  unfold energyDensity
  rw [normSq_sum_eq_plus, hK]
  ring

/-- **Pointwise Bogomolny identity, negative sign.** Under the same hypothesis
`ε = ½ (B + e(v² - |φ|²))² + |a - i b|² - e v² B - K`. -/
theorem energyDensity_eq_minus (e v B K : ℝ) (a b φ : ℂ)
    (hK : 2 * (conj a * b).im = K + e * B * ‖φ‖ ^ 2) :
    energyDensity e v B a b φ =
      (B + e * (v ^ 2 - ‖φ‖ ^ 2)) ^ 2 / 2 + ‖a - I * b‖ ^ 2 - e * v ^ 2 * B - K := by
  unfold energyDensity
  rw [normSq_sum_eq_minus, hK]
  ring

/-- The density is bounded below by `e v² B + K` (positive sign). -/
theorem energyDensity_ge_plus (e v B K : ℝ) (a b φ : ℂ)
    (hK : 2 * (conj a * b).im = K + e * B * ‖φ‖ ^ 2) :
    e * v ^ 2 * B + K ≤ energyDensity e v B a b φ := by
  rw [energyDensity_eq_plus e v B K a b φ hK]
  nlinarith [sq_nonneg (B - e * (v ^ 2 - ‖φ‖ ^ 2)), sq_nonneg ‖a + I * b‖]

/-- The density is bounded below by `-(e v² B + K)` (negative sign). -/
theorem energyDensity_ge_minus (e v B K : ℝ) (a b φ : ℂ)
    (hK : 2 * (conj a * b).im = K + e * B * ‖φ‖ ^ 2) :
    -(e * v ^ 2 * B + K) ≤ energyDensity e v B a b φ := by
  rw [energyDensity_eq_minus e v B K a b φ hK]
  nlinarith [sq_nonneg (B + e * (v ^ 2 - ‖φ‖ ^ 2)), sq_nonneg ‖a - I * b‖]

end Lightlike.Rows.G1_047
