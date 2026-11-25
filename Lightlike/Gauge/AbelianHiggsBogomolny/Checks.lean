import Mathlib
import Lightlike.Gauge.AbelianHiggsBogomolny.Decay

/-!
# Sanity checks for the Bogomolny bound (CO24)

* `bogoEnergy_vacuum`: the vacuum `φ ≡ v`, `A = 0` (winding number `n = 0`) has zero energy density,
  consistent with `2π|n|v² = 0`.
* `bogomolny_sign_flip_fails`, `bogomolny_wrong_square_fails`: flipping the sign of the boundary term,
  or the sign inside the square, breaks the pointwise identity of `bogomolny_pointwise_plus`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex

/-- The vacuum configuration (`φ ≡ v`, `A = 0`, winding number `0`) has zero energy density. -/
theorem bogoEnergy_vacuum (e v : ℝ) (p : ℝ × ℝ) :
    bogoEnergy e v (fun _ => 0) (fun _ => 0) (fun _ => (v : ℂ)) p = 0 := by
  simp [bogoEnergy, energyDensity, covD, sq]

/-- Flipping the sign of the boundary term `e v² B + curlJ` breaks the identity
(`φ = 0`, `D = 0`, `B = v = e = 1`). -/
theorem bogomolny_sign_flip_fails :
    ¬ ∀ (e v B : ℝ) (φ D₁ D₂ : ℂ), energyDensity (2 * e ^ 2) v B φ D₁ D₂ =
      (B + e * (normSq φ - v ^ 2)) ^ 2 / 2 + normSq (D₁ + I * D₂) -
        (e * v ^ 2 * B + curlJ e B φ D₁ D₂) := by
  intro h
  have := h 1 1 1 0 0 0
  norm_num [energyDensity, curlJ] at this

/-- Flipping the sign of `B` relative to `e(|φ|²−v²)` in the square (keeping the plus-sign
boundary term) breaks the identity. -/
theorem bogomolny_wrong_square_fails :
    ¬ ∀ (e v B : ℝ) (φ D₁ D₂ : ℂ), energyDensity (2 * e ^ 2) v B φ D₁ D₂ =
      (B - e * (normSq φ - v ^ 2)) ^ 2 / 2 + normSq (D₁ + I * D₂) +
        (e * v ^ 2 * B + curlJ e B φ D₁ D₂) := by
  intro h
  have := h 1 1 1 0 0 0
  norm_num [energyDensity, curlJ] at this

end Lightlike.Vortex
