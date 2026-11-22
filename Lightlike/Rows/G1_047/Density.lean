import Mathlib

/-!
# Abelian-Higgs energy density and the pointwise Bogomolny identity (CO24)

Conventions (those of Hindmarsh–Kibble, `hindmarsh-kibble-1995`, Lagrangian
`|D φ|² − ¼F² − (λ/4)(|φ|²−η²)²`, with `D_j = ∂_j − i e A_j`; the equation number of the
Lagrangian is not checked here): a static configuration on `ℝ²` is a complex scalar `φ` and a real
gauge potential `(A₁, A₂)`, with magnetic field `B = ∂₁A₂ − ∂₂A₁`. Its energy density is
`½B² + |D₁φ|² + |D₂φ|² + (λ/4)(|φ|²−v²)²`.

This file is the algebraic (pointwise) half of the Bogomolny argument, in terms of the values at one
point of `D₁φ, D₂φ ∈ ℂ`, `φ ∈ ℂ` and `B ∈ ℝ`. At **critical coupling** `λ = 2e²`:

`density = ½(B ± e(|φ|²−v²))² + |D₁φ ± i D₂φ|² ± (e v² B + curlJ)`,

where `curlJ = 2 Im(conj(D₁φ) D₂φ) − e B |φ|²` is, for a configuration, the curl of the current
`J_j = Im(conj φ · D_jφ)` (proved in a later file of this row). Integrating, `∫ curlJ` is a boundary
term and `∫ B = 2πn/e`, which gives `E ≥ 2π|n|v²`.

## Main results

* `energyDensity`, `curlJ`: the density and the current-curl expression.
* `bogomolny_pointwise_plus`, `bogomolny_pointwise_minus`: the two completions of the square.
* `energyDensity_ge_plus`, `energyDensity_ge_minus`: the density bounds `±(e v² B + curlJ)`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex

/-- The covariant derivative `D_jφ = ∂_jφ − i e A_j φ` at a point, from the values `dφ = ∂_jφ`,
`a = A_j`, `φ`. -/
def covD (e a : ℝ) (dφ φ : ℂ) : ℂ := dφ - I * ((e * a : ℝ) : ℂ) * φ

/-- The energy density of the Abelian-Higgs model at a point:
`½B² + |D₁φ|² + |D₂φ|² + (λ/4)(|φ|²−v²)²`. -/
def energyDensity (lam v B : ℝ) (φ D₁ D₂ : ℂ) : ℝ :=
  B ^ 2 / 2 + (normSq D₁ + normSq D₂) + lam / 4 * (normSq φ - v ^ 2) ^ 2

/-- The pointwise expression `2 Im(conj D₁ · D₂) − e B |φ|²`, equal to the curl of the current
`J_j = Im(conj φ · D_jφ)` for a configuration. -/
def curlJ (e B : ℝ) (φ D₁ D₂ : ℂ) : ℝ :=
  2 * ((starRingEnd ℂ) D₁ * D₂).im - e * B * normSq φ

lemma normSq_add_I_mul (D₁ D₂ : ℂ) :
    normSq (D₁ + I * D₂) = normSq D₁ + normSq D₂ - 2 * ((starRingEnd ℂ) D₁ * D₂).im := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, I_re, I_im, conj_re, conj_im]
  ring

lemma normSq_sub_I_mul (D₁ D₂ : ℂ) :
    normSq (D₁ - I * D₂) = normSq D₁ + normSq D₂ + 2 * ((starRingEnd ℂ) D₁ * D₂).im := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, I_re, I_im, conj_re, conj_im]
  ring

/-- **Bogomolny identity, pointwise, upper sign**, at critical coupling `λ = 2e²`. -/
theorem bogomolny_pointwise_plus (e v B : ℝ) (φ D₁ D₂ : ℂ) :
    energyDensity (2 * e ^ 2) v B φ D₁ D₂ =
      (B + e * (normSq φ - v ^ 2)) ^ 2 / 2 + normSq (D₁ + I * D₂) +
        (e * v ^ 2 * B + curlJ e B φ D₁ D₂) := by
  rw [normSq_add_I_mul]
  simp only [energyDensity, curlJ]
  ring

/-- **Bogomolny identity, pointwise, lower sign**, at critical coupling `λ = 2e²`. -/
theorem bogomolny_pointwise_minus (e v B : ℝ) (φ D₁ D₂ : ℂ) :
    energyDensity (2 * e ^ 2) v B φ D₁ D₂ =
      (B - e * (normSq φ - v ^ 2)) ^ 2 / 2 + normSq (D₁ - I * D₂) -
        (e * v ^ 2 * B + curlJ e B φ D₁ D₂) := by
  rw [normSq_sub_I_mul]
  simp only [energyDensity, curlJ]
  ring

/-- The density dominates `e v² B + curlJ` at critical coupling. -/
theorem energyDensity_ge_plus (e v B : ℝ) (φ D₁ D₂ : ℂ) :
    e * v ^ 2 * B + curlJ e B φ D₁ D₂ ≤ energyDensity (2 * e ^ 2) v B φ D₁ D₂ := by
  rw [bogomolny_pointwise_plus]
  have := normSq_nonneg (D₁ + I * D₂)
  have := sq_nonneg (B + e * (normSq φ - v ^ 2))
  linarith

/-- The density dominates `−(e v² B + curlJ)` at critical coupling. -/
theorem energyDensity_ge_minus (e v B : ℝ) (φ D₁ D₂ : ℂ) :
    -(e * v ^ 2 * B + curlJ e B φ D₁ D₂) ≤ energyDensity (2 * e ^ 2) v B φ D₁ D₂ := by
  rw [bogomolny_pointwise_minus]
  have := normSq_nonneg (D₁ - I * D₂)
  have := sq_nonneg (B - e * (normSq φ - v ^ 2))
  linarith

end Lightlike.Vortex
