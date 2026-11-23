import Mathlib

/-!
# The cut-off zero-point energy scales as `Λ_c⁴`

The one-loop zero-point energy density of a free field of mass `m` with a hard momentum cut-off `Λ`
is `ρ = ∫_{|k| ≤ Λ} d³k/(2π)³ · ½ ω_k`, `ω_k = √(k² + m²)`. After the angular integration this is
`ρ(m, Λ) = (1/4π²) ∫₀^Λ k² √(k² + m²) dk`.

This is the quantity that Weinberg's no-go discussion (CO22) says one cannot adjust away without
tuning: it scales like `Λ⁴`.

## Main results

* `zeroPointDensity`: the cut-off integral `ρ(m, Λ)`.
* `zeroPointDensity_scaling`: `ρ(m, Λ) = Λ⁴ ρ(m/Λ, 1)` for `Λ > 0`.
* `zeroPointDensity_massless`: `ρ(0, Λ) = Λ⁴ / (16 π²)` for `Λ ≥ 0`.
* `zeroPointDensity_massless_scaling`: `ρ(0, Λ) = Λ⁴ ρ(0, 1)`.
-/

namespace Lightlike.Rows.G1_045

open intervalIntegral

/-- The integrand `k² √(k² + m²) / (4π²)` of the cut-off zero-point energy density. -/
noncomputable def zeroPointIntegrand (m k : ℝ) : ℝ :=
  k ^ 2 * Real.sqrt (k ^ 2 + m ^ 2) / (4 * Real.pi ^ 2)

/-- **Cut-off zero-point energy density** `ρ(m, Λ) = (1/4π²) ∫₀^Λ k² √(k² + m²) dk`, i.e.
`∫_{|k|≤Λ} d³k/(2π)³ · ½ √(k² + m²)`. -/
noncomputable def zeroPointDensity (m Λ : ℝ) : ℝ :=
  ∫ k in (0 : ℝ)..Λ, zeroPointIntegrand m k

/-- The integrand is homogeneous: `f_m(Λ u) = Λ³ f_{m/Λ}(u)` for `Λ > 0`, `u ≥ 0`. -/
theorem zeroPointIntegrand_mul {m Λ : ℝ} (hΛ : 0 < Λ) (u : ℝ) :
    zeroPointIntegrand m (Λ * u) = Λ ^ 3 * zeroPointIntegrand (m / Λ) u := by
  unfold zeroPointIntegrand
  have h : (Λ * u) ^ 2 + m ^ 2 = Λ ^ 2 * (u ^ 2 + (m / Λ) ^ 2) := by
    field_simp
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hΛ.le]
  ring

/-- **The cut-off zero-point energy scales as `Λ⁴`**: `ρ(m, Λ) = Λ⁴ ρ(m/Λ, 1)` for `Λ > 0`. -/
theorem zeroPointDensity_scaling {m Λ : ℝ} (hΛ : 0 < Λ) :
    zeroPointDensity m Λ = Λ ^ 4 * zeroPointDensity (m / Λ) 1 := by
  unfold zeroPointDensity
  have h := intervalIntegral.integral_comp_mul_left
    (a := (0 : ℝ)) (b := 1) (fun k => zeroPointIntegrand m k) hΛ.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at h
  have h2 : ∫ x in (0 : ℝ)..1, zeroPointIntegrand m (Λ * x)
      = Λ ^ 3 * ∫ x in (0 : ℝ)..1, zeroPointIntegrand (m / Λ) x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => zeroPointIntegrand_mul hΛ u)
  rw [h2] at h
  have : ∫ x in (0 : ℝ)..Λ, zeroPointIntegrand m x
      = Λ * (Λ ^ 3 * ∫ x in (0 : ℝ)..1, zeroPointIntegrand (m / Λ) x) := by
    rw [h]; field_simp
  rw [this]; ring

/-- Massless closed form: `ρ(0, Λ) = Λ⁴ / (16 π²)`. -/
theorem zeroPointDensity_massless (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    zeroPointDensity 0 Λ = Λ ^ 4 / (16 * Real.pi ^ 2) := by
  unfold zeroPointDensity zeroPointIntegrand
  have h : ∀ k ∈ Set.uIcc (0 : ℝ) Λ, k ^ 2 * Real.sqrt (k ^ 2 + 0 ^ 2) / (4 * Real.pi ^ 2)
      = (1 / (4 * Real.pi ^ 2)) * k ^ 3 := by
    intro k hk
    rw [Set.uIcc_of_le hΛ] at hk
    have hk0 : 0 ≤ k := hk.1
    have : Real.sqrt (k ^ 2 + 0 ^ 2) = k := by
      rw [show k ^ 2 + 0 ^ 2 = k ^ 2 by ring]; exact Real.sqrt_sq hk0
    rw [this]; ring
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul, integral_pow]
  field_simp
  ring

/-- For a massless field the scaling is exact: `ρ(0, Λ) = Λ⁴ ρ(0, 1)`. -/
theorem zeroPointDensity_massless_scaling {Λ : ℝ} (hΛ : 0 < Λ) :
    zeroPointDensity 0 Λ = Λ ^ 4 * zeroPointDensity 0 1 := by
  rw [zeroPointDensity_massless Λ hΛ.le, zeroPointDensity_massless 1 zero_le_one]
  ring

end Lightlike.Rows.G1_045
