module

public import Lightlike.Cosmology.FLRW

/-!
# The Sachs–Wolfe effect in matter domination

The large-scale temperature anisotropy of the cosmic microwave background in a spatially flat FLRW
universe filled with dust, in Newtonian gauge,
`ds² = a² [-(1 + 2Ψ) dτ² + (1 - 2Φ) dx²]`, is `ΔT/T = Θ₀ + Ψ` at last scattering (the intrinsic
temperature fluctuation plus the gravitational redshift), with the Doppler and the integrated
terms dropped. This file proves, from Friedmann's first equation and the linearized `00` Einstein
equation, that on super-horizon scales in matter domination (`Φ' = 0`, `Ψ = Φ`)

* the adiabatic condition gives `Θ₀ = δ_m / 3` (`SachsWolfe.intrinsic_eq_third`),
* the `00` equation gives `δ_m = -2 Φ` (`SachsWolfe.delta_eq_neg_two_mul`),
* hence `ΔT/T = Φ / 3` (`SachsWolfe.sachsWolfe`),
* and without the intrinsic term the factor `1/3` becomes `1` (`SachsWolfe.without_intrinsic`).

The perturbation equations are taken as hypotheses in the stated form; the full Boltzmann hierarchy
and the free streaming of photons from last scattering are not formalized.

**References.** `baumann-2009`, Section 17.1.2 (`docs/tasks/sources.yaml`, milestone CO12).
-/

@[expose] public section

noncomputable section

namespace Lightlike

namespace Cosmology

namespace SachsWolfe

/-- The conformal Hubble rate `𝓗 = a H = a'/a` (with `'` the conformal-time derivative), written
with cosmic time `t`: `a(t) · (da/dt / a)`. -/
def conformalHubble (a : ℝ → ℝ) (t : ℝ) : ℝ := a t * (deriv a t / a t)

/-- The `00` Einstein equation of the linearized metric in Newtonian gauge, for dust of density
`ρ` and contrast `δ`, in Fourier space with wavenumber `k`:
`k² Φ + 3𝓗 (Φ' + 𝓗 Ψ) = -4πG a² ρ δ`. Here `Φ'` is passed as a number `dΦ`. -/
def Einstein00 (Gn a ρ 𝓗 k Φ dΦ Ψ δ : ℝ) : Prop :=
  k ^ 2 * Φ + 3 * 𝓗 * (dΦ + 𝓗 * Ψ) = -(4 * Real.pi * Gn * a ^ 2 * ρ * δ)

/-- The temperature anisotropy of the Sachs–Wolfe effect: the intrinsic fluctuation `Θ₀` at last
scattering plus the gravitational redshift `Ψ` out of the potential well. -/
def swAnisotropy (Θ₀ Ψ : ℝ) : ℝ := Θ₀ + Ψ

/-- Friedmann's first equation for `k = 0`, `Λ = 0` in conformal form:
`𝓗² = (8πG/3) a² ρ` (also true where `a = 0`, as division by zero is zero). -/
theorem conformalFriedmann {a ρ : ℝ → ℝ} {Gn t : ℝ}
    (h : FirstFriedmann a ρ 0 0 Gn t) :
    conformalHubble a t ^ 2 = 8 * Real.pi * Gn / 3 * a t ^ 2 * ρ t := by
  unfold FirstFriedmann at h
  unfold conformalHubble
  have h2 : (a t * (deriv a t / a t)) ^ 2 = a t ^ 2 * (deriv a t / a t) ^ 2 := by ring
  rw [h2, h]
  simp
  ring

/-- Adiabatic perturbations, linearized: in a one-parameter family of perturbations with
`n_m ∝ ρ_m` and `n_γ ∝ T³`, the adiabatic condition `n_m/n_γ = const` reads
`1 + δ(ε) = (1 + Θ(ε))³`, and then `δ' (0) = 3 Θ'(0)`: `δ_m = 3 Θ₀` to first order. -/
theorem intrinsic_eq_third {Θ δ : ℝ → ℝ} {Θ' : ℝ} (h0 : Θ 0 = 0)
    (hΘ : HasDerivAt Θ Θ' 0) (had : ∀ ε, 1 + δ ε = (1 + Θ ε) ^ 3) :
    HasDerivAt δ (3 * Θ') 0 := by
  have hδ : δ = fun ε => (1 + Θ ε) ^ 3 - 1 := by
    funext ε; linarith [had ε]
  rw [hδ]
  have h1 : HasDerivAt (fun ε => 1 + Θ ε) Θ' 0 := by
    simpa using hΘ.const_add 1
  have h2 := (h1.pow 3).sub_const 1
  convert h2 using 1
  simp [h0]

/-- First-order form: `Θ₀ = δ_m / 3`, from the derivative statement. -/
theorem intrinsic_eq_third' {δ₁ Θ₁ : ℝ} (h : δ₁ = 3 * Θ₁) : Θ₁ = δ₁ / 3 := by
  linarith

/-- On super-horizon scales (`k = 0`) in matter domination (`Φ' = 0`, `Ψ = Φ`, `𝓗 ≠ 0`), the `00`
Einstein equation together with Friedmann's first equation gives `δ_m = -2Φ`. -/
theorem delta_eq_neg_two_mul {Gn a ρ 𝓗 Φ δ : ℝ} (h𝓗 : 𝓗 ≠ 0)
    (hF : 𝓗 ^ 2 = 8 * Real.pi * Gn / 3 * a ^ 2 * ρ)
    (hE : Einstein00 Gn a ρ 𝓗 0 Φ 0 Φ δ) : δ = -2 * Φ := by
  unfold Einstein00 at hE
  have h4 : 4 * Real.pi * Gn * a ^ 2 * ρ = 3 / 2 * 𝓗 ^ 2 := by rw [hF]; ring
  rw [mul_assoc (4 * Real.pi * Gn * a ^ 2) ρ δ] at hE
  have : 3 * 𝓗 ^ 2 * Φ = -(3 / 2 * 𝓗 ^ 2 * δ) := by
    have e : 4 * Real.pi * Gn * a ^ 2 * (ρ * δ) = (4 * Real.pi * Gn * a ^ 2 * ρ) * δ := by ring
    rw [e, h4] at hE
    nlinarith [hE]
  have hne : 𝓗 ^ 2 ≠ 0 := pow_ne_zero 2 h𝓗
  have : 𝓗 ^ 2 * (3 * Φ + 3 / 2 * δ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hne
  · linarith

/-- **The Sachs–Wolfe effect.** On super-horizon scales in matter domination,
`ΔT/T = Θ₀ + Ψ = Φ/3` when `Θ₀ = δ_m/3` (adiabatic) and `δ_m = -2Φ`. -/
theorem sachsWolfe {Θ₀ δ Φ : ℝ} (hΘ : Θ₀ = δ / 3) (hδ : δ = -2 * Φ) :
    swAnisotropy Θ₀ Φ = Φ / 3 := by
  unfold swAnisotropy
  rw [hΘ, hδ]
  ring

/-- Without the intrinsic-temperature term the anisotropy is `Ψ = Φ`: the `1/3` becomes `1`. -/
theorem without_intrinsic (Φ : ℝ) : swAnisotropy 0 Φ = 1 * Φ := by
  unfold swAnisotropy; ring

/-- The intrinsic term matters: for `Φ ≠ 0` the two anisotropies differ. -/
theorem sachsWolfe_ne_without_intrinsic {Φ : ℝ} (h : Φ ≠ 0) :
    swAnisotropy (-2 * Φ / 3) Φ ≠ swAnisotropy 0 Φ := by
  unfold swAnisotropy
  intro h'
  apply h
  linarith

/-- **The Sachs–Wolfe effect, end to end.** In a spatially flat, `Λ = 0` FLRW background obeying
Friedmann's first equation at time `t` with `𝓗 ≠ 0`, take a one-parameter family of adiabatic
perturbations (`1 + δ(ε) = (1 + Θ(ε))³`, `Θ(0) = 0`) whose first-order values are `Θ₁ = Θ₀` and
`δ₁ = δ_m`. If on super-horizon scales (`k = 0`) in matter domination (`Φ' = 0`, `Ψ = Φ`) the `00`
Einstein equation holds, then `ΔT/T = Θ₀ + Ψ = Φ/3`. -/
theorem sachsWolfe_flrw {a ρ Θ δ : ℝ → ℝ} {Gn t Φ Θ₁ δ₁ : ℝ}
    (hF : FirstFriedmann a ρ 0 0 Gn t) (h𝓗 : conformalHubble a t ≠ 0)
    (hE : Einstein00 Gn (a t) (ρ t) (conformalHubble a t) 0 Φ 0 Φ δ₁)
    (h0 : Θ 0 = 0) (hΘ : HasDerivAt Θ Θ₁ 0) (hδ : HasDerivAt δ δ₁ 0)
    (had : ∀ ε, 1 + δ ε = (1 + Θ ε) ^ 3) :
    swAnisotropy Θ₁ Φ = Φ / 3 := by
  have h1 : δ₁ = 3 * Θ₁ := hδ.unique (intrinsic_eq_third h0 hΘ had)
  exact sachsWolfe (intrinsic_eq_third' h1)
    (delta_eq_neg_two_mul h𝓗 (conformalFriedmann hF) hE)

end SachsWolfe

end Cosmology

end Lightlike
