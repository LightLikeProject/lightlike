import Mathlib
import Lightlike.Rows.G1_032.Linearized

/-!
# Jeans wavenumber (row G1-032)

`jeansWavenumberSq ρ G cs = 4πGρ/c_s²`. On a mode with `Δδ = -k² δ`, `growth_equation` becomes
`d'' + 2H d' + c_s² (k²/a² - k_J²) d = 0`; the sign of the bracket is the Jeans criterion
(Bernardeau et al. 2002, Section 2.3, source key `bernardeau-2002`).
-/

namespace Lightlike.Rows.G1_032

/-- Squared Jeans wavenumber `k_J² = 4πGρ/c_s²`. -/
noncomputable def jeansWavenumberSq (ρ G cs : ℝ) : ℝ := 4 * Real.pi * G * ρ / cs ^ 2

lemma cs_sq_mul_jeans {ρ G cs : ℝ} (hcs : cs ≠ 0) :
    cs ^ 2 * jeansWavenumberSq ρ G cs = 4 * Real.pi * G * ρ := by
  unfold jeansWavenumberSq
  field_simp

/-- **Growth of a Fourier mode with pressure.** If the linearized Euler–Poisson system holds and
`δ(t, ·)` is an eigenfunction of the comoving Laplacian, `Δδ(s, x) = -k² δ(s, x)` for all `s`,
then `d(s) = δ(s, x)` satisfies `d'' + 2Hd' + c_s²(k²/a² - k_J²) d = 0` at `t`
(with `k_J² = 4πGρ/c_s²`, `c_s ≠ 0`). -/
theorem growth_equation_mode {a ρ : ℝ → ℝ} {G cs k2 : ℝ} {δ φ : ℝ × Space → ℝ}
    {u : Fin 3 → ℝ × Space → ℝ} (hsys : LinearizedEulerPoisson a ρ G cs δ φ u)
    (ha : ContDiff ℝ 2 a) (ha0 : ∀ t, a t ≠ 0)
    (hδ : ContDiff ℝ 2 δ) (hφ : ContDiff ℝ 2 φ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (hcs : cs ≠ 0) (t : ℝ) (x : Space) (hk : lap δ (t, x) = -k2 * δ (t, x)) :
    deriv (deriv fun s => δ (s, x)) t + 2 * (deriv a t / a t) * deriv (fun s => δ (s, x)) t
      + cs ^ 2 * (k2 / a t ^ 2 - jeansWavenumberSq (ρ t) G cs) * δ (t, x) = 0 := by
  have h := growth_equation hsys ha ha0 hδ hφ hu t x
  rw [hk] at h
  have h2 := cs_sq_mul_jeans (ρ := ρ t) (G := G) hcs
  have h3 : a t ^ 2 ≠ 0 := pow_ne_zero 2 (ha0 t)
  have h4 : cs ^ 2 * (k2 / a t ^ 2 - jeansWavenumberSq (ρ t) G cs) * δ (t, x)
      = cs ^ 2 / a t ^ 2 * (-k2 * δ (t, x)) * (-1) - 4 * Real.pi * G * ρ t * δ (t, x) * (-1) *
        (-1) := by
    rw [mul_sub, h2]
    field_simp
  linarith

/-- **Jeans criterion.** For `c_s ≠ 0`, the coefficient `c_s²(k²/a² - k_J²)` of the mode equation
is negative (growing/decaying exponential regime) iff the physical wavenumber `k/a` is below
`k_J`, i.e. `k²/a² < k_J²`. -/
theorem jeans_coeff_neg_iff {ρ G cs k2 a : ℝ} (hcs : cs ≠ 0) :
    cs ^ 2 * (k2 / a ^ 2 - jeansWavenumberSq ρ G cs) < 0 ↔ k2 / a ^ 2 < jeansWavenumberSq ρ G cs := by
  have : 0 < cs ^ 2 := by positivity
  rw [mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨this, by linarith⟩

/-- Oscillatory regime: coefficient positive iff `k²/a² > k_J²`. -/
theorem jeans_coeff_pos_iff {ρ G cs k2 a : ℝ} (hcs : cs ≠ 0) :
    0 < cs ^ 2 * (k2 / a ^ 2 - jeansWavenumberSq ρ G cs) ↔ jeansWavenumberSq ρ G cs < k2 / a ^ 2 := by
  have : 0 < cs ^ 2 := by positivity
  rw [mul_pos_iff_of_pos_left this]
  exact sub_pos

/-- Static-background (`H = 0`, frozen `a`, `ρ`) model: for `k²/a² < k_J²`, `d(t) = exp(γ t)` with
`γ² = c_s²(k_J² - k²/a²)` solves `d'' + c_s²(k²/a² - k_J²) d = 0`: Jeans instability. -/
theorem jeans_exponential {ω2 γ : ℝ} (hγ : γ ^ 2 = -ω2) (t : ℝ) :
    deriv (deriv fun s : ℝ => Real.exp (γ * s)) t + ω2 * Real.exp (γ * t) = 0 := by
  have h1 : deriv (fun s : ℝ => Real.exp (γ * s)) = fun s => γ * Real.exp (γ * s) := by
    funext s
    have := ((hasDerivAt_id s).const_mul γ).exp
    simpa [mul_comm] using this.deriv
  rw [h1]
  have h2 : HasDerivAt (fun s : ℝ => γ * Real.exp (γ * s)) (γ * (Real.exp (γ * t) * γ)) t := by
    simpa using (((hasDerivAt_id t).const_mul γ).exp).const_mul γ
  rw [h2.deriv]
  have : γ * (Real.exp (γ * t) * γ) = γ ^ 2 * Real.exp (γ * t) := by ring
  rw [this, hγ]
  ring

end Lightlike.Rows.G1_032
