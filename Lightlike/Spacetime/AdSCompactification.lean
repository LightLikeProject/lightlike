import Mathlib

/-!
# Anti-de Sitter space is conformal to half of the Einstein static universe (G1-016)

In the global coordinates of anti-de Sitter space, `ds² = -(1 + r²) dτ² + (1 + r²)⁻¹ dr² + r² dΩ²`, the conformal radial
coordinate `θ` with `r = tan θ` gives `ds² = cos⁻² θ (-dτ² + dθ² + sin² θ dΩ²)`: AdS is conformal to the region
`0 ≤ θ < π/2` of the Einstein static universe, and its conformal boundary `θ = π/2`, where `cos θ = 0`, carries the
timelike metric `-dτ² + dΩ²`.

* `ads_eq_conformal_esu`: the pullback identity (`dr = dθ / cos² θ`, Mathlib's `Real.hasDerivAt_tan`);
* `bijOn_tan_ads`: `θ ↦ tan θ` maps `[0, π/2)` bijectively onto `[0, ∞)`;
* `cos_eq_zero_ads_boundary`: on `[0, π/2]` the conformal factor `cos θ` vanishes exactly at `θ = π/2`, and
  `ads_boundary_metric`: there the conformal metric is `-dτ² + dΩ²`, of Lorentzian signature.

## References

* M. Blau, *Lecture Notes on General Relativity* (version of 15 November 2026,
  http://www.blau.itp.unibe.ch/newlecturesGR.pdf), section 39.3, eq. (39.76), p. 927, and section 39.3.2,
  eqs. (39.79)–(39.86), pp. 927–929: the conformal radial coordinate `cosh ρ = 1/cos θ`, `sinh ρ = tan θ`, the metric
  `cos⁻² θ (-dτ² + dθ² + sin² θ dΩ²)`, "AdS is conformal to one half of the Einstein static universe", the conformal
  boundary `θ = π/2`, "timelike", `ds̃²|_{θ = π/2} = -dτ² + dΩ²`.
-/

noncomputable section

namespace Lightlike

open Real Set

/-- **The AdS metric in the conformal radial coordinate** (Blau (39.84)): with `r = tan θ`, for a tangent vector
`a ∂_τ + b ∂_θ + w` (`w` tangent to the sphere, `q = dΩ²(w, w)`), the metric `-(1 + r²) dτ² + (1 + r²)⁻¹ dr² + r² dΩ²`
evaluated on it (`dr = b / cos² θ`) is `cos⁻² θ (-a² + b² + sin² θ q)`. -/
theorem ads_eq_conformal_esu {θ : ℝ} (h : cos θ ≠ 0) (a b q : ℝ) :
    -(1 + tan θ ^ 2) * a ^ 2 + (1 + tan θ ^ 2)⁻¹ * (1 / cos θ ^ 2 * b) ^ 2 + tan θ ^ 2 * q =
      (cos θ ^ 2)⁻¹ * (-a ^ 2 + b ^ 2 + sin θ ^ 2 * q) := by
  have h1 : 1 + tan θ ^ 2 = (cos θ ^ 2)⁻¹ := by
    rw [tan_eq_sin_div_cos]; field_simp; linear_combination sin_sq_add_cos_sq θ
  rw [h1, tan_eq_sin_div_cos]
  field_simp

/-- `θ ↦ tan θ` maps `[0, π/2)` bijectively onto `[0, ∞)` (`r = tan θ`, Blau (39.82)–(39.83)). -/
theorem bijOn_tan_ads : BijOn tan (Ico 0 (π / 2)) (Ici 0) := by
  refine ⟨fun θ hθ => ?_, fun θ hθ θ' hθ' he => ?_, fun r hr => ?_⟩
  · have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
    have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])
    rw [mem_Ici, tan_eq_sin_div_cos]
    exact div_nonneg hs hc.le
  · exact injOn_tan ⟨by linarith [hθ.1, pi_pos], hθ.2⟩ ⟨by linarith [hθ'.1, pi_pos], hθ'.2⟩ he
  · refine ⟨arctan r, ⟨?_, arctan_lt_pi_div_two r⟩, tan_arctan r⟩
    rw [← arctan_zero]; exact arctan_strictMono.monotone hr

/-- **The conformal boundary of AdS** (Blau (39.85)–(39.86)): on `[0, π/2]` the conformal factor `cos θ` vanishes
exactly at `θ = π/2`. -/
theorem cos_eq_zero_ads_boundary {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2) : cos θ = 0 ↔ θ = π / 2 := by
  constructor
  · intro hc
    rcases lt_or_eq_of_le h1 with hlt | heq
    · exact absurd hc (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩).ne'
    · exact heq
  · rintro rfl; exact cos_pi_div_two

/-- **The conformal boundary is timelike** (Blau (39.86)): at `θ = π/2` the conformal metric `-dτ² + dθ² + sin² θ dΩ²`
restricted to the boundary (`b = 0`) is `-dτ² + dΩ²`, negative on `∂_τ` and nonnegative on the sphere directions. -/
theorem ads_boundary_metric (a q : ℝ) : -a ^ 2 + (0 : ℝ) ^ 2 + sin (π / 2) ^ 2 * q = -a ^ 2 + q := by
  rw [sin_pi_div_two]; ring

end Lightlike
