import Lightlike.Gauge.AbelianHiggsBogomolny.Winding

/-!
# The Bogomolny bound `E ≥ 2π |n| v²` (CO24)

Combining Green's theorem (`box_integral_bogoTerm`), the pointwise Bogomolny inequality
(`box_energy_ge_plus/minus`) and the limit of the boundary integral at infinity
(`bdy_Wfield_tendsto`), the energy of a configuration at critical coupling `λ = 2e²` is bounded
below by `2π |n| v²`, `n` the winding number of the Higgs field at infinity.

## Main results

* `bogomolny_bound`: if all box energies are `≤ E`, then `2π |n| v² ≤ E`.
-/

noncomputable section
namespace Lightlike.Vortex

open Complex MeasureTheory Set

/-- The boundary integral of `W` is the box integral of `bogoTerm` over `[−R, R]²`. -/
theorem box_bogoTerm_eq_bdy (e v : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂) (R : ℝ) :
    (∫ x in (-R)..R, ∫ y in (-R)..R, bogoTerm e v A₁ A₂ φ (x, y)) =
      bdy (Wfield e v A₁ φ (1, 0)) (Wfield e v A₂ φ (0, 1)) R :=
  box_integral_bogoTerm e v hφ hA₁ hA₂ (-R) R (-R) R

/-- **Bogomolny bound (CO24).** Let `(φ, A₁, A₂)` be a configuration with `φ ∈ C²`,
`A_j ∈ C¹`, such that `φ ≠ 0` near infinity, `‖p‖ · |errTerm| → 0` at infinity (the decay of
`e A (v² − |φ|²)` and `(|φ|² − v²) dθ`), the winding number of `φ` on large squares is `n`
(`∮ dθ = 2π n`), and the energy in every square `[−R, R]²` at critical coupling `λ = 2e²` is
at most `E`. Then `2π |n| v² ≤ E`. -/
theorem bogomolny_bound (e v : ℝ) (n : ℤ) (E : ℝ) {A₁ A₂ : ℝ × ℝ → ℝ} {φ : ℝ × ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hA₁ : ContDiff ℝ 1 A₁) (hA₂ : ContDiff ℝ 1 A₂)
    (hne : ∃ R₀ : ℝ, ∀ p : ℝ × ℝ, R₀ ≤ ‖p‖ → φ p ≠ 0)
    (h₁ : Filter.Tendsto (fun p : ℝ × ℝ => ‖p‖ * |errTerm e v A₁ φ (1, 0) p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (h₂ : Filter.Tendsto (fun p : ℝ × ℝ => ‖p‖ * |errTerm e v A₂ φ (0, 1) p|)
      (Bornology.cobounded (ℝ × ℝ)) (nhds 0))
    (hw : ∀ᶠ R in Filter.atTop,
      bdy (windingForm φ (1, 0)) (windingForm φ (0, 1)) R = 2 * Real.pi * n)
    (hE : ∀ R : ℝ, 0 ≤ R →
      (∫ x in (-R)..R, ∫ y in (-R)..R, bogoEnergy e v A₁ A₂ φ (x, y)) ≤ E) :
    2 * Real.pi * |(n : ℝ)| * v ^ 2 ≤ E := by
  have T := bdy_Wfield_tendsto e v n (hφ.of_le (by norm_num)) hA₁.continuous hA₂.continuous
    hne h₁ h₂ hw
  have hev : ∀ᶠ R : ℝ in Filter.atTop, 0 ≤ R := Filter.eventually_ge_atTop 0
  have up : 2 * Real.pi * n * v ^ 2 ≤ E := by
    refine le_of_tendsto T ?_
    filter_upwards [hev] with R hR
    rw [← box_bogoTerm_eq_bdy e v hφ hA₁ hA₂ R]
    exact (box_energy_ge_plus e v hφ hA₁ hA₂ (by linarith) (by linarith)).trans (hE R hR)
  have lo : -(2 * Real.pi * n * v ^ 2) ≤ E := by
    refine le_of_tendsto T.neg ?_
    filter_upwards [hev] with R hR
    rw [← box_bogoTerm_eq_bdy e v hφ hA₁ hA₂ R]
    exact (box_energy_ge_minus e v hφ hA₁ hA₂ (by linarith) (by linarith)).trans (hE R hR)
  have habs : |2 * Real.pi * n * v ^ 2| ≤ E := abs_le.mpr ⟨by linarith, up⟩
  have : |2 * Real.pi * n * v ^ 2| = 2 * Real.pi * |(n : ℝ)| * v ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2),
      abs_of_nonneg (sq_nonneg v)]
  linarith

end Lightlike.Vortex
