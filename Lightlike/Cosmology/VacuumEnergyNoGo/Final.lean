import Mathlib
import Lightlike.Cosmology.VacuumEnergyNoGo.Example
import Lightlike.Cosmology.VacuumEnergyNoGo.CutOff

/-!
# Weinberg's no-go theorem for the vacuum energy (T-CO22): bundled statement

Under Lorentz (Poincaré) invariance of the vacuum the stress tensor of a constant-field vacuum is
`-V(φ) g` (compare `cosmoT`), so the vacuum energy density is `V φ` at a stationary point `φ` of
the potential `V`. Weinberg's argument (1989, own formulation; the source text
`padilla-2015, Section 3.2` is only a table of contents here) is:

* a field-independent constant added to `V` moves every vacuum energy by that constant and does not
  move the vacua (`Shift`), so it cannot cancel the energies of two vacua of different energy;
* if `V` is scale covariant of degree `≠ 0` (the one-loop zero-point energy of a classically
  scale-invariant theory, cut off at `Λ_c`, is `Λ_c⁴ ρ(m/Λ_c, 1)`, see `CutOff`) the vacuum energy
  vanishes at every vacuum (`Scale`), but that is a statement about the vacua of a scale-invariant
  potential and requires a flat direction through the vacuum, i.e. a tuning of the free parameters
  (`Example`); adding a non-zero constant destroys the covariance.

## Main results

* `weinberg_no_go`: the hypotheses (scale covariance of non-zero degree, stationarity) and the
  conclusion, with the failure of the shifted potential.
* `weinberg_no_go_example`: the explicit scale-invariant example with two free parameters `a, b`:
  a vacuum off the origin exists iff `a = b`; the hypotheses are necessary
  (`shifted_vacuum_energy_ne_zero`, `not_vacuum_energy_ne_zero`).
* `weinberg_cutoff_scaling`: the cut-off zero-point density scales as `Λ_c⁴`.
-/

namespace Lightlike.Cosmology.VacuumEnergyNoGo

/-- **Weinberg's no-go theorem.** Let `V` be a scale-covariant potential of degree `deg ≠ 0` on the
constant fields `ι → ℝ`. Then

1. every vacuum (differentiable stationary point) has vanishing vacuum energy;
2. a field-independent constant `c` added to `V` keeps the vacua and shifts each vacuum energy to
   `V φ + c = c`, so for `c ≠ 0` the adjusted theory has no vacuum of zero energy among the vacua
   of `V`, and the adjusted potential is no longer scale covariant of degree `deg`;
3. consequently a scale-covariant adjusted potential `V + c` has `c = 0`: the cancellation is not
   a field-independent adjustment, it is the covariance of `V` itself (which for the explicit
   example requires `a = b`, see `weinberg_no_go_example`). -/
theorem weinberg_no_go {ι : Type*} [Fintype ι] {V : (ι → ℝ) → ℝ} {d : ι → ℝ} {deg : ℝ}
    (hV : ScaleCovariant V d deg) (hdeg : deg ≠ 0) :
    (∀ φ, IsVacuum V φ → vacuumEnergy V φ = 0) ∧
    (∀ c : ℝ, c ≠ 0 → ∀ φ, IsVacuum V φ →
        IsVacuum (shiftPot V c) φ ∧ vacuumEnergy (shiftPot V c) φ = c) ∧
    (∀ c : ℝ, c ≠ 0 → ¬ ScaleCovariant (shiftPot V c) d deg) ∧
    (∀ c : ℝ, ScaleCovariant (shiftPot V c) d deg → c = 0) := by
  refine ⟨fun φ hφ => weinberg_vanish hV hdeg hφ, ?_, fun c hc => not_scaleCovariant_shift hV hdeg hc,
    ?_⟩
  · intro c _ φ hφ
    refine ⟨(isVacuum_add_const V c φ).mpr hφ, ?_⟩
    rw [vacuumEnergy_add_const, weinberg_vanish hV hdeg hφ, zero_add]
  · intro c hc
    by_contra hne
    exact not_scaleCovariant_shift hV hdeg hne hc

/-- **The scale-invariant example is tuned.** For `V_{a,b}(x₀, x₁) = (x₀ - a x₁²)² + (x₀ - b x₁²)²`
(`exampleV`, weights `(2, 1)`, degree `4`): it is scale covariant for all `a, b`; a vacuum
with `x₁ ≠ 0` exists iff `a = b`; for `a ≠ b` the only vacuum is the origin; and both hypotheses
of Weinberg's argument are needed (a shifted potential has a vacuum of non-zero energy, and a
non-stationary point has non-zero potential). -/
theorem weinberg_no_go_example (a b : ℝ) :
    ScaleCovariant (exampleV a b) exampleWeights 4 ∧
    ((∃ x : Fin 2 → ℝ, IsVacuum (exampleV a b) x ∧ x 1 ≠ 0) ↔ a = b) ∧
    (a ≠ b → ∀ x, IsVacuum (exampleV a b) x → x = 0) ∧
    (∀ c : ℝ, c ≠ 0 → IsVacuum (shiftPot (exampleV a b) c) 0 ∧
        vacuumEnergy (shiftPot (exampleV a b) c) 0 ≠ 0) ∧
    (exampleV a b ![1, 0] ≠ 0 ∧ ¬ IsVacuum (exampleV a b) ![1, 0]) :=
  ⟨exampleV_scaleCovariant a b, exists_flat_vacuum_iff a b,
    fun hab _ hx => vacuum_eq_zero_of_ne hab hx,
    fun _ hc => shifted_vacuum_energy_ne_zero a b hc, not_vacuum_energy_ne_zero a b⟩

/-- **The cut-off zero-point energy scales as `Λ_c⁴`**: `ρ(m, Λ_c) = Λ_c⁴ ρ(m/Λ_c, 1)`; for a
massless field `ρ(0, Λ_c) = Λ_c⁴ / (16 π²)`. -/
theorem weinberg_cutoff_scaling {m Λ : ℝ} (hΛ : 0 < Λ) :
    zeroPointDensity m Λ = Λ ^ 4 * zeroPointDensity (m / Λ) 1 ∧
    zeroPointDensity 0 Λ = Λ ^ 4 / (16 * Real.pi ^ 2) :=
  ⟨zeroPointDensity_scaling hΛ, zeroPointDensity_massless Λ hΛ.le⟩

end Lightlike.Cosmology.VacuumEnergyNoGo

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.weinberg_cutoff_scaling := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.weinberg_cutoff_scaling
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.weinberg_no_go := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.weinberg_no_go
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.weinberg_no_go_example := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.weinberg_no_go_example
