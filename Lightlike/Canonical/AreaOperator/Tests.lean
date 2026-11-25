import Lightlike.Canonical.AreaOperator.Casimir

/-!
# Non-vacuity tests for the area operator (row G2-012)

The theorems of `Area.lean`, `Spectrum.lean` and `Casimir.lean` are stated for an arbitrary
probability Haar measure `μ` on `SU(2)`.  Here we instantiate `μ` with the normalised Haar measure
`Measure.haarMeasure ⊤` (which satisfies the hypotheses), and check the specific numbers: the area
gap for `γ = ℓ = 1`, the eigenvalue of one spin-`1/2` puncture, and that the true spectrum separates
one spin-`1` puncture from two spin-`1/2` punctures while the `j`-model does not.
-/

open MeasureTheory MeasureTheory.Measure TopologicalSpace Lightlike.HarmonicAnalysis

namespace Lightlike.Canonical.AreaOperator.Tests

open Lightlike.Canonical.AreaOperator

/-- The normalised Haar measure on `SU(2)`. -/
noncomputable abbrev μ₀ : Measure SU2 := Measure.haarMeasure (⊤ : PositiveCompacts SU2)

instance : IsProbabilityMeasure μ₀ :=
  ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts SU2))⟩

/-- The area gap for `γ = ℓ = 1` is `4 √3 π`. -/
example : areaGap 1 1 = 4 * Real.sqrt 3 * Real.pi := by
  simp [areaGap]

/-- One spin-`1/2` puncture, `γ = ℓ = 1`: eigenvalue `4 √3 π`, the gap. -/
example : areaEigenvalue 1 1 (fun _ : Fin 1 => 1) = 4 * Real.sqrt 3 * Real.pi := by
  rw [areaEigenvalue_single_one]; simp [areaGap]

/-- The eigenvalue theorem applies to the Haar measure `μ₀`, for one spin-`1/2` puncture. -/
example (a b : ∀ i : Fin 1, Fin ((fun _ : Fin 1 => 1) i + 1)) :
    areaOperator μ₀ 1 1 (spinNetwork (fun _ : Fin 1 => 1) a b) =
      fun g => ((areaGap 1 1 : ℝ) : ℂ) * spinNetwork (fun _ : Fin 1 => 1) a b g := by
  rw [areaOperator_eq_areaEigenvalue, areaEigenvalue_single_one]

/-- The gap theorem applies to a concrete configuration (`k = 2`, spins `1/2, 0`). -/
example : areaGap 1 1 ≤ areaEigenvalue 1 1 (![1, 0] : Fin 2 → ℕ) :=
  areaGap_le_areaEigenvalue one_pos one_pos _ ⟨0, by simp⟩

/-- The true spectrum distinguishes spin `1` from two spins `1/2` ... -/
example : areaEigenvalue 1 1 (fun _ : Fin 1 => 2) ≠ areaEigenvalue 1 1 (fun _ : Fin 2 => 1) :=
  areaEigenvalue_two_ne_one_one one_ne_zero one_ne_zero

/-- ... while the `j`-model does not. -/
example : areaEigenvalueJ 1 1 (fun _ : Fin 1 => 2) = areaEigenvalueJ 1 1 (fun _ : Fin 2 => 1) :=
  areaEigenvalueJ_two_eq_one_one 1 1

/-- The `j`-model gives a smaller (wrong) minimal area. -/
example : areaEigenvalueJ 1 1 (fun _ : Fin 1 => 1) < areaGap 1 1 :=
  areaEigenvalueJ_single_one_ne_areaGap one_pos one_pos

#check @areaOperator_spinNetwork
#check @sum_spinOp_sq_eq_casSqrt_sq

end Lightlike.Canonical.AreaOperator.Tests

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_012.Tests.«μ₀» := _root_.Lightlike.Canonical.AreaOperator.Tests.«μ₀»
