import Lightlike.Rows.G2_012.Area

/-!
# The spectrum of the area operator: area gap and the `j` versus `√(j(j+1))` control (row G2-012)

* `areaEigenvalue γ ℓ m = 8π γ ℓ² Σ_i √(j_i (j_i + 1))`, `j_i = m i / 2`, the eigenvalue of
  `areaOperator` on a spin network (`areaOperator_eq_areaEigenvalue`).
* `areaGap γ ℓ = 4 √3 π γ ℓ²`: every nonzero eigenvalue is `≥ areaGap`
  (`areaGap_le_areaEigenvalue`), with equality for a single puncture of spin `1/2`
  (`areaEigenvalue_single_one`); so no eigenvalue lies in `(0, areaGap)`.
* Control: replacing `√(j(j+1))` by `j` (`areaEigenvalueJ`) gives a different spectrum
  (`areaEigenvalueJ_single_one_ne_areaGap`, `areaEigenvalue_two_ne_one_one`).
-/

open MeasureTheory Lightlike.HarmonicAnalysis UnitaryMatrixRep

namespace Lightlike.Rows.G2_012

noncomputable section

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- The area operator with the Casimir square root `casSqrt` replaced by an arbitrary multiplier `φ`. -/
def areaOperatorWith {k : ℕ} (φ : ℕ → ℝ) (γ ℓ : ℝ) (F : (Fin k → SU2) → ℂ) : (Fin k → SU2) → ℂ :=
  fun g => ((8 * Real.pi * γ * ℓ ^ 2 : ℝ) : ℂ) * ∑ i : Fin k, edgeMult μ i φ F g

omit [μ.IsHaarMeasure] [IsProbabilityMeasure μ] in
/-- The true area operator is `areaOperatorWith casSqrt`. -/
theorem areaOperator_eq_with {k : ℕ} (γ ℓ : ℝ) (F : (Fin k → SU2) → ℂ) :
    areaOperator μ γ ℓ F = areaOperatorWith μ casSqrt γ ℓ F := rfl

/-- Any multiplier version acts diagonally on a spin network. -/
theorem areaOperatorWith_spinNetwork {k : ℕ} (φ : ℕ → ℝ) (γ ℓ : ℝ) (m : Fin k → ℕ)
    (a b : ∀ i, Fin (m i + 1)) :
    areaOperatorWith μ φ γ ℓ (spinNetwork m a b) =
      fun g => ((8 * Real.pi * γ * ℓ ^ 2 * ∑ i : Fin k, φ (m i) : ℝ) : ℂ) * spinNetwork m a b g := by
  funext g
  simp only [areaOperatorWith, edgeMult_spinNetwork]
  push_cast
  rw [← Finset.sum_mul]
  ring

/-- The eigenvalue `8π γ ℓ² Σ_i √(j_i (j_i + 1))` for spins `j_i = m i / 2`. -/
def areaEigenvalue {k : ℕ} (γ ℓ : ℝ) (m : Fin k → ℕ) : ℝ :=
  8 * Real.pi * γ * ℓ ^ 2 * ∑ i, casSqrt (m i)

/-- The spin network is an eigenfunction of the area operator with eigenvalue `areaEigenvalue`. -/
theorem areaOperator_eq_areaEigenvalue {k : ℕ} (γ ℓ : ℝ) (m : Fin k → ℕ)
    (a b : ∀ i, Fin (m i + 1)) :
    areaOperator μ γ ℓ (spinNetwork m a b) =
      fun g => (areaEigenvalue γ ℓ m : ℂ) * spinNetwork m a b g :=
  areaOperatorWith_spinNetwork μ casSqrt γ ℓ m a b

/-- The area gap `4 √3 π γ ℓ²`. -/
def areaGap (γ ℓ : ℝ) : ℝ := 4 * Real.sqrt 3 * Real.pi * γ * ℓ ^ 2

theorem casSqrt_nonneg (m : ℕ) : 0 ≤ casSqrt m := by
  unfold casSqrt; positivity

theorem casSqrt_one : casSqrt 1 = Real.sqrt 3 / 2 := by
  unfold casSqrt; norm_num

theorem casSqrt_sq (m : ℕ) : casSqrt m ^ 2 = (m : ℝ) * ((m : ℝ) + 2) / 4 := by
  unfold casSqrt
  rw [div_pow, Real.sq_sqrt (by positivity)]
  norm_num

/-- Every positive spin has `√(j(j+1)) ≥ √3 / 2`. -/
theorem sqrt3_div_two_le_casSqrt {m : ℕ} (hm : 1 ≤ m) : Real.sqrt 3 / 2 ≤ casSqrt m := by
  unfold casSqrt
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (3 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 2) := by nlinarith
  have := Real.sqrt_le_sqrt h2
  linarith

/-- **Area gap**: for `γ, ℓ > 0`, a configuration with at least one puncture carrying a nonzero
spin has area `≥ 4 √3 π γ ℓ²`. -/
theorem areaGap_le_areaEigenvalue {k : ℕ} {γ ℓ : ℝ} (hγ : 0 < γ) (hℓ : 0 < ℓ) (m : Fin k → ℕ)
    (h : ∃ i, 1 ≤ m i) : areaGap γ ℓ ≤ areaEigenvalue γ ℓ m := by
  obtain ⟨i, hi⟩ := h
  have hsum : Real.sqrt 3 / 2 ≤ ∑ l, casSqrt (m l) :=
    (sqrt3_div_two_le_casSqrt hi).trans
      (Finset.single_le_sum (fun l _ => casSqrt_nonneg (m l)) (Finset.mem_univ i))
  have hc : 0 ≤ 8 * Real.pi * γ * ℓ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsum hc
  unfold areaGap areaEigenvalue
  nlinarith

/-- The gap is attained by a single puncture of spin `1/2`. -/
theorem areaEigenvalue_single_one (γ ℓ : ℝ) :
    areaEigenvalue γ ℓ (fun _ : Fin 1 => 1) = areaGap γ ℓ := by
  simp only [areaEigenvalue, areaGap, Finset.univ_unique, Finset.sum_singleton, casSqrt_one]
  ring

/-- With all spins zero the eigenvalue is `0`. -/
theorem areaEigenvalue_zero {k : ℕ} (γ ℓ : ℝ) :
    areaEigenvalue γ ℓ (fun _ : Fin k => 0) = 0 := by
  simp [areaEigenvalue, casSqrt]

/-- No area eigenvalue lies in `(0, areaGap)`. -/
theorem areaEigenvalue_eq_zero_or_gap_le {k : ℕ} {γ ℓ : ℝ} (hγ : 0 < γ) (hℓ : 0 < ℓ)
    (m : Fin k → ℕ) : areaEigenvalue γ ℓ m = 0 ∨ areaGap γ ℓ ≤ areaEigenvalue γ ℓ m := by
  by_cases h : ∃ i, 1 ≤ m i
  · exact Or.inr (areaGap_le_areaEigenvalue hγ hℓ m h)
  · left
    have : m = fun _ => 0 := funext fun i => by
      have := not_exists.mp h i
      omega
    subst this
    exact areaEigenvalue_zero γ ℓ

/-! ### Control: `j` in place of `√(j(j+1))` -/

/-- The wrong model: eigenvalue `8π γ ℓ² Σ_i j_i`. -/
def areaEigenvalueJ {k : ℕ} (γ ℓ : ℝ) (m : Fin k → ℕ) : ℝ :=
  8 * Real.pi * γ * ℓ ^ 2 * ∑ i, ((m i : ℝ) / 2)

/-- The wrong model's operator, `areaOperatorWith` for the multiplier `m ↦ m / 2`, has eigenvalue
`areaEigenvalueJ` on spin networks. -/
theorem areaOperatorJ_spinNetwork {k : ℕ} (γ ℓ : ℝ) (m : Fin k → ℕ) (a b : ∀ i, Fin (m i + 1)) :
    areaOperatorWith μ (fun n => (n : ℝ) / 2) γ ℓ (spinNetwork m a b) =
      fun g => (areaEigenvalueJ γ ℓ m : ℂ) * spinNetwork m a b g :=
  areaOperatorWith_spinNetwork μ (fun n => (n : ℝ) / 2) γ ℓ m a b

/-- The wrong model gives the wrong smallest area `4π γ ℓ²` for one spin-`1/2` puncture,
strictly below the true gap. -/
theorem areaEigenvalueJ_single_one_ne_areaGap {γ ℓ : ℝ} (hγ : 0 < γ) (hℓ : 0 < ℓ) :
    areaEigenvalueJ γ ℓ (fun _ : Fin 1 => 1) < areaGap γ ℓ := by
  have h3 : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hp : 0 < Real.pi * γ * ℓ ^ 2 := by positivity
  simp only [areaEigenvalueJ, areaGap, Finset.univ_unique, Finset.sum_singleton]
  push_cast
  nlinarith

/-- True spectrum distinguishes one spin-`1` puncture from two spin-`1/2` punctures, whereas the
`j`-model does not (`areaEigenvalueJ` coincides on them). -/
theorem areaEigenvalueJ_two_eq_one_one (γ ℓ : ℝ) :
    areaEigenvalueJ γ ℓ (fun _ : Fin 1 => 2) = areaEigenvalueJ γ ℓ (fun _ : Fin 2 => 1) := by
  simp only [areaEigenvalueJ, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two]
  push_cast
  ring

theorem areaEigenvalue_two_ne_one_one {γ ℓ : ℝ} (hγ : γ ≠ 0) (hℓ : ℓ ≠ 0) :
    areaEigenvalue γ ℓ (fun _ : Fin 1 => 2) ≠ areaEigenvalue γ ℓ (fun _ : Fin 2 => 1) := by
  intro h
  simp only [areaEigenvalue, Finset.univ_unique, Finset.sum_singleton, Fin.sum_univ_two] at h
  have hc : 8 * Real.pi * γ * ℓ ^ 2 ≠ 0 := by positivity
  have h' := mul_left_cancel₀ hc h
  have e1 := casSqrt_sq 2
  have e2 := casSqrt_sq 1
  rw [h'] at e1
  have : (casSqrt 1 + casSqrt 1) ^ 2 = 4 * casSqrt 1 ^ 2 := by ring
  rw [this, e2] at e1
  norm_num at e1

end

end Lightlike.Rows.G2_012
