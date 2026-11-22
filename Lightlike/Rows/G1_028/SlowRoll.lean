module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Slow-roll parameters and the number of e-folds of a scalar potential

Units `8πG = 1`, as in milestone CO9 (single-field inflation, slow roll).

* `epsilonV V φ` : `ε = (1/2) (V′/V)²`.
* `etaV V φ` : `η = V″/V`.
* `eFolds V φi φe` : `N = ∫_{φe}^{φi} V/V′ dφ`, the slow-roll number of e-folds.
* `tensorToScalar ε` : `r = 16 ε`.
* `quadPot m` : the potential `V = m² φ²/2`.
* `epsilonV_quadPot`, `epsilonV_quadPot_eq_one_iff` : `ε = 2/φ²`, so `ε = 1` at `φ = √2`.
* `eFolds_quadPot` : `N = (φi² − φe²)/4`; `eFolds_quadPot_end` : `N = φi²/4 − 1/2` when inflation
  ends at `φe = √2` (where `ε = 1`).
* `spectralTilt_quadPot`, `tensorToScalar_quadPot` : with `N₀ = φ²/4 = N + 1/2`,
  `n_s − 1 = −6ε + 2η = −2/N₀` and `r = 16ε = 8/N₀`.

**References.** Baumann, *TASI Lectures on Inflation* (`baumann-2009`), Section 6.2 (slow roll).
-/

@[expose] public section

open intervalIntegral

noncomputable section

namespace Lightlike

namespace Cosmology

namespace SlowRoll

/-- The first slow-roll parameter `ε = (1/2) (V′/V)²` (units `8πG = 1`). -/
def epsilonV (V : ℝ → ℝ) (φ : ℝ) : ℝ := (deriv V φ / V φ) ^ 2 / 2

/-- The second slow-roll parameter `η = V″/V` (units `8πG = 1`). -/
def etaV (V : ℝ → ℝ) (φ : ℝ) : ℝ := deriv (deriv V) φ / V φ

/-- The slow-roll number of e-folds `N = ∫_{φe}^{φi} V/V′ dφ`, from the end value `φe` to the
initial value `φi`. -/
def eFolds (V : ℝ → ℝ) (φi φe : ℝ) : ℝ := ∫ φ in φe..φi, V φ / deriv V φ

/-- The scalar tilt at leading order in slow roll, `n_s − 1 = −6ε + 2η`. -/
def spectralTilt (V : ℝ → ℝ) (φ : ℝ) : ℝ := -6 * epsilonV V φ + 2 * etaV V φ

/-- The tensor-to-scalar ratio `r = 16 ε` in terms of the first slow-roll parameter. -/
def tensorToScalar (ε : ℝ) : ℝ := 16 * ε

/-- The quadratic potential `V(φ) = m² φ²/2`. -/
def quadPot (m : ℝ) (φ : ℝ) : ℝ := m ^ 2 * φ ^ 2 / 2

/-- `V′(φ) = m² φ` for the quadratic potential. -/
lemma deriv_quadPot (m φ : ℝ) : deriv (quadPot m) φ = m ^ 2 * φ := by
  have h : HasDerivAt (quadPot m) (m ^ 2 * φ) φ := by
    have := ((hasDerivAt_pow 2 φ).const_mul (m ^ 2)).div_const 2
    exact this.congr_deriv (by push_cast; ring)
  exact h.deriv

/-- `V″ = m²` for the quadratic potential. -/
lemma deriv_deriv_quadPot (m φ : ℝ) : deriv (deriv (quadPot m)) φ = m ^ 2 := by
  have : deriv (quadPot m) = fun φ => m ^ 2 * φ := funext (deriv_quadPot m)
  rw [this]
  simp

/-- For the quadratic potential `ε = 2/φ²` (for `m ≠ 0`, `φ ≠ 0`). -/
lemma epsilonV_quadPot {m φ : ℝ} (hm : m ≠ 0) (hφ : φ ≠ 0) :
    epsilonV (quadPot m) φ = 2 / φ ^ 2 := by
  unfold epsilonV
  rw [deriv_quadPot]
  unfold quadPot
  field_simp

/-- `ε = 1` at `φ = √2` for the quadratic potential, and for `φ > 0` only there. -/
lemma epsilonV_quadPot_eq_one_iff {m φ : ℝ} (hm : m ≠ 0) (hφ : 0 < φ) :
    epsilonV (quadPot m) φ = 1 ↔ φ = Real.sqrt 2 := by
  rw [epsilonV_quadPot hm hφ.ne']
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  constructor
  · intro h
    have hsq : φ ^ 2 = 2 := by
      have : φ ^ 2 ≠ 0 := by positivity
      field_simp at h
      linarith
    rw [← Real.sqrt_sq hφ.le, hsq]
  · rintro rfl
    rw [Real.sq_sqrt h2]
    norm_num

/-- `ε = 1` at `φ = √2` for the quadratic potential. -/
lemma epsilonV_quadPot_sqrt_two {m : ℝ} (hm : m ≠ 0) :
    epsilonV (quadPot m) (Real.sqrt 2) = 1 :=
  (epsilonV_quadPot_eq_one_iff hm (by positivity)).2 rfl

/-- For the quadratic potential `η = 2/φ²` (for `m ≠ 0`, `φ ≠ 0`). -/
lemma etaV_quadPot {m φ : ℝ} (hm : m ≠ 0) (hφ : φ ≠ 0) :
    etaV (quadPot m) φ = 2 / φ ^ 2 := by
  unfold etaV
  rw [deriv_deriv_quadPot]
  unfold quadPot
  field_simp

/-- The ratio `V/V′` of the quadratic potential is `φ/2`, at every point (both sides are `0`
at `φ = 0`). -/
lemma quadPot_div_deriv {m : ℝ} (hm : m ≠ 0) (φ : ℝ) :
    quadPot m φ / deriv (quadPot m) φ = φ / 2 := by
  rw [deriv_quadPot]
  unfold quadPot
  by_cases hφ : φ = 0
  · simp [hφ]
  · field_simp

/-- **Number of e-folds for the quadratic potential**: `N = (φi² − φe²)/4`. -/
theorem eFolds_quadPot {m : ℝ} (hm : m ≠ 0) (φi φe : ℝ) :
    eFolds (quadPot m) φi φe = (φi ^ 2 - φe ^ 2) / 4 := by
  unfold eFolds
  simp_rw [quadPot_div_deriv hm]
  rw [intervalIntegral.integral_div, integral_id]
  ring

/-- With inflation ending at `φe = √2` (where `ε = 1`), `N = φi²/4 − 1/2`. -/
theorem eFolds_quadPot_end {m : ℝ} (hm : m ≠ 0) (φi : ℝ) :
    eFolds (quadPot m) φi (Real.sqrt 2) = φi ^ 2 / 4 - 1 / 2 := by
  rw [eFolds_quadPot hm, Real.sq_sqrt (by norm_num)]
  ring

/-- For the quadratic potential `n_s − 1 = −8/φ² = −2/N₀` with `N₀ = φ²/4`. -/
theorem spectralTilt_quadPot {m φ : ℝ} (hm : m ≠ 0) (hφ : φ ≠ 0) :
    spectralTilt (quadPot m) φ = -2 / (φ ^ 2 / 4) := by
  unfold spectralTilt
  rw [epsilonV_quadPot hm hφ, etaV_quadPot hm hφ]
  field_simp
  ring

/-- For the quadratic potential `r = 16ε = 32/φ² = 8/N₀` with `N₀ = φ²/4`. -/
theorem tensorToScalar_quadPot {m φ : ℝ} (hm : m ≠ 0) (hφ : φ ≠ 0) :
    tensorToScalar (epsilonV (quadPot m) φ) = 8 / (φ ^ 2 / 4) := by
  unfold tensorToScalar
  rw [epsilonV_quadPot hm hφ]
  field_simp
  ring

end SlowRoll

end Cosmology

end Lightlike
