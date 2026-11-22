module

public import Mathlib
public import Lightlike.Rows.G1_037.Bogoliubov

/-!
# The conformal vacuum on spatially flat FLRW (row G1-037, milestone CO11)

For a scalar field `φ = χ / a` on a spatially flat FLRW spacetime with scale factor `a(η)` in
conformal time, the Fourier mode `χ_k` solves `χ'' + (k² + C(η)) χ = 0` with
`C = m² a² + (6 ξ − 1) a''/a`. For a massless (`m = 0`) conformally coupled (`ξ = 1/6`) field
`C = 0` for every scale factor, and the positive-frequency mode `e^{-ikη}/√(2k)` defines the
conformal vacuum.

The conformal modes are exact adiabatic reference modes (all WKB orders equal `e^{-ikη}/√(2k)`),
so the conformal vacuum has `β_k = 0` and the α-vacua built from it have `|β_k| = sinh a`, for every
`k`. By `Lightlike.Adiabatic.not_bogoliubovDecay_alphaVacuum` they have `BogoliubovDecay` of no order.

Main results
* `Lightlike.Adiabatic.conformalPotential_massless_conformal`: `C = 0` for `m = 0`, `ξ = 1/6`.
* `Lightlike.Adiabatic.conformalMode_isSolution`: the conformal mode solves the `C = 0` equation.
* `Lightlike.Adiabatic.isNormalised_conformalData`: it is normalised.
* `Lightlike.Adiabatic.bogBeta_conformalData_alphaVacuum`: `β = e^{iθ} sinh a` for its α-vacua.
* `Lightlike.Adiabatic.not_bogoliubovDecay_conformal_alphaVacuum`: no α-vacuum with `a > 0`
  over the conformal vacuum has `BogoliubovDecay` of any order.

The Hadamard property itself is not formalised here (no wave-front set in Lightlike or Mathlib).
-/

@[expose] public section

noncomputable section

namespace Lightlike.Adiabatic

open Complex Filter Asymptotics

/-- The potential `C = m² a² + (6 ξ − 1) a''/a` of the mode equation `χ'' + (k² + C) χ = 0`
of the rescaled field `χ = a φ`, with `a''` the second derivative of the scale factor in
conformal time. -/
def conformalPotential (a : ℝ → ℝ) (m ξ : ℝ) (η : ℝ) : ℝ :=
  m ^ 2 * a η ^ 2 + (6 * ξ - 1) * (deriv (deriv a) η / a η)

/-- **A massless conformally coupled field has no potential on any flat FLRW background.** -/
theorem conformalPotential_massless_conformal (a : ℝ → ℝ) (η : ℝ) :
    conformalPotential a 0 (1 / 6) η = 0 := by
  simp [conformalPotential]

/-- The mode equation `v'' + (k² + C) v = 0`. -/
def IsModeSolution (k : ℝ) (C : ℝ → ℝ) (v : ℝ → ℂ) : Prop :=
  ∀ η, deriv (deriv v) η + ((k ^ 2 + C η : ℝ) : ℂ) * v η = 0

/-- The conformal mode `e^{-ikη}/√(2k)`. -/
def conformalMode (k : ℝ) (η : ℝ) : ℂ :=
  exp (-(I * k) * η) / ((Real.sqrt (2 * k) : ℝ) : ℂ)

theorem hasDerivAt_conformalMode (k η : ℝ) :
    HasDerivAt (conformalMode k) (-(I * k) * conformalMode k η) η := by
  have h : HasDerivAt (fun z : ℂ => exp (-(I * k) * z) / ((Real.sqrt (2 * k) : ℝ) : ℂ))
      (exp (-(I * k) * (η : ℂ)) * (-(I * k) * 1) / ((Real.sqrt (2 * k) : ℝ) : ℂ)) (η : ℂ) :=
    (((hasDerivAt_id (η : ℂ)).const_mul (-(I * k))).cexp).div_const _
  have h2 := h.comp_ofReal
  have : exp (-(I * k) * (η : ℂ)) * (-(I * k) * 1) / ((Real.sqrt (2 * k) : ℝ) : ℂ) =
      -(I * k) * conformalMode k η := by
    unfold conformalMode; ring
  rw [this] at h2
  exact h2

theorem deriv_conformalMode (k : ℝ) :
    deriv (conformalMode k) = fun η => -(I * k) * conformalMode k η :=
  funext fun η => (hasDerivAt_conformalMode k η).deriv

/-- **The conformal mode solves the equation with `C = 0`.** -/
theorem conformalMode_isSolution (k : ℝ) : IsModeSolution k (fun _ => 0) (conformalMode k) := by
  intro η
  rw [deriv_conformalMode, deriv_const_mul_field']
  rw [deriv_conformalMode]
  simp only [add_zero, Complex.ofReal_pow]
  have : (I * (k : ℂ)) ^ 2 = -(k : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  linear_combination (conformalMode k η) * this

/-- The mode data `(v, v')` of the conformal mode at time `η`. -/
def conformalData (k η : ℝ) : ModeData :=
  (conformalMode k η, -(I * k) * conformalMode k η)

/-- **The conformal mode is normalised** (`k > 0`). -/
theorem isNormalised_conformalData {k : ℝ} (hk : 0 < k) (η : ℝ) :
    IsNormalised (conformalData k η) := by
  unfold IsNormalised conformalData
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  have hs : ((Real.sqrt (2 * k) : ℝ) : ℂ) ^ 2 = 2 * k := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by linarith)]; push_cast; ring
  have hs0 : ((Real.sqrt (2 * k) : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt (2 * k) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    exact_mod_cast this
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hconj : (starRingEnd ℂ) (conformalMode k η) = exp (I * k * η) /
      ((Real.sqrt (2 * k) : ℝ) : ℂ) := by
    unfold conformalMode
    rw [map_div₀, ← Complex.exp_conj]
    simp [Complex.conj_ofReal]
  rw [hconj]
  unfold conformalMode
  have he : exp (-(I * k * η)) * exp (I * k * η) = 1 := by
    rw [← Complex.exp_add]; simp
  simp only [neg_mul]
  field_simp
  linear_combination (2 * k) * he - hs

/-- A normalised mode has `α = 1` relative to itself. -/
theorem bogAlpha_self {r : ModeData} (hr : IsNormalised r) : bogAlpha r r = 1 := by
  unfold IsNormalised at hr
  unfold bogAlpha
  linear_combination (-I) * hr - Complex.I_sq

/-- A mode has `β = 0` relative to itself. -/
theorem bogBeta_self (r : ModeData) : bogBeta r r = 0 := by
  unfold bogBeta; ring

/-- **The α-vacuum over a normalised mode has `β = e^{iθ} sinh a` relative to that mode.** -/
theorem bogBeta_alphaVacuum_self {r : ModeData} (hr : IsNormalised r) (a θ : ℝ) :
    bogBeta r (alphaVacuum a θ r) = exp (θ * I) * (Real.sinh a : ℂ) := by
  rw [bogBeta_alphaVacuum, bogBeta_self, bogAlpha_self hr]
  simp

/-- **The α-vacuum over the conformal vacuum has `|β_k| = |sinh a|` for every `k > 0`.** -/
theorem bogBeta_conformalData_alphaVacuum {k : ℝ} (hk : 0 < k) (η a θ : ℝ) :
    ‖bogBeta (conformalData k η) (alphaVacuum a θ (conformalData k η))‖ = |Real.sinh a| := by
  rw [bogBeta_alphaVacuum_self (isNormalised_conformalData hk η), norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **No α-vacuum with `a > 0` over the conformal vacuum is adiabatic of any order.**
Relative to the conformal modes (exact adiabatic references of every order), its `β_k` is
`e^{iθ} sinh a`, which has no decay `k^{-(N+1)}`. -/
theorem not_bogoliubovDecay_conformal_alphaVacuum (η a θ : ℝ) (ha : 0 < a) (N : ℕ) :
    ¬ BogoliubovDecay N
      (fun k => bogBeta (conformalData k η) (alphaVacuum a θ (conformalData k η))) := by
  intro hO
  refine not_bogoliubovDecay_alphaVacuum (r := fun k => conformalData (max k 1) η)
    (u := fun k => conformalData (max k 1) η)
    (fun k => isNormalised_conformalData (lt_of_lt_of_le one_pos (le_max_right _ _)) η)
    (fun k => isNormalised_conformalData (lt_of_lt_of_le one_pos (le_max_right _ _)) η)
    (by simp only [bogBeta_self]; exact tendsto_const_nhds) ha θ N ?_
  refine hO.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  simp [max_eq_left hk]
