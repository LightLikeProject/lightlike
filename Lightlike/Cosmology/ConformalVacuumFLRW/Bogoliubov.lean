module

public import Mathlib

/-!
# Bogoliubov coefficients of α-vacua (row G1-037, milestone CO11)

A mode of a free scalar field on a spatially flat FLRW spacetime, for one comoving wavenumber
`k` and at one conformal time `η₀`, is recorded by the pair `(u(η₀), u'(η₀))`. A reference mode `r`
(a Parker–Fulling WKB mode in the application) is normalised by `r r̄' − r̄ r' = i`. A normalised mode
`u` is `u = α r + β r̄`, and `β` is the Bogoliubov coefficient of the state of `u` relative to `r`.

The Fourier-mode form of the adiabatic condition used in this row says that `β = β_k` decays
like `k^{-(N+1)}` (`BogoliubovDecay`). Junker and Schrohe (`junker-schrohe-2002`) define adiabatic
states of order `N` by a Sobolev condition on the two-point function; we do not formalise that
definition, and `BogoliubovDecay` is only its Fourier-mode shadow.

The α-vacua are the Bogoliubov transforms `u ↦ cosh a · u + e^{iθ} sinh a · ū` of a vacuum mode.

Main results
* `Lightlike.Adiabatic.reconstruct`: `u = α r + β r̄`.
* `Lightlike.Adiabatic.normSq_alpha_sub_normSq_beta`: `|α|² − |β|² = 1`.
* `Lightlike.Adiabatic.bogBeta_alphaVacuum`: the coefficient `β` of the α-vacuum is
  `cosh a · β + e^{iθ} sinh a · ᾱ`.
* `Lightlike.Adiabatic.sinh_le_norm_bogBeta_alphaVacuum_add`: `|β_a| + cosh a |β| ≥ sinh a`.
* `Lightlike.Adiabatic.not_bogoliubovDecay_alphaVacuum`: if a vacuum is adiabatic of order `0`
  (its `β` tends to `0`), no α-vacuum with `a ≠ 0` has `BogoliubovDecay` of any order.
-/

@[expose] public section

noncomputable section

namespace Lightlike.Adiabatic

open Complex Filter Asymptotics

/-- A mode at one time: its value and its time derivative. -/
abbrev ModeData := ℂ × ℂ

/-- The Wronskian form `r r̄' − r̄ r'` of a reference mode; it equals `i` for a normalised mode. -/
def IsNormalised (r : ModeData) : Prop :=
  r.1 * (starRingEnd ℂ) r.2 - (starRingEnd ℂ) r.1 * r.2 = I

/-- The coefficient `α` of `u = α r + β r̄`: `α = −i (u r̄' − u' r̄)`. -/
def bogAlpha (r u : ModeData) : ℂ :=
  -I * (u.1 * (starRingEnd ℂ) r.2 - u.2 * (starRingEnd ℂ) r.1)

/-- The Bogoliubov coefficient `β` of `u = α r + β r̄`: `β = i (u r' − u' r)`. -/
def bogBeta (r u : ModeData) : ℂ :=
  I * (u.1 * r.2 - u.2 * r.1)

/-- The complex conjugate of a mode. -/
def conjMode (u : ModeData) : ModeData :=
  ((starRingEnd ℂ) u.1, (starRingEnd ℂ) u.2)

/-- The α-vacuum transform `cosh a · u + e^{iθ} sinh a · ū` of a mode. -/
def alphaVacuum (a θ : ℝ) (u : ModeData) : ModeData :=
  ((Real.cosh a : ℂ) * u.1 + exp (θ * I) * (Real.sinh a : ℂ) * (conjMode u).1,
   (Real.cosh a : ℂ) * u.2 + exp (θ * I) * (Real.sinh a : ℂ) * (conjMode u).2)

/-- **A mode is the combination `α r + β r̄` of the reference mode and its conjugate.** -/
theorem reconstruct {r : ModeData} (hr : IsNormalised r) (u : ModeData) :
    u.1 = bogAlpha r u * r.1 + bogBeta r u * (starRingEnd ℂ) r.1 ∧
    u.2 = bogAlpha r u * r.2 + bogBeta r u * (starRingEnd ℂ) r.2 := by
  unfold IsNormalised at hr
  unfold bogAlpha bogBeta
  constructor
  · linear_combination (I * u.1) * hr + u.1 * Complex.I_sq
  · linear_combination (I * u.2) * hr + u.2 * Complex.I_sq

/-- The conjugate of `α` is the `β` coefficient of the conjugate mode. -/
theorem bogBeta_conjMode (r u : ModeData) :
    bogBeta r (conjMode u) = (starRingEnd ℂ) (bogAlpha r u) := by
  simp [bogBeta, bogAlpha, conjMode]

/-- `β` is additive and `ℂ`-homogeneous in the mode. -/
theorem bogBeta_alphaVacuum (r : ModeData) (a θ : ℝ) (u : ModeData) :
    bogBeta r (alphaVacuum a θ u) =
      (Real.cosh a : ℂ) * bogBeta r u +
        exp (θ * I) * (Real.sinh a : ℂ) * (starRingEnd ℂ) (bogAlpha r u) := by
  rw [← bogBeta_conjMode]
  simp only [bogBeta, alphaVacuum]
  ring

/-- **The Wronskian is `|α|² − |β|²` times that of the reference**: `|α|² − |β|² = 1` for
normalised `r` and `u`. -/
theorem normSq_alpha_sub_normSq_beta {r u : ModeData} (hr : IsNormalised r)
    (hu : IsNormalised u) :
    ‖bogAlpha r u‖ ^ 2 - ‖bogBeta r u‖ ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := reconstruct hr u
  have key : (bogAlpha r u * (starRingEnd ℂ) (bogAlpha r u) -
      bogBeta r u * (starRingEnd ℂ) (bogBeta r u)) * I = I := by
    unfold IsNormalised at hu hr
    rw [h1, h2] at hu
    simp only [map_add, map_mul, Complex.conj_conj] at hu
    linear_combination hu - (bogAlpha r u * (starRingEnd ℂ) (bogAlpha r u) -
      bogBeta r u * (starRingEnd ℂ) (bogBeta r u)) * hr
  have key2 : bogAlpha r u * (starRingEnd ℂ) (bogAlpha r u) -
      bogBeta r u * (starRingEnd ℂ) (bogBeta r u) = 1 := by
    have := mul_right_cancel₀ Complex.I_ne_zero (key.trans (one_mul I).symm)
    exact this
  rw [Complex.mul_conj, Complex.mul_conj] at key2
  have := congrArg Complex.re key2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at this
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at this
  simpa using this

theorem one_le_norm_bogAlpha {r u : ModeData} (hr : IsNormalised r) (hu : IsNormalised u) :
    1 ≤ ‖bogAlpha r u‖ := by
  have h := normSq_alpha_sub_normSq_beta hr hu
  have h0 : 0 ≤ ‖bogBeta r u‖ ^ 2 := sq_nonneg _
  have : 1 ≤ ‖bogAlpha r u‖ ^ 2 := by linarith
  nlinarith [norm_nonneg (bogAlpha r u)]

/-- **An α-vacuum with `a ≠ 0` keeps a definite Bogoliubov coefficient**: for `a ≥ 0`,
`sinh a ≤ |β_a| + cosh a |β|`. -/
theorem sinh_le_norm_bogBeta_alphaVacuum_add {r u : ModeData} (hr : IsNormalised r)
    (hu : IsNormalised u) {a : ℝ} (ha : 0 ≤ a) (θ : ℝ) :
    Real.sinh a ≤ ‖bogBeta r (alphaVacuum a θ u)‖ + Real.cosh a * ‖bogBeta r u‖ := by
  have hs : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha
  have hc : 0 ≤ Real.cosh a := (Real.cosh_pos a).le
  have h1 := one_le_norm_bogAlpha hr hu
  have hexp : ‖exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hsplit : exp (θ * I) * (Real.sinh a : ℂ) * (starRingEnd ℂ) (bogAlpha r u) =
      bogBeta r (alphaVacuum a θ u) - (Real.cosh a : ℂ) * bogBeta r u := by
    rw [bogBeta_alphaVacuum]; ring
  have hn : ‖exp (θ * I) * (Real.sinh a : ℂ) * (starRingEnd ℂ) (bogAlpha r u)‖ =
      Real.sinh a * ‖bogAlpha r u‖ := by
    rw [norm_mul, norm_mul, hexp, one_mul, Complex.norm_real, Real.norm_of_nonneg hs,
      RCLike.norm_conj]
  have htri := norm_sub_le (bogBeta r (alphaVacuum a θ u)) ((Real.cosh a : ℂ) * bogBeta r u)
  rw [← hsplit, hn, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc] at htri
  nlinarith

/-- The Fourier-mode shadow of "adiabatic of order `N`": the Bogoliubov coefficient `b k`
relative to the order-`N` reference mode is `O(k^{-(N+1)})` as `k → ∞`. -/
def BogoliubovDecay (N : ℕ) (b : ℝ → ℂ) : Prop :=
  b =O[atTop] fun k : ℝ => k ^ (-(N + 1 : ℤ))

/-- For families `k ↦ r k`, `k ↦ u k` of normalised modes with `β_k → 0` for `u`, the `β_k` of
an α-vacuum with `a > 0` does not tend to `0`. -/
theorem not_tendsto_bogBeta_alphaVacuum {r u : ℝ → ModeData} (hr : ∀ k, IsNormalised (r k))
    (hu : ∀ k, IsNormalised (u k)) (h0 : Tendsto (fun k => bogBeta (r k) (u k)) atTop (nhds 0))
    {a : ℝ} (ha : 0 < a) (θ : ℝ) :
    ¬ Tendsto (fun k => bogBeta (r k) (alphaVacuum a θ (u k))) atTop (nhds 0) := by
  intro h
  have hn0 := h.norm.add (h0.norm.const_mul (Real.cosh a))
  simp only [norm_zero, mul_zero, add_zero] at hn0
  have hlt : Real.sinh a ≤ 0 :=
    ge_of_tendsto hn0 (Eventually.of_forall fun k =>
      sinh_le_norm_bogBeta_alphaVacuum_add (hr k) (hu k) ha.le θ)
  exact absurd (Real.sinh_pos_iff.mpr ha) (not_lt.mpr hlt)

/-- **No α-vacuum with `a > 0` is adiabatic of any order when the vacuum it is built from is
adiabatic of order `0`**: its `β_k` has no decay `k^{-(N+1)}`, for every `N`. -/
theorem not_bogoliubovDecay_alphaVacuum {r u : ℝ → ModeData} (hr : ∀ k, IsNormalised (r k))
    (hu : ∀ k, IsNormalised (u k)) (h0 : Tendsto (fun k => bogBeta (r k) (u k)) atTop (nhds 0))
    {a : ℝ} (ha : 0 < a) (θ : ℝ) (N : ℕ) :
    ¬ BogoliubovDecay N (fun k => bogBeta (r k) (alphaVacuum a θ (u k))) := by
  intro hO
  apply not_tendsto_bogBeta_alphaVacuum hr hu h0 ha θ
  have hz : Tendsto (fun k : ℝ => k ^ (-(N + 1 : ℤ))) atTop (nhds 0) :=
    tendsto_zpow_atTop_zero (by omega)
  exact hO.trans_tendsto hz

end Lightlike.Adiabatic
