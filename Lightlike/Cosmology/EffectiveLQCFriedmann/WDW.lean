module

public import Lightlike.Cosmology.EffectiveLQCFriedmann.LQC

/-!
# The Wheeler–DeWitt limit of the effective Friedmann equation: no bounce

Trust check (2) of the row: letting the quantum-geometry scale go to zero (`ρ_c → ∞`, i.e.
`1/ρ_c = 0`) the effective equation `H² = (8πG/3) ρ (1 − ρ/ρ_c)` becomes the classical flat
Friedmann equation `H² = 8πGρ/3`, which has no bounce.

* `LQCFriedmann_zero_iff` : with the Lean convention `ρ/0 = 0` the value `ρ_c = 0` encodes
  `1/ρ_c = 0`, and `LQCFriedmann a ρ 0 G t ↔ FirstFriedmann a ρ 0 0 G t` (flat, `Λ = 0`).
* `effRate_tendsto` : for fixed `ρ`, the effective right-hand side tends to the classical one as
  `ρ_c → ∞`.
* `FirstFriedmann.hubble_ne_zero` : the classical flat equation has `H ≠ 0` whenever `ρ > 0`:
  no bounce.
* `LQCFriedmann.hubble_sq_le` : the effective `H²` never exceeds the classical one.

**References.** A. Ashtekar, T. Pawlowski, P. Singh (`aps-2006`).
-/

@[expose] public section

noncomputable section

namespace Lightlike

namespace Cosmology

namespace LQC

/-- **Wheeler–DeWitt limit**: with `1/ρ_c = 0` (encoded by `ρ_c = 0`, since `ρ/0 = 0` in Lean)
the effective equation is exactly the classical flat Friedmann equation with `Λ = 0`. -/
theorem LQCFriedmann_zero_iff (a ρ : ℝ → ℝ) (Gn t : ℝ) :
    LQCFriedmann a ρ 0 Gn t ↔ FirstFriedmann a ρ 0 0 Gn t := by
  unfold LQCFriedmann FirstFriedmann
  simp

/-- As `ρ_c → ∞` the effective right-hand side `(8πG/3) ρ (1 − ρ/ρ_c)` tends to the classical
`8πGρ/3`. -/
theorem effRate_tendsto (Gn ρ : ℝ) :
    Filter.Tendsto (fun ρc : ℝ => 8 * Real.pi * Gn / 3 * ρ * (1 - ρ / ρc)) Filter.atTop
      (nhds (8 * Real.pi * Gn / 3 * ρ)) := by
  have h : Filter.Tendsto (fun ρc : ℝ => ρ / ρc) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  have h3 := (tendsto_const_nhds (x := 8 * Real.pi * Gn / 3 * ρ)).mul h2
  simpa using h3

/-- **No bounce in the Wheeler–DeWitt limit**: the classical flat equation with `Λ = 0`,
`G > 0`, `a t ≠ 0` and `ρ t > 0` forces `a'/a ≠ 0`. -/
theorem FirstFriedmann.hubble_ne_zero {a ρ : ℝ → ℝ} {Gn t : ℝ}
    (h : FirstFriedmann a ρ 0 0 Gn t) (hG : 0 < Gn) (hρ : 0 < ρ t) :
    deriv a t / a t ≠ 0 := by
  unfold FirstFriedmann at h
  intro h0
  rw [h0] at h
  have : 0 < 8 * Real.pi * Gn / 3 * ρ t := by positivity
  have h' : (0 : ℝ) = 8 * Real.pi * Gn / 3 * ρ t := by
    simp only [zero_pow two_ne_zero, zero_div, sub_zero, add_zero] at h
    exact h
  linarith

/-- The same statement for the effective equation at `ρ_c = 0` (the WDW limit). -/
theorem LQCFriedmann.hubble_ne_zero_wdw {a ρ : ℝ → ℝ} {Gn t : ℝ}
    (h : LQCFriedmann a ρ 0 Gn t) (hG : 0 < Gn) (hρ : 0 < ρ t) :
    deriv a t / a t ≠ 0 :=
  FirstFriedmann.hubble_ne_zero ((LQCFriedmann_zero_iff a ρ Gn t).1 h) hG hρ

/-- The quantum-corrected `H²` never exceeds the classical `8πGρ/3` (for `ρ ≥ 0`,
`ρ_c > 0`, `G > 0`). -/
theorem LQCFriedmann.hubble_sq_le {a ρ : ℝ → ℝ} {ρc Gn t : ℝ}
    (h : LQCFriedmann a ρ ρc Gn t) (hG : 0 < Gn) (hc : 0 < ρc) (hρ : 0 ≤ ρ t) :
    (deriv a t / a t) ^ 2 ≤ 8 * Real.pi * Gn / 3 * ρ t := by
  unfold LQCFriedmann at h
  rw [h]
  have h1 : 0 ≤ 8 * Real.pi * Gn / 3 * ρ t := by positivity
  have h2 : 0 ≤ ρ t / ρc := by positivity
  nlinarith

end LQC

end Cosmology

end Lightlike
