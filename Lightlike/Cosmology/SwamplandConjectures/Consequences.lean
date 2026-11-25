module

public import Mathlib
public import Lightlike.Cosmology.SwamplandConjectures.Defs

/-!
# Consequences of the swampland hypotheses (row G1-046, milestone CO23)

Supporting lemmas around the hypotheses of `Lightlike/Cosmology/SwamplandConjectures/Defs.lean`:

* the de Sitter conjecture implies its refined version;
* the refined conjecture at a critical point with `V > 0` forces a tachyonic Hessian direction;
* the distance conjecture forces the tower mass to tend to `0` at infinite field distance, and the
  mass `e^{-α d}` satisfies it;
* the quintessence equation of state `w = -1 + λ²/3` of the exponential potential is accelerating
  (`w < -1/3`) exactly when `λ² < 2`.
-/

@[expose] public section

namespace Lightlike.Cosmology.SwamplandConjectures

open Real Filter Topology

set_option linter.unusedSectionVars false

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The de Sitter conjecture implies the refined one (for any `c'`). -/
theorem refined_of_deSitter {c : ℝ} (c' : ℝ) {V : E → ℝ} (h : DeSitterConjecture c V) :
    RefinedDeSitterConjecture c c' V :=
  fun φ hφ => Or.inl (h φ hφ)

/-- Refined de Sitter conjecture at a critical point with `V > 0` and `c > 0`: there is a unit
direction `v` with `∇²V(v,v) ≤ -c' V`. -/
theorem tachyonic_direction_of_critical {c c' : ℝ} {V : E → ℝ} (hc : 0 < c)
    (h : RefinedDeSitterConjecture c c' V) {φ : E} (hV : 0 < V φ)
    (hcrit : fderiv ℝ V φ = 0) :
    ∃ v : E, ‖v‖ = 1 ∧ iteratedFDeriv ℝ 2 V φ ![v, v] ≤ -c' * V φ := by
  rcases h φ hV with h1 | h2
  · exfalso
    have : gradNorm V φ = 0 := by simp [gradNorm, hcrit]
    have := mul_pos hc hV
    linarith
  · exact h2

/-- **Distance conjecture, consequence**: the tower mass tends to `0` as the field distance
from `φ₀` tends to infinity. -/
theorem DistanceConjecture.tendsto_zero {m : E → ℝ} {φ₀ : E} (h : DistanceConjecture m φ₀) :
    Tendsto m (comap (fun φ => dist φ φ₀) atTop) (𝓝 0) := by
  obtain ⟨α, hα, C, D, hb⟩ := h
  have hexp : Tendsto (fun t : ℝ => C * Real.exp (-α * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -α * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hlim : Tendsto (fun φ : E => C * Real.exp (-α * dist φ φ₀))
      (comap (fun φ => dist φ φ₀) atTop) (𝓝 0) :=
    hexp.comp tendsto_comap
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · have : ∀ᶠ φ in comap (fun φ : E => dist φ φ₀) atTop, D ≤ dist φ φ₀ :=
      tendsto_comap.eventually (eventually_ge_atTop D)
    exact this.mono fun φ hφ => (hb φ hφ).1
  · have : ∀ᶠ φ in comap (fun φ : E => dist φ φ₀) atTop, D ≤ dist φ φ₀ :=
      tendsto_comap.eventually (eventually_ge_atTop D)
    exact this.mono fun φ hφ => (hb φ hφ).2

/-- The mass `e^{-α d(φ, φ₀)}` satisfies the distance conjecture for any `α > 0`. -/
theorem distanceConjecture_exp (φ₀ : E) {α : ℝ} (hα : 0 < α) :
    DistanceConjecture (fun φ => Real.exp (-α * dist φ φ₀)) φ₀ :=
  ⟨α, hα, 1, 0, fun _ _ => ⟨(Real.exp_pos _).le, by simp⟩⟩

end General

/-- The equation of state `w = -1 + λ²/3` of a scalar field rolling down `V₀ e^{-λφ}`
(scaling solution, units `8πG = 1`). -/
noncomputable def eosExp (l : ℝ) : ℝ := -1 + l ^ 2 / 3

/-- Accelerated expansion (`w < -1/3`) for the exponential potential holds iff `λ² < 2`,
i.e. iff the slow-roll parameter `ε_V = λ²/2` is below `1`. -/
theorem eosExp_lt_iff (l : ℝ) : eosExp l < -1 / 3 ↔ l ^ 2 < 2 := by
  unfold eosExp
  constructor <;> intro h <;> linarith

end Lightlike.Cosmology.SwamplandConjectures

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.DistanceConjecture.tendsto_zero := _root_.Lightlike.Cosmology.SwamplandConjectures.DistanceConjecture.tendsto_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.distanceConjecture_exp := _root_.Lightlike.Cosmology.SwamplandConjectures.distanceConjecture_exp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.eosExp := _root_.Lightlike.Cosmology.SwamplandConjectures.eosExp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.eosExp_lt_iff := _root_.Lightlike.Cosmology.SwamplandConjectures.eosExp_lt_iff
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.refined_of_deSitter := _root_.Lightlike.Cosmology.SwamplandConjectures.refined_of_deSitter
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_046.tachyonic_direction_of_critical := _root_.Lightlike.Cosmology.SwamplandConjectures.tachyonic_direction_of_critical
