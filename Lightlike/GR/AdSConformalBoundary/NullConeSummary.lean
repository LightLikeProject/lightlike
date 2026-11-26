import Lightlike.GR.AdSConformalBoundary.NullConeConformal

/-!
# The isometry group of anti-de Sitter space acts conformally on its conformal boundary

The summary of the action of `SO(2,3)` on the conformal boundary of anti-de Sitter space (GE7), collecting
`NullCone.lean`, `NullConeAction.lean` and `NullConeConformal.lean`. A boundary point is a null direction
`X = (cos τ, sin τ, ω)` of `ℝ^{2,3}` with `|ω| = 1` (the circle times the sphere, the angle modulo `2π`); a matrix `Λ`
with `Λᵀ η' Λ = η'` acts by `Λ X = ρ X'`:

* `ads_isometry_conformal_boundary`: the action is well defined (`ρ > 0`, `X'` of the same form), it is a group action,
  and for a tangent vector `(dτ, dω) = (a, v)` (`v ⊥ ω`) the image has `-(dτ')² + |dω'|² = (-a² + |v|²) / ρ²`: the
  boundary metric `-dτ² + dΩ²` is multiplied by `ρ⁻²`.
* `adsTimeShift`: the rotation in the `(X₀, X₁)` plane is the time translation `τ ↦ τ + s` of the boundary, with
  factor `1` (the generator of `adsBdyMetric_timeShift`).
-/

open Matrix

noncomputable section

namespace Lightlike

/-- **The isometry group of anti-de Sitter space acts conformally on its conformal boundary.** -/
theorem ads_isometry_conformal_boundary {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) :
    ∀ (τ : ℝ) (ω : Fin 3 → ℝ), ∑ i, ω i ^ 2 = 1 →
      (0 < adsNullFactor Λ τ ω ∧ ∑ i, adsDir Λ τ ω i ^ 2 = 1 ∧
        Λ *ᵥ adsNullVec τ ω = adsNullFactor Λ τ ω • adsNullVec (adsAngle Λ τ ω) (adsDir Λ τ ω)) ∧
      (∀ M : Matrix (Fin 5) (Fin 5) ℝ, Mᵀ * adsEta * M = adsEta →
        adsNullVec (adsAngle (Λ * M) τ ω) (adsDir (Λ * M) τ ω) =
          adsNullVec (adsAngle Λ (adsAngle M τ ω) (adsDir M τ ω)) (adsDir Λ (adsAngle M τ ω) (adsDir M τ ω))) ∧
      (∀ (a : ℝ) (v : Fin 3 → ℝ), ∑ i, ω i * v i = 0 →
        -(adsAngleDeriv Λ τ ω a v) ^ 2 + ∑ i, adsDirDeriv Λ τ ω a v i ^ 2 =
          (-a ^ 2 + ∑ i, v i ^ 2) / adsNullFactor Λ τ ω ^ 2) := by
  intro τ ω hω
  exact ⟨⟨adsNullFactor_pos hΛ τ hω, sum_sq_adsDir hΛ τ hω, mulVec_adsNullVec_eq hΛ τ hω⟩,
    fun M hM => adsNullVec_mul hΛ hM τ hω, fun a v hv => adsBdyMetric_conformal hΛ τ hω hv a⟩

/-- The rotation by `s` in the `(X₀, X₁)` plane. -/
def adsTimeShift (s : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![Real.cos s, -Real.sin s, 0, 0, 0; Real.sin s, Real.cos s, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1]

theorem adsTimeShift_lorentz (s : ℝ) : (adsTimeShift s)ᵀ * adsEta * adsTimeShift s = adsEta := by
  have h := Real.sin_sq_add_cos_sq s
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adsTimeShift, adsEta, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ] <;> nlinarith [h]

/-- The rotation acts as the time translation `τ ↦ τ + s` with factor `1`. -/
theorem adsTimeShift_mulVec (s τ : ℝ) (ω : Fin 3 → ℝ) :
    adsTimeShift s *ᵥ adsNullVec τ ω = adsNullVec (τ + s) ω := by
  ext j
  fin_cases j <;>
    simp [adsTimeShift, adsNullVec, mulVec, dotProduct, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem adsNullFactor_adsTimeShift (s τ : ℝ) {ω : Fin 3 → ℝ} : adsNullFactor (adsTimeShift s) τ ω = 1 := by
  unfold adsNullFactor
  rw [adsTimeShift_mulVec]
  simp [adsNullVec]

end Lightlike
