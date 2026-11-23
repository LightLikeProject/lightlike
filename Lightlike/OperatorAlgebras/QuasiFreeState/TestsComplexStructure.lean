import Lightlike.OperatorAlgebras.QuasiFreeState.ComplexStructure

/-!
# Tests for the complex-structure purity criterion

One mode: `V = ℝ²`, `η = ` the Euclidean form, `ω(x, y) = x₀ y₁ - x₁ y₀`, `J(x₀, x₁) = (-x₁, x₀)`. This is the Fock vacuum
of one mode, a pure quasi-free state (`isPureState_oneMode`). A non-example (wrong input): with the doubled form
`η' = 2 η` (a thermal covariance, a mixed state) and the same `ω` there is no compatible complex structure
(`not_compatible_thermal`), so the criterion does not apply; this is a failure of the hypothesis, not a proof of
mixedness (the necessity half is not proved).
-/

namespace Lightlike.OperatorAlgebras.QuasiFreeState

/-- The Euclidean form on `ℝ²` scaled by `c`. -/
noncomputable def etaC (c : ℝ) : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => c * (x 0 * y 0 + x 1 * y 1))
    (fun x x' y => by simp; ring) (fun r x y => by simp; ring)
    (fun x y y' => by simp; ring) (fun r x y => by simp; ring)

/-- The standard symplectic form of one mode. -/
noncomputable def omegaOne : LinearMap.BilinForm ℝ (Fin 2 → ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => x 0 * y 1 - x 1 * y 0)
    (fun x x' y => by simp; ring) (fun r x y => by simp; ring)
    (fun x y y' => by simp; ring) (fun r x y => by simp; ring)

/-- The rotation `J(x₀, x₁) = (-x₁, x₀)`. -/
def rotJ : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![-x 1, x 0]
  map_add' x y := by ext i; fin_cases i <;> (simp; try ring)
  map_smul' r x := by ext i; fin_cases i <;> simp

/-- The one-mode compatible complex structure. -/
noncomputable def oneModeStructure : CompatibleComplexStructure omegaOne (etaC 1) where
  J := rotJ
  J_sq x := by ext i; fin_cases i <;> simp [rotJ]
  symm x y := by simp [etaC]; ring
  eta_J x y := by simp [etaC, rotJ]; ring
  eta_pos x hx := by
    have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (by ext i; fin_cases i <;> simp [hc.1, hc.2])
    simp only [etaC, LinearMap.mk₂_apply]
    rcases h with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 1)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0)]
  omega_eq x y := by simp [etaC, omegaOne, rotJ]; ring

/-- The Gram kernel of the one-mode covariance is positive semidefinite. -/
instance : Fact (qfKerM omegaOne (etaC 1)).PosSemidef :=
  qfFact omegaOne (etaC 1) oneModeStructure.omega_antisymm oneModeStructure.isCovariance

/-- **One mode**: the quasi-free state of the Euclidean covariance is pure. -/
theorem isPureState_oneMode :
    IsPureState (qfState omegaOne (etaC 1) oneModeStructure.omega_antisymm) :=
  isPureState_qfState_of_complexStructure oneModeStructure

/-- **Wrong input**: for the doubled covariance `2 η` and the same `ω` there is no compatible complex structure. -/
theorem not_compatible_thermal : IsEmpty (CompatibleComplexStructure omegaOne (etaC 2)) := by
  refine ⟨fun S => ?_⟩
  have h1 := S.omega_eq (Pi.single 0 1) (S.J (Pi.single 0 1))
  rw [S.J_sq] at h1
  have h2 := S.eta_J (Pi.single 0 1) (Pi.single 0 1)
  set p := S.J (Pi.single 0 1) 0 with hp
  set q := S.J (Pi.single 0 1) 1 with hq
  simp [etaC, omegaOne] at h1 h2
  nlinarith [h1, h2]

end Lightlike.OperatorAlgebras.QuasiFreeState
