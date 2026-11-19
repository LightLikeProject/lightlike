import Lightlike.Gauge.Orbits.GaugeOrbits

/-!
# Checks for the gauge orbits theorem

The single constraint `γ (p, q) = p` on the phase space `ℝ × ℝ` satisfies the hypotheses of
`Lightlike.Gauge.exists_gauge_orbit`: it is first class with structure functions `0`, and its
gradient `(1, 0)` is nonzero. Its gauge orbits are the lines `p = 0`, `q` free.
-/

open Set Metric ClassicalMechanics

noncomputable section

namespace Lightlike.Gauge.Tests

/-- The constraint `γ (p, q) = p`. -/
def momentumConstraint : Fin 1 → ℝ → ℝ → ℝ := fun _ p _ => p

/-- **Non-vacuity of `IsFirstClassWith`**: one constraint, structure functions `0`. -/
theorem isFirstClassWith_momentum :
    IsFirstClassWith momentumConstraint (fun _ _ _ _ => (0 : ℝ)) := by
  refine ⟨fun _ _ _ => contDiff_const, fun a b z => ?_⟩
  simp [momentumConstraint, poissonBracket]

/-- The gradient of the constraint `γ (p, q) = p` is nonzero at every point. -/
theorem phaseGrad_momentum_ne_zero (x : ℝ × ℝ) :
    phaseGrad (momentumConstraint 0) x.1 x.2 ≠ 0 := by
  intro h0
  have h1 := fderiv_apply_eq_pairing (momentumConstraint 0) (p := x.1) (q := x.2)
    (show DifferentiableAt ℝ (fun z : ℝ × ℝ => z.1) (x.1, x.2) from differentiableAt_fst)
    ((1 : ℝ), (0 : ℝ))
  rw [h0] at h1
  have h2 : fderiv ℝ (fun z : ℝ × ℝ => momentumConstraint 0 z.1 z.2) (x.1, x.2) (1, 0) = 1 := by
    show fderiv ℝ (fun z : ℝ × ℝ => z.1) (x.1, x.2) (1, 0) = 1
    rw [fderiv_fst]
    rfl
  rw [h2] at h1
  simp [pairing] at h1

/-- **Non-vacuity of `exists_gauge_orbit`**: the constraint `γ (p, q) = p` on `ℝ × ℝ`. -/
theorem exists_gauge_orbit_momentum (x₀ : ℝ × ℝ) :
    ∃ (ε : ℝ) (f : (Fin 1 → ℝ) × (ℝ × ℝ) → ℝ × ℝ)
      (f' : (Fin 1 → ℝ) × (ℝ × ℝ) → ((Fin 1 → ℝ) × (ℝ × ℝ) →L[ℝ] ℝ × ℝ)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x) ∧
      ∀ t ∈ ball (0 : Fin 1 → ℝ) ε, ∀ x ∈ ball x₀ ε, x ∈ constraintSet momentumConstraint →
        f (t, x) ∈ constraintSet momentumConstraint ∧ HasFDerivAt f (f' (t, x)) (t, x) ∧
        Function.Injective (fun τ : Fin 1 → ℝ => f' (t, x) (τ, 0)) ∧
        range (fun τ : Fin 1 → ℝ => f' (t, x) (τ, 0)) =
          (hamSpan momentumConstraint (f (t, x)).1 (f (t, x)).2 : Set (ℝ × ℝ)) :=
  exists_gauge_orbit momentumConstraint (fun _ => contDiff_fst) isFirstClassWith_momentum
    (linearIndependent_unique_iff.2 (phaseGrad_momentum_ne_zero x₀))

end Lightlike.Gauge.Tests
