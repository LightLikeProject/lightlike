import Lightlike.Cosmology.BardeenPotentials.Bardeen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Non-vacuity tests for the Bardeen potentials (G1-030)

* an explicit perturbation with `Φ ≠ 0`, so it is not pure gauge (the hypotheses of the iff are satisfiable and the
  conclusion is not trivially true);
* a wrong-sign gauge law, which breaks the invariance of `Φ`, so the sign convention of `gauge` is load-bearing.
-/

namespace Lightlike
namespace Cosmology
namespace Perturbation
namespace Tests

/-- On the de Sitter-like scale factor `a = exp` the conformal Hubble rate is `1`. -/
theorem hubble_exp (η : ℝ) : hubble Real.exp η = 1 := by
  simp [hubble, Real.deriv_exp, Real.exp_ne_zero]

/-- A lapse perturbation `A = 1` with everything else zero. -/
def lapseOnly : ScalarPert := ⟨fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem lapseOnly_phi (η : ℝ) : bardeenPhi Real.exp lapseOnly η = 1 := by
  have hsh : shear lapseOnly = fun _ => 0 := by
    funext x
    simp [shear, lapseOnly]
  unfold bardeenPhi
  rw [hsh, hubble_exp]
  simp [lapseOnly]

/-- `lapseOnly` has `Φ = 1 ≠ 0`, hence is not pure gauge. -/
theorem lapseOnly_not_pureGauge :
    ¬ ∃ T L : ℝ → ℝ, Differentiable ℝ T ∧ Differentiable ℝ L ∧
        lapseOnly = gauge Real.exp T L ⟨0, 0, 0, 0⟩ := by
  have hc : ∀ c : ℝ, Differentiable ℝ (fun _ : ℝ => c) := fun c => differentiable_const c
  have h := bardeen_eq_zero_iff_pureGauge (a := Real.exp) (p := lapseOnly) (hc 0) (hc 0)
    (by
      have : deriv (lapseOnly.E) = fun _ => 0 := funext fun x => deriv_const x (0 : ℝ)
      rw [this]
      exact hc 0)
  intro hex
  have := (h.2 hex).1
  have h1 := congrFun this 0
  rw [lapseOnly_phi] at h1
  simp at h1

/-- A wrong-sign gauge law: `A ↦ A + T' + 𝓗 T` instead of `A - T' - 𝓗 T`. -/
noncomputable def gaugeBad (a T L : ℝ → ℝ) (p : ScalarPert) : ScalarPert where
  A := fun η => p.A η + deriv T η + hubble a η * T η
  B := fun η => p.B η + T η - deriv L η
  psi := fun η => p.psi η + hubble a η * T η
  E := fun η => p.E η - L η

/-- With the wrong sign `Φ` is not invariant: the transform of the zero perturbation by `T = 1`, `L = 0`
on `a = exp` has `Φ = 2 ≠ 0`. -/
theorem gaugeBad_breaks_phi :
    bardeenPhi Real.exp (gaugeBad Real.exp (fun _ => 1) (fun _ => 0) ⟨0, 0, 0, 0⟩) 0 ≠
      bardeenPhi Real.exp ⟨0, 0, 0, 0⟩ 0 := by
  have hsh : shear (gaugeBad Real.exp (fun _ => 1) (fun _ => 0) ⟨0, 0, 0, 0⟩) = fun _ => 1 := by
    funext x
    simp [shear, gaugeBad]
  have hsh0 : shear (⟨0, 0, 0, 0⟩ : ScalarPert) = fun _ => 0 := by
    funext x
    simp [shear]
  unfold bardeenPhi
  rw [hsh, hsh0, hubble_exp]
  simp [gaugeBad, hubble_exp]

end Tests
end Perturbation
end Cosmology
end Lightlike
