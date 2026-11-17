import Lightlike.Regge.Linear3.TorusConvergence
import Lightlike.Regge.Conv3.ReggeConvergenceTests

/-!
# Trust checks for the convergence of the Regge action of the periodic Kuhn complex

`torus_regge_converges` is not vacuous: its hypotheses hold for the Euclidean metric (the flat torus: the
Regge action of the complex tends to `0`, `euclid_torus`) and for the periodic non-constant conformal metric
`g = (2 + cos 2π x₀) δ` (`cosMetric_torus`). The scalar curvature of `cosMetric` is not computed here, so
its non-flatness is not claimed in Lean. The hinge sum of `reggeAction3` that the complex action equals
(`reggeAction_torus_eq`) is checked numerically from true geodesic lengths on the round `S³` chart in
`scripts/regge/regge3d_sphere_check.py`, and the second-order coefficient of the action of the periodic
complex with Christiansen's interpolated lengths in `scripts/regge/regge3d_linearized_check.py`.
-/

open Real Filter Topology MeasureTheory
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3 Lightlike.Geodesic

/-- A periodic non-constant conformal metric `g = (2 + cos (2π x₀)) δ` on `ℝ³`. -/
noncomputable def cosMetric : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => Matrix.diagonal fun _ => 2 + Real.cos (2 * π * x 0)

open scoped ContDiff in
theorem isRiemMetric_cosMetric : IsRiemMetric cosMetric Set.univ where
  coord := by
    have := isCoordMetric_diagonal (n := 3) (fun y _ => 2 + Real.cos (2 * π * y 0)) (U := Set.univ)
      isOpen_univ (fun i => by
        have h : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => 2 + Real.cos (2 * π * y 0)) := by
          fun_prop
        exact h.contDiffOn)
      (fun x _ i => by linarith [Real.neg_one_le_cos (2 * π * x 0)])
    exact this
  posDef := fun x _ => by
    rw [cosMetric, Matrix.posDef_diagonal_iff]
    intro i
    linarith [Real.neg_one_le_cos (2 * π * x 0)]

theorem cosMetric_periodic (p : Fin 3 → ℝ) (e : Fin 3 → ℤ) :
    cosMetric (p + fun i => (e i : ℝ)) = cosMetric p := by
  unfold cosMetric
  have : 2 * π * (p 0 + (e 0 : ℝ)) = 2 * π * p 0 + (e 0 : ℤ) * (2 * π) := by ring
  simp only [Pi.add_apply, this, Real.cos_add_int_mul_two_pi]

/-- **Non-vacuity of the torus convergence for a non-constant periodic metric.** -/
theorem cosMetric_torus (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N] (hN : 3 ≤ N), N0 ≤ N →
      |reggeAction (torusComplex N (by omega)) (lenD N (Geodesic.dist cosMetric Set.univ)) -
        ∫ y in unitCube, scalarCurvature cosMetric y / 2 * √((cosMetric y).det)| < ε :=
  torus_regge_converges isRiemMetric_cosMetric cosMetric_periodic ε hε

/-- The flat torus: for the Euclidean metric the Regge action of the periodic complex tends to `0`. -/
theorem euclid_torus (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N] (hN : 3 ≤ N), N0 ≤ N →
      |reggeAction (torusComplex N (by omega))
        (lenD N (Geodesic.dist (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) Set.univ))| < ε := by
  have := torus_regge_converges (isRiemMetric_euclid (n := 3) isOpen_univ) (fun p e => rfl) ε hε
  simpa [scalarCurvature_euclid] using this

end Lightlike.Regge.Linear3
