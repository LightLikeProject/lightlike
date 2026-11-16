import Lightlike.Regge.Conv3.ReggeConvergence

/-!
# Trust checks for the convergence of the 3D Regge action

`regge3d_tendsto` is not vacuous: its hypotheses hold for the flat metric (limit `0`) and for the round
`S³` in stereographic coordinates `g = 4/(1+|x|²)² δ`, which has scalar curvature `6` (`sphere_regge_tendsto`).
The definition of `reggeAction3` is checked numerically, from true geodesic lengths, in
`scripts/regge/regge3d_sphere_check.py`: the action of the sphere approaches `∫ (R/2) √det g ≈ 4.5712` with
the error halving as `N` doubles (an observation; the theorem gives no rate).
-/

open Real Matrix Lightlike Filter Topology MeasureTheory
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

/-- The scalar curvature of the Euclidean metric vanishes. -/
theorem scalarCurvature_euclid (y : Fin 3 → ℝ) :
    scalarCurvature (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) y = 0 := by
  have h : (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) = fun _ => (1 : Matrix (Fin 3) (Fin 3) ℝ) := rfl
  rw [h]
  simp [scalarCurvature, ricci, riemann_const]

/-- Non-vacuity: the hypotheses of `regge3d_tendsto` hold for the Euclidean metric on `ℝ³`, and the
Regge action of the Kuhn grid tends to `0`, the integral of half its (zero) scalar curvature. -/
theorem euclid_regge_tendsto :
    Tendsto (fun N : ℕ => reggeAction3 (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) Set.univ N)
      atTop (𝓝 0) := by
  have := regge3d_tendsto (isRiemMetric_euclid (n := 3) isOpen_univ) (Set.subset_univ _)
  simpa [scalarCurvature_euclid] using this


open scoped ContDiff in
/-- The round 3-sphere in stereographic coordinates, `g = 4/(1+|x|²)² δ`: a non-flat metric
(scalar curvature `6`) on all of `ℝ³`. -/
noncomputable def sphereMetric : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => Matrix.diagonal fun _ => 4 / (1 + ∑ j, x j ^ 2) ^ 2

open scoped ContDiff in
/-- The stereographic metric of the round 3-sphere is a Riemannian metric on `ℝ³`. -/
theorem isRiemMetric_sphereMetric : IsRiemMetric sphereMetric Set.univ where
  coord := by
    have := isCoordMetric_diagonal (n := 3) (fun y _ => 4 / (1 + ∑ j, y j ^ 2) ^ 2) (U := Set.univ)
      isOpen_univ (fun i => by
        have h : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => 4 / (1 + ∑ j, y j ^ 2) ^ 2) := by
          refine contDiff_const.div ((contDiff_const.add ?_).pow 2) (fun y => by positivity)
          exact ContDiff.sum fun j _ => (by fun_prop : ContDiff ℝ ∞ fun x : Fin 3 → ℝ => x j ^ 2)
        exact h.contDiffOn)
      (fun x _ i => by positivity)
    exact this
  posDef := fun x _ => by
    rw [sphereMetric, Matrix.posDef_diagonal_iff]
    intro i; positivity

/-- Non-vacuity for a non-flat metric: the round 3-sphere satisfies the hypotheses of `regge3d_tendsto`,
so its Regge action converges to `∫ (R/2) √det g` over the unit cube (numerically `≈ 4.5712`, see
`scripts/regge/regge3d_sphere_check.py`). -/
theorem sphere_regge_tendsto :
    Tendsto (fun N : ℕ => reggeAction3 sphereMetric Set.univ N) atTop
      (𝓝 (∫ y in unitCube, scalarCurvature sphereMetric y / 2 * √((sphereMetric y).det))) :=
  regge3d_tendsto isRiemMetric_sphereMetric (Set.subset_univ _)

end Lightlike.Regge.Conv3
