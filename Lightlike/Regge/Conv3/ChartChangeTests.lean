import Lightlike.Regge.Conv3.ChartChangeGeneral
import Lightlike.Regge.Conv3.ChartChangeGeneral

/-!
# Trust checks for the jet-level star identity at a general point

* The Euclidean metric satisfies the hypotheses of `jetStarCore_of_chart` (`euclid_chart_core`).
* The metric `diag(exp x₀, 1, 1)` is Riemannian on all of `ℝ³` and has first derivative `∂₀ g₀₀ = 1`
  at the origin (`expMetric_grad`), so `jetStarCore_of_flat`, which needs all first derivatives to
  vanish, does not apply to it (`expMetric_not_flat`), while `jetStarCore_of_chart` does
  (`expMetric_core`). This is the case the general-chart theorem adds.
-/

open Real Matrix Lightlike
open scoped ContDiff
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

/-- The metric `diag(exp x₀, 1, 1)`. -/
noncomputable def expMetric : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => Matrix.diagonal ![Real.exp (x 0), 1, 1]

/-- `expMetric` is a Riemannian metric on `ℝ³`. -/
theorem isRiemMetric_expMetric : IsRiemMetric expMetric Set.univ where
  coord := by
    have := isCoordMetric_diagonal (n := 3) (fun y => ![Real.exp (y 0), 1, 1]) (U := Set.univ)
      isOpen_univ (fun i => by
        fin_cases i
        · have h : ContDiff ℝ ∞ (fun y : Fin 3 → ℝ => Real.exp (y 0)) := by fun_prop
          simpa using h.contDiffOn
        · simpa using contDiffOn_const
        · simpa using contDiffOn_const)
      (fun x _ i => by fin_cases i <;> simp [(Real.exp_pos (x 0)).ne'])
    unfold expMetric
    exact this
  posDef := fun x _ => by
    rw [expMetric, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> simp [Real.exp_pos]

/-- The first derivative `∂₀ g₀₀` of `expMetric` at `0` is `1`. -/
theorem expMetric_grad : pd 0 (fun y => expMetric y 0 0) 0 = 1 := by
  have h : HasFDerivAt (fun y : Fin 3 → ℝ => Real.exp (y 0))
      (Real.exp ((0 : Fin 3 → ℝ) 0) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0)) 0 :=
    (Real.hasDerivAt_exp _).comp_hasFDerivAt (0 : Fin 3 → ℝ)
      (hasFDerivAt_apply (0 : Fin 3) (0 : Fin 3 → ℝ))
  have h2 : (fun y => expMetric y 0 0) = fun y : Fin 3 → ℝ => Real.exp (y 0) := by
    funext y; simp [expMetric]
  rw [h2]
  unfold pd
  rw [h.fderiv]
  simp

/-- The first derivatives of `expMetric` at `0` do not all vanish, so `jetStarCore_of_flat` does
not apply to it. -/
theorem expMetric_not_flat : ¬ ∀ k i j, pd k (fun y => expMetric y i j) 0 = 0 := by
  intro h
  have := h 0 0 0
  rw [expMetric_grad] at this
  norm_num at this

/-- Non-vacuity: the Euclidean metric satisfies the hypotheses of the general-chart theorem. -/
theorem euclid_chart_core (m : Fin 3 → ℝ) :
    JetStarCore (euclid : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) m :=
  jetStarCore_of_chart (isRiemMetric_euclid isOpen_univ) (Set.mem_univ m)

/-- **The case the general-chart theorem adds:** `JetStarCore` for a metric with a nonzero first
derivative at the point. -/
theorem expMetric_core : JetStarCore expMetric 0 :=
  jetStarCore_of_chart isRiemMetric_expMetric (Set.mem_univ 0)

end Lightlike.Regge.Conv3
