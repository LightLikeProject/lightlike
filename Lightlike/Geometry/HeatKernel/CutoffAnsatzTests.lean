import Mathlib
import Lightlike.Geometry.HeatKernel.CutoffAnsatz
import Lightlike.Geometry.HeatKernel.TransportEquationsTests

/-!
# Tests: the cut-off ansatz

With the constant cutoff `θ ≡ 1` the cutoff terms vanish (`cutoff_terms_eq_zero_of_eventuallyEq_one`), and on the
line with the free coefficients (`u₀ = 1`, `u_k = 0`) `heatOperator_cutoff_ansatz` applies (non-vacuity): the right side
is then `0`, the free heat kernel solving the heat equation.
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.CutoffAnsatzTests

open Lightlike.LaplaceBeltramiTests Lightlike.GaussianAnsatzTests Lightlike.TransportEquationsTests

/-- The constant cutoff contributes nothing. -/
example (Φ : (Fin 1 → ℝ) → ℝ) (y : Fin 1 → ℝ) :
    coordLaplacian gLine (fun _ => (1 : ℝ)) y = 0 ∧ coordGradPair gLine (fun _ => (1 : ℝ)) Φ y = 0 :=
  cutoff_terms_eq_zero_of_eventuallyEq_one (Filter.EventuallyEq.rfl)

/-- Non-vacuity on the line with the free coefficients and the constant cutoff. -/
example (N : ℕ) {t : ℝ} (ht : 0 < t) (y : Fin 1 → ℝ) :
    ∃ D, HasDerivAt (fun s => (fun _ => (1 : ℝ)) y * (heatGaussian 1 (σLine y) s * truncAnsatz uFree N s y)) D t ∧
      D + (4 * Real.pi * t) ^ (-((1 : ℕ) : ℝ) / 2) *
          coordLaplacian gLine (fun z => (fun _ => (1 : ℝ)) z * (gaussFactor t (σLine z) * truncAnsatz uFree N t z)) y =
        (fun _ => (1 : ℝ)) y * (heatGaussian 1 (σLine y) t * (t ^ N * coordLaplacian gLine (uFree N) y)) +
          (4 * Real.pi * t) ^ (-((1 : ℕ) : ℝ) / 2) *
            (gaussFactor t (σLine y) * truncAnsatz uFree N t y * coordLaplacian gLine (fun _ => (1 : ℝ)) y -
              2 * coordGradPair gLine (fun _ => (1 : ℝ)) (fun z => gaussFactor t (σLine z) * truncAnsatz uFree N t z) y) :=
  heatOperator_cutoff_ansatz isCoordMetric_gLine
    ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).mul (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)).contDiffOn
    (fun k => contDiffOn_const) (fun z _ => congrFun eikonal_σLine z) (isTransport_free N) contDiff_const ht
    (mem_univ y)

end Lightlike.CutoffAnsatzTests
