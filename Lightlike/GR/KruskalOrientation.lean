import Lightlike.GR.KruskalManifold
import Lightlike.Spacetime.Causal.TimeOrientation
import Lightlike.Spacetime.OpenCoordMetric

/-!
# The time orientation of the Kruskal manifold

Gap row G1-020. On the Kruskal manifold in its global chart `(T, x)` the coordinate field `∂_T` is timelike
everywhere, `g(∂_T, ∂_T) = -h(r) < 0`, so it is a time orientation (`kruskalOrientation`): the Kruskal spacetime is
time orientable (`kruskal_timeOrientable`).
-/

open Matrix Real Set Filter Topology Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {M : ℝ}

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The time orientation `∂_T` of the Kruskal manifold.** -/
def kruskalOrientation (hM : 0 < M) : Causal.TimeOrientation (kruskalManifoldMetric M hM) where
  X _ := Pi.single 0 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have e : ∀ y : kruskalCOpen, ((trivializationAt (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) x)
        ⟨y, (Pi.single 0 1 : Fin 4 → ℝ)⟩).2 = Pi.single 0 1 := fun y => by
      have hb : y ∈ (trivializationAt (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) x).baseSet := by
        simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
      have h1 : (trivializationAt (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) x).continuousLinearMapAt ℝ y
          (Pi.single 0 1 : Fin 4 → ℝ) =
          ((trivializationAt (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) x)
            ⟨y, (Pi.single 0 1 : Fin 4 → ℝ)⟩).2 := by
        rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hb]
      rw [opens_continuousLinearMapAt] at h1
      exact h1.symm
    simp only [e]
    exact contMDiffAt_const
  timelike x := by
    show matForm (kruskalCMetric M x.1) (Pi.single 0 1) (Pi.single 0 1) < 0
    have h := kh_pos M hM (krC_pos M hM x.2)
    rw [matForm_apply]
    simp [kruskalCMetric, Fin.sum_univ_four]
    exact h

/-- The Kruskal spacetime is time orientable. -/
theorem kruskal_timeOrientable (hM : 0 < M) : Causal.TimeOrientable (kruskalManifoldMetric M hM) :=
  ⟨kruskalOrientation hM⟩

end Lightlike
