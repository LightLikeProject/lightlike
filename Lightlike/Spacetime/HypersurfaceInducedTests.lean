import Lightlike.Spacetime.HypersurfaceInduced
import Lightlike.Spacetime.SphereHypersurface
import Lightlike.Spacetime.Minkowski

/-!
# Tests of the induced metric of a level set

* `sphere_inducedMetric_separating`: non-vacuity, the unit sphere in a Euclidean space has a nondegenerate induced
  metric at every point `x₀ ≠ 0` (through `inducedMetric_separating_of_isUnitNormal` and `isUnitNormal_sphere`);
* `null_inducedMetric_not_separating`: the wrong-model control, the null hyperplane `t = x` of the Minkowski plane has
  a nonzero tangent vector `(1, 1)` orthogonal to all tangent vectors, so its induced metric is degenerate and the
  hypothesis that the normal is not null cannot be dropped from the nondegeneracy theorem.
-/

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Hypersurface.Tests

/-- **Non-vacuity**: on a sphere `‖y‖² = r²` the induced metric at `x₀ ≠ 0` is nondegenerate. -/
theorem sphere_inducedMetric_separating {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {x₀ : F} (hx₀ : x₀ ≠ 0)
    (v : levelTangent (E := F) (fun y : F => ‖y‖ ^ 2) x₀)
    (hv : ∀ w : levelTangent (E := F) (fun y : F => ‖y‖ ^ 2) x₀,
      inducedMetric (euclMetric F) (fun y : F => ‖y‖ ^ 2) x₀ v w = 0) : v = 0 :=
  inducedMetric_separating_of_isUnitNormal (euclMetric F) (isUnitNormal_sphere hx₀) v hv

/-- The null function `φ(t, x) = t − x` on the Minkowski plane. -/
def nullFn : (Fin 2 → ℝ) → ℝ := fun y => y 0 - y 1

/-- **Wrong-model control**: for the null hyperplane `t = x` of the Minkowski plane there is a nonzero vector of
the tangent space of the level set that is `η`-orthogonal to every tangent vector, so the induced metric is degenerate. -/
theorem null_inducedMetric_not_separating (p : Fin 2 → ℝ) :
    ∃ v : levelTangent (E := Fin 2 → ℝ) nullFn p, v ≠ 0 ∧
      ∀ w : levelTangent (E := Fin 2 → ℝ) nullFn p,
        inducedMetric (minkowskiMetric 2).toNondegMetric nullFn p v w = 0 := by
  set L : (Fin 2 → ℝ) →L[ℝ] ℝ := (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) with hL
  have hd : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ) nullFn p = L := by
    rw [mfderiv_eq_fderiv]
    exact (L.hasFDerivAt (x := p)).fderiv
  have key : ∀ u : Fin 2 → ℝ, L u = 0 ↔ u 0 = u 1 := by
    intro u
    simp [hL, sub_eq_zero]
  have hmem : ∀ u : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p,
      u ∈ levelTangent (E := Fin 2 → ℝ) nullFn p ↔ (show Fin 2 → ℝ from u) 0 = (show Fin 2 → ℝ from u) 1 := by
    intro u
    rw [mem_levelTangent, hd]
    exact key u
  have h1 : (fun _ : Fin 2 => (1 : ℝ)) ∈ levelTangent (E := Fin 2 → ℝ) nullFn p :=
    (hmem (fun _ : Fin 2 => (1 : ℝ))).2 rfl
  refine ⟨⟨fun _ => 1, h1⟩, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun z : levelTangent (E := Fin 2 → ℝ) nullFn p =>
      (show Fin 2 → ℝ from (z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p)) 0) h
    exact one_ne_zero h0
  · intro w
    have hw := (hmem _).1 w.2
    change minkowskiForm 2 (fun _ : Fin 2 => (1 : ℝ)) (show Fin 2 → ℝ from (w : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p)) = 0
    rw [minkowskiForm_apply, Fin.sum_univ_two]
    simp only [etaDiag]
    norm_num
    have hw' : (w : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p) 0 = (w : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p) 1 := hw
    linarith

end Lightlike.Hypersurface.Tests
