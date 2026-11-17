import Lightlike.Spacetime.Causal.CausalCurve
import Lightlike.Spacetime.Causal.SmoothOrientation

/-!
# The chart derivative of a curve is the velocity in the trivialization

For a curve `γ` that is differentiable within `s` at `t`, with `γ t` in the chart at `p`, the
derivative of the chart coordinates `extChartAt I p ∘ γ` is the second component of the image of
the velocity `velocity I γ s t` in the tangent-bundle trivialization around `p`. This is the bridge
between the manifold definition of a causal curve (`Lightlike.Causal.IsCurveWith`) and the
coordinate estimates of the causal ladder.

Supporting lemma; no catalogue entry. The proof follows Mathlib's
`IsMIntegralCurveOn.hasDerivWithinAt`, which treats integral curves.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the chart coordinates of a curve at `p` is the velocity in the trivialization
of the tangent bundle around `p`. -/
theorem hasDerivWithinAt_chart_comp {γ : ℝ → M} {s : Set ℝ} {t : ℝ} (p : M)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    (hsrc : γ t ∈ (extChartAt I p).source) :
    HasDerivWithinAt (extChartAt I p ∘ γ) ((tTriv I M p ⟨γ t, velocity I γ s t⟩).2) s t := by
  replace hsrc := extChartAt_source I p ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc)
    hγ.hasMFDerivWithinAt (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply]
  have ha : (mfderiv[s] γ t) a = (id a : ℝ) • (velocity I γ s t : E) := by
    have := (mfderivWithin 𝓘(ℝ, ℝ) I γ s t).map_smul (id a : ℝ) (1 : ℝ)
    simpa [velocity] using this
  rw [ha, map_smul]
  have h2 : (mfderiv% (chartAt H p) (γ t)) (velocity I γ s t) =
      (tTriv I M p ⟨γ t, velocity I γ s t⟩).2 := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hsrc]
    rfl
  exact congrArg (fun w : E => (id a : ℝ) • w) h2

end Lightlike.Causal
