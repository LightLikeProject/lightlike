import Mathlib
import Lightlike.Spacetime.Lorentzian
import Lightlike.Spacetime.Corners.CovDerivTransport

/-!
# A nondegenerate metric for a transported model

For `e : E ≃L[ℝ] F` and `I' = I.transContinuousLinearEquiv e`, a metric `g` for `I` gives the metric `g'(v, w) = g(e⁻¹ v, e⁻¹ w)`
for `I'` (`transMetric`): symmetric and nondegenerate as `g` is, and smooth by the transport of the smoothness of sections of the bundle of
bilinear forms (`contMDiffAt_bilinSection_trans_iff`).
-/

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem inCoordinates_form_trans (e : E ≃L[ℝ] F) (x₀ x : M) (hx : x ∈ (chartAt H x₀).source)
    (β : TangentSpace I x →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e)) ℝ (fun _ : M => ℝ)
      x₀ x x₀ x (β.comp (e.symm : F →L[ℝ] E)) =
    (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ) x₀ x x₀ x β) := by
  unfold ContinuousLinearMap.inCoordinates
  rw [TangentBundle.symmL_trivializationAt_eq_core hx, TangentBundle.symmL_trivializationAt_eq_core (I := I) hx]
  ext v
  have h1 : (tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x v =
      e (tangentCoordChange I x₀ x x (e.symm v)) := tangentCoordChange_transContinuousLinearEquiv e x₀ x x v
  have key : e.symm ((tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x v) =
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x (e.symm v) := by
    rw [h1]; exact e.symm_apply_apply _
  exact congrArg (Trivialization.continuousLinearMapAt ℝ (trivializationAt ℝ (fun _ : M => ℝ) x₀) x)
    (congrArg β key)

theorem contMDiffAt_formSection_trans_iff (e : E ≃L[ℝ] F) {n : WithTop ℕ∞}
    (β : Π y : M, TangentSpace I y →L[ℝ] ℝ) {x : M} :
    ContMDiffAt (I.transContinuousLinearEquiv e) ((I.transContinuousLinearEquiv e).prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y => (⟨y, (β y).comp (e.symm : F →L[ℝ] E)⟩ :
        TotalSpace (F →L[ℝ] ℝ) (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ] ℝ))) x ↔
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun y => (⟨y, β y⟩ : TotalSpace (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ))) x := by
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  refine and_congr ?_ ?_
  · exact ⟨fun _ => contMDiffAt_id, fun _ => contMDiffAt_id⟩
  · have hev : (fun y : M => ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e)) ℝ
        (fun _ : M => ℝ) x y x y ((β y).comp (e.symm : F →L[ℝ] E))) =ᶠ[nhds x]
        fun y => (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
          (ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ) x y x y (β y)) := by
      filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
      exact inCoordinates_form_trans e x y hy (β y)
    refine (hev.contMDiffAt_iff).trans ?_
    rw [contMDiffAt_linEquiv_comp_iff (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))
      (fun y => ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ) x y x y (β y))
      (J := I.transContinuousLinearEquiv e)]
    exact contMDiffAt_transContinuousLinearEquiv_iff e

theorem clmAt_form_bundle (x₀ x : M) (hx : x ∈ (chartAt H x₀).source) (ψ : TangentSpace I x →L[ℝ] ℝ) :
    (trivializationAt (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ) x₀).continuousLinearMapAt ℝ x ψ =
      ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ) x₀ x x₀ x ψ := by
  have hb : x ∈ (trivializationAt (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨hx, by simp⟩
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_def_of_mem _ hb]
  rfl

/-- The transport of a field of bilinear forms: `B' (v, w) = B (e⁻¹ v, e⁻¹ w)`. -/
def transBilin (e : E ≃L[ℝ] F) : (E →L[ℝ] E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
  e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

theorem inCoordinates_bilin_trans (e : E ≃L[ℝ] F) (x₀ x : M) (hx : x ∈ (chartAt H x₀).source)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e)) (F →L[ℝ] ℝ)
      (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ] ℝ) x₀ x x₀ x (transBilin e B) =
    transBilin e (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] ℝ) x₀ x x₀ x B) := by
  unfold ContinuousLinearMap.inCoordinates
  rw [TangentBundle.symmL_trivializationAt_eq_core hx, TangentBundle.symmL_trivializationAt_eq_core (I := I) hx]
  ext w v
  have hL := clmAt_form_bundle (I := I.transContinuousLinearEquiv e) x₀ x hx
  have hR := clmAt_form_bundle (I := I) x₀ x hx
  have h1 : (tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x w =
      e (tangentCoordChange I x₀ x x (e.symm w)) := tangentCoordChange_transContinuousLinearEquiv e x₀ x x w
  have key : e.symm ((tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x w) =
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x (e.symm w) := by
    rw [h1]; exact e.symm_apply_apply _
  have hbil : (transBilin e B) ((tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x w) =
      (B ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x (e.symm w))).comp (e.symm : F →L[ℝ] E) := by
    ext u
    exact congrArg (fun z : E => (B z) (e.symm u)) key
  have hgoal : ((trivializationAt (F →L[ℝ] ℝ) (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ] ℝ) x₀).continuousLinearMapAt ℝ x
      ((transBilin e B) ((tangentBundleCore (I.transContinuousLinearEquiv e) M).coordChange (achart H x₀) (achart H x) x w))) v =
    ((trivializationAt (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ) x₀).continuousLinearMapAt ℝ x
      (B ((tangentBundleCore I M).coordChange (achart H x₀) (achart H x) x (e.symm w)))) (e.symm v) := by
    rw [hbil]
    exact (congrArg (fun f => f v) (hL _)).trans
      ((congrArg (fun f => f v) (inCoordinates_form_trans e x₀ x hx _)).trans
        (congrArg (fun f => f (e.symm v)) (hR _).symm))
  exact hgoal

theorem contMDiffAt_bilinSection_trans_iff (e : E ≃L[ℝ] F) {n : WithTop ℕ∞}
    (B : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) {x : M} :
    ContMDiffAt (I.transContinuousLinearEquiv e) ((I.transContinuousLinearEquiv e).prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y => (⟨y, transBilin e (B y)⟩ :
        TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ]
          TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ] ℝ))) x ↔
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun y => (⟨y, B y⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ]
        TangentSpace I y →L[ℝ] ℝ))) x := by
  rw [contMDiffAt_hom_bundle, contMDiffAt_hom_bundle]
  refine and_congr ?_ ?_
  · exact ⟨fun _ => contMDiffAt_id, fun _ => contMDiffAt_id⟩
  · have hev : (fun y : M => ContinuousLinearMap.inCoordinates F (TangentSpace (I.transContinuousLinearEquiv e))
        (F →L[ℝ] ℝ) (fun y : M => TangentSpace (I.transContinuousLinearEquiv e) y →L[ℝ] ℝ) x y x y
        (transBilin e (B y))) =ᶠ[nhds x]
        fun y => transBilin e (ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
          (fun y : M => TangentSpace I y →L[ℝ] ℝ) x y x y (B y)) := by
      filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
      exact inCoordinates_bilin_trans e x y hy (B y)
    refine (hev.contMDiffAt_iff).trans ?_
    rw [contMDiffAt_linEquiv_comp_iff (G := E →L[ℝ] E →L[ℝ] ℝ) (G' := F →L[ℝ] F →L[ℝ] ℝ) (transBilin e)
      (fun y => ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) x y x y (B y)) (J := I.transContinuousLinearEquiv e)]
    exact contMDiffAt_transContinuousLinearEquiv_iff e

variable [IsManifold I ∞ M]

/-- **The metric transported to the model `I.transContinuousLinearEquiv e`**: `g'(v, w) = g(e⁻¹ v, e⁻¹ w)`. -/
def transMetric (e : E ≃L[ℝ] F) (g : NondegMetric I M) : NondegMetric (I.transContinuousLinearEquiv e) M where
  g x := transBilin e (g.g x)
  symm x v w := g.symm x (e.symm v) (e.symm w)
  nondegenerate x v h := by
    have h0 : ∀ u : TangentSpace I x, g.g x (e.symm v) u = 0 := fun u => by
      have h1 := h (e u)
      change (g.g x (e.symm v)) (e.symm (e u)) = 0 at h1
      erw [e.symm_apply_apply] at h1
      exact h1
    have := g.nondegenerate x (e.symm v) h0
    exact (e.apply_symm_apply v).symm.trans ((congrArg e this).trans (map_zero e))
  contMDiff := by
    intro x
    exact (contMDiffAt_bilinSection_trans_iff e (n := ∞) (fun y => g.g y)).2 (g.contMDiff x)

end Lightlike
