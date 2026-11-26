import Mathlib
import Lightlike.Spacetime.Corners.TangentTransport

/-!
# The Lie bracket for a transported model

For `e : E ≃L[ℝ] F` and `I' = I.transContinuousLinearEquiv e`, the Lie bracket of two transported vector fields is the transport of
the Lie bracket: `mlieBracket I' (transSection e X) (transSection e Y) x = e (mlieBracket I X Y x)`
(`mlieBracket_transSection`), when the fields are differentiable at `x`. The proof applies the naturality of the Lie bracket
(Mathlib: `VectorField.mpullback_mlieBracket`) to the identity of `M`, seen as a smooth map from the manifold modelled on `I` to the
one modelled on `I'`, whose derivative is `e`.

**Limits.** Fields differentiable at the point; the model space `F` is arbitrary (not necessarily `Fin n → ℝ`).
-/

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The derivative of the identity of `M`, from the model `I` to the model `I.transContinuousLinearEquiv e`, is `e`. -/
theorem mfderiv_id_transContinuousLinearEquiv (e : E ≃L[ℝ] F) [IsManifold I 1 M] (x : M) :
    mfderiv I (I.transContinuousLinearEquiv e) (id : M → M) x = (e : E →L[ℝ] F) := by
  have h : HasMFDerivAt I I (id : M → M) x (ContinuousLinearMap.id ℝ (TangentSpace I x)) := hasMFDerivAt_id x
  have := hasMFDerivAt_transContinuousLinearEquiv_right e h
  exact this.mfderiv.trans (by ext; rfl)

/-- The identity of `M` is smooth from the model `I` to the model `I.transContinuousLinearEquiv e`. -/
theorem contMDiffAt_id_transContinuousLinearEquiv (e : E ≃L[ℝ] F) [IsManifold I 1 M] {n : WithTop ℕ∞} (x : M) :
    ContMDiffAt I (I.transContinuousLinearEquiv e) n (id : M → M) x := by
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  have h1 : ContDiffWithinAt ℝ n (e : E → F) (range I) (extChartAt I x x) := e.contDiff.contDiffWithinAt
  refine h1.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    show e (extChartAt I x ((extChartAt I x).symm y)) = e y
    rw [(extChartAt I x).right_inv hy]
  · show e (extChartAt I x ((extChartAt I x).symm (extChartAt I x x))) = e (extChartAt I x x)
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]

/-- **The Lie bracket of transported vector fields is the transport of the Lie bracket.** -/
theorem mlieBracket_transSection [CompleteSpace E] [CompleteSpace F] (e : E ≃L[ℝ] F) [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
    {X Y : Π y : M, TangentSpace I y} {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    mlieBracket (I.transContinuousLinearEquiv e) (transSection e X) (transSection e Y) x =
      e (mlieBracket I X Y x) := by
  have hinv : ∀ y : M, (mfderiv I (I.transContinuousLinearEquiv e) (id : M → M) y).inverse = (e.symm : F →L[ℝ] E) := by
    intro y
    rw [mfderiv_id_transContinuousLinearEquiv e y]
    exact ContinuousLinearMap.inverse_equiv e
  have hpb : ∀ (Z : Π y : M, TangentSpace I y),
      mpullback I (I.transContinuousLinearEquiv e) (id : M → M) (transSection e Z) = Z := by
    intro Z
    funext y
    simp only [mpullback, hinv y]
    exact e.symm_apply_apply (Z y)
  have hV : MDifferentiableAt (I.transContinuousLinearEquiv e) (I.transContinuousLinearEquiv e).tangent
      (fun y => (⟨y, transSection e X y⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)) (id x) :=
    (mdifferentiableAt_transSection_iff e X x).2 hX
  have hW : MDifferentiableAt (I.transContinuousLinearEquiv e) (I.transContinuousLinearEquiv e).tangent
      (fun y => (⟨y, transSection e Y y⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)) (id x) :=
    (mdifferentiableAt_transSection_iff e Y x).2 hY
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have h := mpullback_mlieBracket (I := I) (I' := I.transContinuousLinearEquiv e) (n := ∞) hV hW
    (contMDiffAt_id_transContinuousLinearEquiv e x) (by simp)
  rw [hpb, hpb] at h
  have h2 : (mlieBracket I X Y x) = e.symm (mlieBracket (I.transContinuousLinearEquiv e) (transSection e X)
      (transSection e Y) x) := by
    rw [← h]; simp only [mpullback, hinv x]; rfl
  rw [h2]; exact (e.apply_symm_apply _).symm

end Lightlike
