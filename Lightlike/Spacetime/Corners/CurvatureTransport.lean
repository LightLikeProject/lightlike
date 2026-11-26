import Mathlib
import Lightlike.Spacetime.Corners.MetricTransport
import Lightlike.Spacetime.Corners.CurvatureSymmetries
import Lightlike.Spacetime.Corners.BianchiSecond

/-!
# Curvature for a transported model

For `e : E ≃L[ℝ] F`, `I' = I.transContinuousLinearEquiv e`, `cov` a locally smooth connection for `I` and `cov' = transCov e cov`:
the extension of a tangent vector for `I'` is the transport of the extension of the transported vector (`extend_trans`), and the
curvature of `cov'` is the transport of the curvature of `cov`: `curvatureAt_trans`.
-/

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **The extension of a vector for the transported model** is, on the chart domain, the transport of the extension of the
transported vector. -/
theorem extend_trans (e : E ≃L[ℝ] F) (x : M) (v : TangentSpace (I.transContinuousLinearEquiv e) x) (y : M)
    (hy : y ∈ (chartAt H x).source) :
    (FiberBundle.extend F v : Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y) y =
      transSection e (FiberBundle.extend E (x := x) (e.symm v : TangentSpace I x) : Π y : M, TangentSpace I y) y := by
  unfold FiberBundle.extend
  have hb' : y ∈ (trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) x).baseSet := hy
  have hb : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := hy
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hw2 : ((trivializationAt E (TangentSpace I) x) (⟨x, (e.symm v : TangentSpace I x)⟩ : TangentBundle I M)).2 = e.symm v :=
    (trivializationAt_snd (I := I) x x (e.symm v : TangentSpace I x)).trans (tangentCoordChange_self (I := I) hx)
  have hw : ((trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) x)
      (⟨x, v⟩ : TangentBundle (I.transContinuousLinearEquiv e) M)).2 = v :=
    (trivializationAt_snd (I := I.transContinuousLinearEquiv e) x x v).trans
      (tangentCoordChange_self (I := I.transContinuousLinearEquiv e) (by simp [extChartAt]))
  show (trivializationAt F (TangentSpace (I.transContinuousLinearEquiv e)) x).symm y _ =
    e ((trivializationAt E (TangentSpace I) x).symm y ((trivializationAt E (TangentSpace I) x
      (⟨x, (e.symm v : TangentSpace I x)⟩ : TangentBundle I M)).2))
  rw [← Trivialization.symmL_apply (R := ℝ) _ hb', ← Trivialization.symmL_apply (R := ℝ) _ hb,
    TangentBundle.symmL_trivializationAt_eq_core hy, TangentBundle.symmL_trivializationAt_eq_core (I := I) hy, hw, hw2]
  exact tangentCoordChange_transContinuousLinearEquiv (I := I) e x y y v

variable [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold I 2 M]

theorem smoothNear_trans (e : E ≃L[ℝ] F) {X : Π y : M, TangentSpace I y} {x : M} (hX : SmoothNearW X x) :
    SmoothNearW (I := I.transContinuousLinearEquiv e) (transSection e X) x := by
  filter_upwards [hX] with y hy
  exact (contMDiffAt_transSection_iff e (n := ∞) X y).2 hy

/-- **The curvature of the transported connection is the transport of the curvature.** -/
theorem curvatureAt_trans (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov] (x : M)
    (a b c : TangentSpace I x) :
    (transCov e cov).curvatureAt x (e a) (e b) (e c) = e (cov.curvatureAt x a b c) := by
  have := locallySmoothConnectionW_transCov e cov
  set X : Π y : M, TangentSpace I y := FiberBundle.extend E a with hXd
  set Y : Π y : M, TangentSpace I y := FiberBundle.extend E b with hYd
  set Z : Π y : M, TangentSpace I y := FiberBundle.extend E c with hZd
  have hX : SmoothNearW X x := eventually_extendW x _
  have hY : SmoothNearW Y x := eventually_extendW x _
  have hZ : SmoothNearW Z x := eventually_extendW x _
  have hXx : X x = a := FiberBundle.extend_apply_self E _
  have hYx : Y x = b := FiberBundle.extend_apply_self E _
  have hZx : Z x = c := FiberBundle.extend_apply_self E _
  have h1 := curvatureAt_apply_eventuallyW cov X Y Z x hX hY hZ
  have h2 := curvatureAt_apply_eventuallyW (transCov e cov) (transSection e X) (transSection e Y) (transSection e Z) x
    (smoothNear_trans e hX) (smoothNear_trans e hY) (smoothNear_trans e hZ)
  rw [hXx, hYx, hZx] at h1
  have hX' : transSection e X x = e a := congrArg e hXx
  have hY' : transSection e Y x = e b := congrArg e hYx
  have hZ' : transSection e Z x = e c := congrArg e hZx
  rw [hX', hY', hZ'] at h2
  have key : ∀ (Zf Yf : Π y : M, TangentSpace I y),
      (fun y => transCov e cov (transSection e Zf) y (transSection e Yf y)) =
        transSection e (fun y => cov Zf y (Yf y)) := by
    intro Zf Yf
    funext y
    rw [transCov_apply]
    exact congrArg (fun w : E => e (cov Zf y w)) (e.symm_apply_apply (Yf y))
  have hbr : mlieBracket (I.transContinuousLinearEquiv e) (transSection e X) (transSection e Y) x =
      e (mlieBracket I X Y x) := mlieBracket_transSection e (mdiffAt_of_smoothNearW hX) (mdiffAt_of_smoothNearW hY)
  rw [h2, key Z Y, key Z X, hbr, h1]
  have t1 := transCov_apply e cov (fun y => cov Z y (Y y)) x (e a)
  have t2 := transCov_apply e cov (fun y => cov Z y (X y)) x (e b)
  have t3 := transCov_apply e cov Z x (e (mlieBracket I X Y x))
  rw [t1, t2, t3]
  erw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]
  exact ((map_sub e _ _).trans (congrArg (fun z => z - e _) (map_sub e _ _))).symm

end Lightlike
