import Mathlib
import Lightlike.Spacetime.Corners.LeviCivitaTransport

/-!
# The covariant derivative of a field of bilinear forms for a transported model

For `T` a field of bilinear forms on the tangent spaces for `I`, `T' y (v, w) = T y (e⁻¹ v, e⁻¹ w)` is the transported field, and
`covDerivBilinAt_trans`: `(∇' T') (e X, e v, e w) = (∇ T) (X, v, w)`. The extensions of the vectors for the two models agree on the chart domain
(`extend_trans`), and the covariant derivative and the derivative of a function depend on them only through their germs.
-/

open Bundle Manifold Set VectorField Filter
open scoped Manifold ContDiff Topology
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold I 2 M]

theorem extend_trans_eventually (e : E ≃L[ℝ] F) (x : M) (v : TangentSpace I x) :
    (FiberBundle.extend F (x := x) (e v : TangentSpace (I.transContinuousLinearEquiv e) x) :
        Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y) =ᶠ[𝓝 x]
      transSection e (FiberBundle.extend E (x := x) v : Π y : M, TangentSpace I y) := by
  filter_upwards [(chartAt H x).open_source.mem_nhds (mem_chart_source H x)] with y hy
  have h := extend_trans (I := I) e x (e v) y hy
  have hv : (e.symm (e v) : TangentSpace I x) = v := e.symm_apply_apply v
  rw [hv] at h
  exact h

theorem cov_ext_trans (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov] (x : M)
    (v : TangentSpace I x) (X : TangentSpace I x) :
    (transCov e cov (FiberBundle.extend F (x := x) (e v : TangentSpace (I.transContinuousLinearEquiv e) x)) x) (e X) =
      e (cov (FiberBundle.extend E (x := x) v) x X) := by
  have := locallySmoothConnectionW_transCov e cov
  have h1 : SmoothNearW (I := I.transContinuousLinearEquiv e)
      (FiberBundle.extend F (x := x) (e v : TangentSpace (I.transContinuousLinearEquiv e) x)) x :=
    eventually_extendW x _
  have h2 : SmoothNearW (I := I.transContinuousLinearEquiv e)
      (transSection e (FiberBundle.extend E (x := x) v : Π y : M, TangentSpace I y)) x :=
    smoothNear_trans e (eventually_extendW x _)
  have hloc := (transCov e cov).isCovariantDerivativeOn.congr_of_eventuallyEq (s := Set.univ)
    (mdiffAt_of_smoothNear h1) (mdiffAt_of_smoothNear h2) Filter.univ_mem (extend_trans_eventually e x v)
  rw [hloc]
  exact (transCov_apply e cov (FiberBundle.extend E (x := x) v) x (e X)).trans
    (congrArg (fun z : TangentSpace I x => e (cov (FiberBundle.extend E (x := x) v) x z)) (e.symm_apply_apply X))

/-- **The covariant derivative of a transported field of bilinear forms is the transport of the covariant derivative.** -/
theorem covDerivBilinAt_trans (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov]
    (T : Π y : M, TangentSpace I y → TangentSpace I y → ℝ) (x : M) (X v w : TangentSpace I x) :
    (transCov e cov).covDerivBilinAt
      (fun y (v' w' : TangentSpace (I.transContinuousLinearEquiv e) y) => T y (e.symm v') (e.symm w')) x (e X) (e v) (e w) =
      cov.covDerivBilinAt T x X v w := by
  unfold Connection.covDerivBilinAt
  have hv := extend_trans_eventually e x v
  have hw := extend_trans_eventually e x w
  set ev : Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y :=
    FiberBundle.extend F (x := x) (e v : TangentSpace (I.transContinuousLinearEquiv e) x) with hevd
  set ew : Π y : M, TangentSpace (I.transContinuousLinearEquiv e) y :=
    FiberBundle.extend F (x := x) (e w : TangentSpace (I.transContinuousLinearEquiv e) x) with hewd
  have hf : (fun y => T y (untransSection e ev y) (untransSection e ew y)) =ᶠ[𝓝 x]
      (fun y => T y (FiberBundle.extend E (x := x) v y) (FiberBundle.extend E (x := x) w y)) := by
    filter_upwards [hv, hw] with y hy1 hy2
    have h1 : untransSection e ev y = FiberBundle.extend E (x := x) v y := by
      show e.symm (ev y) = _
      rw [hy1]; exact e.symm_apply_apply _
    have h2 : untransSection e ew y = FiberBundle.extend E (x := x) w y := by
      show e.symm (ew y) = _
      rw [hy2]; exact e.symm_apply_apply _
    rw [h1, h2]
  have m : (mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ)
      (fun y => T y (untransSection e ev y) (untransSection e ew y)) x) (e X) =
      (mfderiv I 𝓘(ℝ, ℝ) (fun y => T y (FiberBundle.extend E (x := x) v y) (FiberBundle.extend E (x := x) w y)) x) X := by
    rw [mfderiv_trans_real, hf.mfderiv_eq]
    exact congrArg (mfderiv I 𝓘(ℝ, ℝ) (fun y => T y (FiberBundle.extend E (x := x) v y)
      (FiberBundle.extend E (x := x) w y)) x) (e.symm_apply_apply X)
  have c1 := cov_ext_trans e cov x v X
  have c2 := cov_ext_trans e cov x w X
  show (show ℝ from (mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ)
      (fun y => T y (untransSection e ev y) (untransSection e ew y)) x) (e X)) -
      T x (e.symm ((transCov e cov ev x) (e X))) (e.symm (e w)) -
      T x (e.symm (e v)) (e.symm ((transCov e cov ew x) (e X))) = _
  rw [m, c1, c2]
  erw [e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply, e.symm_apply_apply]

end Lightlike
