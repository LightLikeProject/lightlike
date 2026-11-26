import Mathlib
import Lightlike.Spacetime.Corners.CurvatureTransport

/-!
# The Levi-Civita conditions for a transported model

For `e : E ≃L[ℝ] F`, `I' = I.transContinuousLinearEquiv e`, `cov' = transCov e cov` and `g' = transMetric e g`: the torsion of `cov'` is the
transport of the torsion of `cov` (`torsion_trans`), `cov'` is compatible with `g'` when `cov` is with `g`
(`isMetricCompatible_trans`), hence `cov'` is the Levi-Civita connection of `g'` when `cov` is the one of `g`
(`isLeviCivita_trans`).
-/

open Bundle Manifold Set VectorField
open scoped Manifold ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E] [CompleteSpace F]

/-- The derivative of a real function for the transported model, with no differentiability hypothesis. -/
theorem mfderiv_trans_real (e : E ≃L[ℝ] F) (g : M → ℝ) (x : M) :
    mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) g x =
      (mfderiv I 𝓘(ℝ, ℝ) g x).comp (e.symm : F →L[ℝ] E) := by
  by_cases hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x
  · exact mfderiv_transContinuousLinearEquiv_real e hg
  · have hg' : ¬ MDifferentiableAt (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ) g x :=
      fun h => hg ((mdifferentiableAt_transContinuousLinearEquiv_iff e).1 h)
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, mfderiv_zero_of_not_mdifferentiableAt hg']
    ext; rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold I 2 M]

/-- **The torsion of the transported connection is the transport of the torsion.** -/
theorem torsion_trans (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov] (x : M)
    (a b : TangentSpace I x) :
    (transCov e cov).torsion x (e a) (e b) = e (cov.torsion x a b) := by
  have := locallySmoothConnectionW_transCov e cov
  set X : Π y : M, TangentSpace I y := FiberBundle.extend E a with hXd
  set Y : Π y : M, TangentSpace I y := FiberBundle.extend E b with hYd
  have hX : SmoothNearW X x := eventually_extendW x _
  have hY : SmoothNearW Y x := eventually_extendW x _
  have hXx : X x = a := FiberBundle.extend_apply_self E _
  have hYx : Y x = b := FiberBundle.extend_apply_self E _
  have hXd' : MDifferentiableAt I I.tangent (fun y => (⟨y, X y⟩ : TangentBundle I M)) x := mdiffAt_of_smoothNearW hX
  have hYd' : MDifferentiableAt I I.tangent (fun y => (⟨y, Y y⟩ : TangentBundle I M)) x := mdiffAt_of_smoothNearW hY
  have t1 := cov.torsion_apply hXd' hYd'
  have t2 := (transCov e cov).torsion_apply
    ((mdifferentiableAt_transSection_iff e X x).2 hXd') ((mdifferentiableAt_transSection_iff e Y x).2 hYd')
  rw [hXx, hYx] at t1
  have hX' : transSection e X x = e a := congrArg e hXx
  have hY' : transSection e Y x = e b := congrArg e hYx
  rw [hX', hY'] at t2
  have hbr : mlieBracket (I.transContinuousLinearEquiv e) (transSection e X) (transSection e Y) x =
      e (mlieBracket I X Y x) := mlieBracket_transSection e (mdiffAt_of_smoothNearW hX) (mdiffAt_of_smoothNearW hY)
  rw [t2, t1, hbr]
  have c1 := transCov_apply e cov Y x (e a)
  have c2 := transCov_apply e cov X x (e b)
  rw [c1, c2]
  erw [e.symm_apply_apply, e.symm_apply_apply]
  exact ((map_sub e _ _).trans (congrArg (fun z => z - e _) (map_sub e _ _))).symm

theorem torsion_trans_eq_zero (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov]
    (h : cov.torsion = 0) : (transCov e cov).torsion = 0 := by
  funext x
  ext v w
  have t := torsion_trans e cov x (e.symm v) (e.symm w)
  erw [e.apply_symm_apply, e.apply_symm_apply] at t
  have h0 : cov.torsion x (e.symm v) (e.symm w) = 0 := by rw [h]; rfl
  show (transCov e cov).torsion x v w = 0
  rw [t, h0]
  exact map_zero e

/-- **Metric compatibility is preserved by the transport.** -/
theorem isMetricCompatible_trans (e : E ≃L[ℝ] F) (cov : Connection I M) (g : NondegMetric I M)
    (hC : cov.IsMetricCompatible g) : (transCov e cov).IsMetricCompatible (transMetric e g) := by
  intro X σ τ x hX hσ hτ
  have hX0 : MDifferentiableAt I I.tangent
      (fun y => (⟨y, (untransSection e X : Π y : M, TangentSpace I y) y⟩ : TangentBundle I M)) x :=
    (mdifferentiableAt_transSection_iff e (untransSection e X) x).1 (by rwa [transSection_untransSection])
  have hσ0 : MDifferentiableAt I I.tangent
      (fun y => (⟨y, (untransSection e σ : Π y : M, TangentSpace I y) y⟩ : TangentBundle I M)) x :=
    (mdifferentiableAt_transSection_iff e (untransSection e σ) x).1 (by rwa [transSection_untransSection])
  have hτ0 : MDifferentiableAt I I.tangent
      (fun y => (⟨y, (untransSection e τ : Π y : M, TangentSpace I y) y⟩ : TangentBundle I M)) x :=
    (mdifferentiableAt_transSection_iff e (untransSection e τ) x).1 (by rwa [transSection_untransSection])
  have h := hC (untransSection e X) (untransSection e σ) (untransSection e τ) x hX0 hσ0 hτ0
  change (mfderiv (I.transContinuousLinearEquiv e) 𝓘(ℝ, ℝ)
      (fun y => g.g y (e.symm (σ y)) (e.symm (τ y))) x) (X x) = _
  rw [mfderiv_trans_real]
  refine h.trans ?_
  show _ = (g.g x (e.symm (e (cov (untransSection e σ) x (e.symm (X x)))))) (e.symm (τ x)) +
    (g.g x (e.symm (σ x))) (e.symm (e (cov (untransSection e τ) x (e.symm (X x)))))
  erw [e.symm_apply_apply, e.symm_apply_apply]
  rfl

/-- **The transported connection is the Levi-Civita connection of the transported metric.** -/
theorem isLeviCivita_trans (e : E ≃L[ℝ] F) (cov : Connection I M) [LocallySmoothConnectionW cov]
    (g : NondegMetric I M) (h : cov.IsLeviCivita g) :
    (transCov e cov).IsLeviCivita (transMetric e g) :=
  ⟨torsion_trans_eq_zero e cov h.1, isMetricCompatible_trans e cov g h.2⟩

end Lightlike
