import Lightlike.Spacetime.ModelTransport
import Lightlike.Spacetime.FLRWSphere
import Lightlike.Spacetime.StereoConformal
import Lightlike.Spacetime.Corners.Curvature

/-!
# The FLRW metric on `J × S³` for the model `Fin 4 → ℝ` (CO30, attempt 1)

`I4` is the model of `↥J × S³` transported to `Fin 4 → ℝ` (time first) with `ModelWithCorners.transContinuousLinearEquiv`, so that the coordinate
layer of the library (`NondegMetric.coordMetricW`, the Einstein equations in charts) applies. `flrwMetric4` is the FLRW metric of `FLRWSphere.lean` as a
Lorentzian metric for this model: the pullback of `-dT² + |dv|² - dc²` by the embedding `(t, x) ↦ (t, a(t) x, a(t))`, evaluated on `modelEquiv⁻¹`
(`flrwForm4_eq`).

**Limits.** The metric only; its coordinate expression in the charts and the Einstein equations are later steps.
-/

open Manifold Metric Bundle TopologicalSpace
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

/-- the identification of the model `ℝ × ℝ³` with `Fin 4 → ℝ` (time first) -/
def modelEquiv : (ℝ × EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (Fin 4 → ℝ) :=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin 3) ℝ)).trans
    (Fin.consEquivL ℝ (fun _ : Fin 4 => ℝ))

/-- the model with corners of `J × S³` on `Fin 4 → ℝ` -/
abbrev I4 : ModelWithCorners ℝ (Fin 4 → ℝ) (ModelProd ℝ (EuclideanSpace ℝ (Fin 3))) :=
  IJS.transContinuousLinearEquiv modelEquiv

example (J : Opens ℝ) : IsManifold I4 ∞ (↥J × S3) := inferInstance
theorem modelEquiv_apply (s : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    modelEquiv (s, u) = Fin.cons s (fun i => u i) := by
  rfl

/-- The FLRW form on `J × S³`, as a form on the tangent spaces of the model `Fin 4 → ℝ`. -/
def flrwForm4 {J : Opens ℝ} (a : ℝ → ℝ) (p : ↥J × S3) :
    TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ :=
  pullbackForm (I := I4) Lmink (flrwEmb (J := J) a) p

/-- The derivative of the embedding with respect to the transported model. -/
theorem dι_I4 {J : Opens ℝ} {a : ℝ → ℝ} (p : ↥J × S3) (ha : DifferentiableAt ℝ a (p.1 : ℝ)) (v : TangentSpace I4 p) :
    dι (I := I4) (flrwEmb (J := J) a) p v = dι (I := IJS) (flrwEmb (J := J) a) p (modelEquiv.symm v) := by
  have h := hasMFDerivAt_transContinuousLinearEquiv modelEquiv (hasMFDerivAt_flrwEmb p ha)
  unfold dι
  rw [h.mfderiv, (hasMFDerivAt_flrwEmb p ha).mfderiv]
  rfl

/-- **The FLRW form in the model `Fin 4 → ℝ`** is the form on `ℝ × ℝ³` evaluated on the preimages. -/
theorem flrwForm4_eq {J : Opens ℝ} {a : ℝ → ℝ} (p : ↥J × S3) (ha : DifferentiableAt ℝ a (p.1 : ℝ)) (v w : TangentSpace I4 p) :
    flrwForm4 a p v w = flrwForm a p (modelEquiv.symm v) (modelEquiv.symm w) := by
  unfold flrwForm4 flrwForm
  rw [pullbackForm_apply (I := I4), dι_I4 p ha, dι_I4 p ha]
  exact (pullbackForm_apply (I := IJS) Lmink (flrwEmb (J := J) a) p (modelEquiv.symm v) (modelEquiv.symm w)).symm


/-- **The FLRW metric on `J × S³` as a Lorentzian metric of the manifold modelled on `Fin 4 → ℝ`.** -/
def flrwMetric4 (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) :
    LorentzianMetric I4 (↥J × S3) 4 where
  g := flrwForm4 a
  contMDiff := contMDiff_pullbackForm Lmink
    ((ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left (e := modelEquiv)).2 (contMDiff_flrwEmb ha))
  lorentzian p := by
    have hd : DifferentiableAt ℝ a (p.1 : ℝ) :=
      ((ha.contDiffAt (J.isOpen.mem_nhds p.1.2)).differentiableAt (by simp))
    obtain ⟨Bs, hBs⟩ := (flrwLorentzMetric J ha hpos).lorentzian p
    refine ⟨Bs.map (show TangentSpace IJS p ≃ₗ[ℝ] TangentSpace I4 p from modelEquiv.toLinearEquiv), fun i j => ?_⟩
    rw [Module.Basis.map_apply, Module.Basis.map_apply]
    rw [flrwForm4_eq p hd]
    have h1 := hBs i j
    change flrwForm a p (Bs i) (Bs j) = _ at h1
    change flrwForm a p (modelEquiv.symm (modelEquiv (Bs i))) (modelEquiv.symm (modelEquiv (Bs j))) = _
    erw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact h1

end Lightlike
