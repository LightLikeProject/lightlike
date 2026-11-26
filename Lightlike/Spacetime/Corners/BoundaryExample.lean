import Mathlib
import Lightlike.Spacetime.PullbackForm
import Lightlike.Spacetime.Lorentzian
import Lightlike.Spacetime.ModelTransport
import Lightlike.Spacetime.Corners.CurvatureSymmetries
import Lightlike.Spacetime.Corners.BianchiSecond
import Lightlike.Spacetime.Corners.LeviCivitaSmooth
import Lightlike.Spacetime.Corners.DivergenceFree

/-!
# A manifold with boundary: the segment `[0, 1]`

The closed segment `[0, 1]` is a manifold with boundary (Mathlib's model `𝓡∂ 1`); its model is transported to
`Fin 1 → ℝ` by `modelEquiv1` (`IB`), the model of the Corners layer of the curvature (`Spacetime/Corners/`). `segMetric`
is the metric `dx²` of the segment, the pullback of the product of reals by the inclusion into `ℝ`, a `NondegMetric` of
the manifold `Icc 0 1` with boundary points `0` and `1`. For its Levi-Civita connection the identities of the Corners
layer hold (`segment_identities`): the first and second Bianchi identities, the pair symmetry and the symmetry of the
Ricci tensor and the divergence of the Einstein tensor, on a manifold with boundary.

**Limits.** The dimension is one, so the curvature of the segment vanishes and the identities are, in this example, the
statement that the hypotheses of the theorems (a locally smooth Levi-Civita connection on a manifold modelled with
boundary on `Fin 1 → ℝ`) are satisfiable and the theorems apply at points of the boundary; it is not a test of nonzero
curvature at the boundary.
-/

open Manifold Bundle Set
open scoped ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace Lightlike

instance : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩

/-- The closed segment `[0, 1]`. -/
abbrev Seg : Type := Icc (0 : ℝ) 1

/-- the identification of the model `ℝ¹` (Euclidean) with `Fin 1 → ℝ` -/
def modelEquiv1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ

/-- the model with corners of the segment on `Fin 1 → ℝ` -/
abbrev IB : ModelWithCorners ℝ (Fin 1 → ℝ) (EuclideanHalfSpace 1) :=
  (𝓡∂ 1).transContinuousLinearEquiv modelEquiv1

example : IsManifold IB ∞ Seg := inferInstance

/-- The derivative of the inclusion `[0, 1] → ℝ` as a plain continuous linear map. -/
def dcoeSeg (z : Seg) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
  mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Seg → ℝ) z

theorem hasMFDerivAt_valSeg (z : Seg) :
    HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Seg → ℝ) z (dcoeSeg z) :=
  ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)).hasMFDerivAt

/-- The derivative of the inclusion with respect to the transported model. -/
theorem dι_IB (z : Seg) (v : TangentSpace IB z) :
    dι (I := IB) (Subtype.val : Seg → ℝ) z v = dcoeSeg z (modelEquiv1.symm v) := by
  have h := hasMFDerivAt_transContinuousLinearEquiv modelEquiv1 (hasMFDerivAt_valSeg z)
  unfold dι
  rw [h.mfderiv]
  rfl

theorem dcoeSeg_injective (z : Seg) : Function.Injective (dcoeSeg z) :=
  isImmersionOfComplement_subtypeVal_Icc.mfderiv_injective (n := ∞) (by simp) z

/-- **The metric `dx²` of the segment `[0, 1]`**, as a metric of the manifold with boundary modelled on `Fin 1 → ℝ`. -/
def segMetric : NondegMetric IB Seg where
  g := pullbackForm (I := IB) (ContinuousLinearMap.mul ℝ ℝ) (Subtype.val : Seg → ℝ)
  symm x v w := pullbackForm_symm (fun a b => mul_comm a b) _ x v w
  nondegenerate x v h := by
    have h0 := h v
    rw [pullbackForm_apply, dι_IB] at h0
    have h1 : dcoeSeg x (modelEquiv1.symm v) = 0 := by
      have : dcoeSeg x (modelEquiv1.symm v) * dcoeSeg x (modelEquiv1.symm v) = 0 := h0
      exact mul_self_eq_zero.1 this
    have h2 : modelEquiv1.symm v = 0 := dcoeSeg_injective x (h1.trans (map_zero _).symm)
    exact modelEquiv1.symm.injective (h2.trans (map_zero _).symm)
  contMDiff := contMDiff_pullbackForm _
    ((ContinuousLinearEquiv.contMDiff_transContinuousLinearEquiv_left (e := modelEquiv1)).2
      (contMDiff_subtypeVal_Icc (n := ∞)))

section Identities

variable (cov : Connection IB Seg) [LocallySmoothConnectionW cov]

/-- **The identities of the Corners layer on a manifold with boundary**: for a locally smooth Levi-Civita connection of
`segMetric` on the segment `[0, 1]` (points of the boundary included), the first and second Bianchi identities, the
pair symmetry of the curvature, the symmetry of the Ricci tensor and the vanishing divergence of the Einstein tensor. -/
theorem segment_identities (h : cov.IsLeviCivita segMetric) (x : Seg) :
    (∀ X Y Z : TangentSpace IB x,
      cov.curvatureAt x X Y Z + cov.curvatureAt x Y Z X + cov.curvatureAt x Z X Y = 0) ∧
    (∀ X Y Z W : TangentSpace IB x,
      cov.riemannLowerAt segMetric x X Y Z W = cov.riemannLowerAt segMetric x Z W X Y) ∧
    (∀ Y Z : TangentSpace IB x, cov.ricciAt x Y Z = cov.ricciAt x Z Y) ∧
    (∀ X Y Z W : TangentSpace IB x,
      cov.covDerivCurvatureAt x X Y Z W + cov.covDerivCurvatureAt x Y Z X W +
        cov.covDerivCurvatureAt x Z X Y W = 0) ∧
    (∀ w : TangentSpace IB x, cov.divBilinAt segMetric (cov.einsteinField segMetric) x w = 0) :=
  ⟨fun X Y Z => bianchi_first_provedW cov h.1 x X Y Z,
    fun X Y Z W => riemannLowerAt_pair_symmW cov segMetric h.1 h.2 x X Y Z W,
    fun Y Z => ricciAt_symm_provedW cov segMetric h.1 h.2 x Y Z,
    fun X Y Z W => bianchi_second_provedW cov h.1 x X Y Z W,
    fun w => einstein_divergence_free_provedW segMetric cov x h w⟩

end Identities

/-- **Non-vacuity**: the Levi-Civita connection of `segMetric` is locally smooth and Levi-Civita, so the identities
apply to it, at every point of the segment including the boundary point `0`. -/
theorem segment_exists_leviCivita :
    ∃ cov : Connection IB Seg, LocallySmoothConnectionW cov ∧ cov.IsLeviCivita segMetric :=
  ⟨leviCivita segMetric, inferInstance, ⟨leviCivita_torsion _, leviCivita_compat _⟩⟩

end Lightlike
