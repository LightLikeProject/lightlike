import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Lightlike.Gauge.Connection.PureGauge

/-!
# Gauge covariance of the curvature

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1: under a change of trivialisation (a gauge
transformation `g`) the potential transforms as `A ↦ g A g⁻¹ - dg g⁻¹` (eq. (38), p. 30) and the curvature as
`F ↦ g F g⁻¹` (eqs. (63), p. 42, and (64), p. 43).

All statements are on an open set `U` (the source's trivialisation domain).
* `gaugeTransform g h A`: `y ↦ (ζ ↦ g(y) A(y)(ζ) h(y) - dg(y)(ζ) h(y))`, with `h = g⁻¹` on `U` (eq. (38)).
* `curvature_gaugeTransform`: `F_{A'}(η, ξ) = g F_A(η, ξ) g⁻¹` on `U` (eq. (64)).
* `curvature_transition`: (38) on an overlap `U ∩ V` gives `F_V = g_{VU} F_U g_{VU}⁻¹` there (eq. (63)).
-/

open ContinuousLinearMap Set
open scoped Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- **The gauge transform** of `A` by `g` (with `h = g⁻¹`): `A'(y)(ζ) = g(y) A(y)(ζ) h(y) - dg(y)(ζ) h(y)`
(Svetlichny eq. (38)). -/
def gaugeTransform (g h : E → 𝔄) (A : E → E →L[ℝ] 𝔄) (y : E) : E →L[ℝ] 𝔄 :=
  ((ContinuousLinearMap.mul ℝ 𝔄 (g y)).comp ((ContinuousLinearMap.mul ℝ 𝔄).flip (h y))).comp (A y) -
    ((ContinuousLinearMap.mul ℝ 𝔄).flip (h y)).comp (fderiv ℝ g y)

lemma gaugeTransform_apply (g h : E → 𝔄) (A : E → E →L[ℝ] 𝔄) (y ζ : E) :
    gaugeTransform g h A y ζ = g y * A y ζ * h y - fderiv ℝ g y ζ * h y := by
  simp [gaugeTransform, mul_assoc]

/-- The directional derivative of a `CLM`-valued map applied to a fixed vector. -/
lemma fderiv_apply_const {B : E → E →L[ℝ] 𝔄} {x : E} (hB : DifferentiableAt ℝ B x) (η ζ : E) :
    fderiv ℝ B x η ζ = fderiv ℝ (fun y => B y ζ) x η := by
  rw [fderiv_clm_apply hB (differentiableAt_const ζ)]
  simp

/-- **The derivative of the inverse**, on an open set: if `h g = g h = 1` on an open `U ∋ x`, then
`dh(x)(ζ) = -h(x) dg(x)(ζ) h(x)`. -/
lemma fderiv_inv_apply_of_mem {g h : E → 𝔄} {U : Set E} {x : E} (hUx : U ∈ 𝓝 x) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (hhg : ∀ y ∈ U, h y * g y = 1) (hgh : g x * h x = 1) (ζ : E) :
    fderiv ℝ h x ζ = -(h x * fderiv ℝ g x ζ * h x) := by
  have h1 : fderiv ℝ (fun z => h z * g z) x ζ = 0 := by
    have he : (fun z => h z * g z) =ᶠ[𝓝 x] fun _ => (1 : 𝔄) := Filter.eventually_of_mem hUx hhg
    rw [he.fderiv_eq]; simp
  rw [fderiv_fun_mul' hh hg] at h1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    op_smul_eq_mul] at h1
  calc fderiv ℝ h x ζ = fderiv ℝ h x ζ * (g x * h x) := by rw [hgh, mul_one]
    _ = (fderiv ℝ h x ζ * g x) * h x := by rw [mul_assoc]
    _ = -(h x * fderiv ℝ g x ζ) * h x := by rw [eq_neg_of_add_eq_zero_right h1]
    _ = _ := by rw [neg_mul]

/-- **Gauge covariance of the curvature** on an open set `U` (Svetlichny eqs. (63), (64)): if `g` is `C²` and `A`,
`h = g⁻¹` are differentiable on `U`, then `F_{A'}(η, ξ) = g F_A(η, ξ) g⁻¹` at every `x ∈ U`. -/
theorem curvature_gaugeTransform {g h : E → 𝔄} {A : E → E →L[ℝ] 𝔄} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ 2 g U) (hh : DifferentiableOn ℝ h U) (hA : DifferentiableOn ℝ A U)
    (hhg : ∀ y ∈ U, h y * g y = 1) (hgh : ∀ y ∈ U, g y * h y = 1) {x : E} (hx : x ∈ U) (η ξ : E) :
    curvature (gaugeTransform g h A) x η ξ = g x * curvature A x η ξ * h x := by
  have hUx : U ∈ 𝓝 x := hU.mem_nhds hx
  have hgx : ContDiffAt ℝ 2 g x := hg.contDiffAt hUx
  have hg1 : DifferentiableAt ℝ g x := hgx.differentiableAt (by norm_num)
  have hdg : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hgx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hhx : DifferentiableAt ℝ h x := hh.differentiableAt hUx
  have hAx : DifferentiableAt ℝ A x := hA.differentiableAt hUx
  have hA' : DifferentiableAt ℝ (gaugeTransform g h A) x := by
    unfold gaugeTransform
    exact ((((ContinuousLinearMap.mul ℝ 𝔄).differentiableAt.comp x hg1).clm_comp
      ((ContinuousLinearMap.mul ℝ 𝔄).flip.differentiableAt.comp x hhx)).clm_comp hAx).sub
      (((ContinuousLinearMap.mul ℝ 𝔄).flip.differentiableAt.comp x hhx).clm_comp hdg)
  -- the directional derivative of `y ↦ A'(y)(ζ)`
  have hD : ∀ θ ζ : E, fderiv ℝ (gaugeTransform g h A) x θ ζ =
      fderiv ℝ g x θ * A x ζ * h x + g x * fderiv ℝ A x θ ζ * h x + g x * A x ζ * fderiv ℝ h x θ -
        (fderiv ℝ (fderiv ℝ g) x θ ζ * h x + fderiv ℝ g x ζ * fderiv ℝ h x θ) := by
    intro θ ζ
    rw [fderiv_apply_const hA']
    have e : (fun y => gaugeTransform g h A y ζ) = fun y => g y * A y ζ * h y - fderiv ℝ g y ζ * h y :=
      funext fun y => gaugeTransform_apply g h A y ζ
    have hAζ : DifferentiableAt ℝ (fun y => A y ζ) x := hAx.clm_apply (differentiableAt_const ζ)
    have hdgζ : DifferentiableAt ℝ (fun y => fderiv ℝ g y ζ) x := hdg.clm_apply (differentiableAt_const ζ)
    rw [e, fderiv_fun_sub ((hg1.fun_mul hAζ).fun_mul hhx) (hdgζ.fun_mul hhx),
      fderiv_fun_mul' (hg1.fun_mul hAζ) hhx, fderiv_fun_mul' hg1 hAζ, fderiv_fun_mul' hdgζ hhx]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, op_smul_eq_mul]
    rw [← fderiv_apply_const hAx, ← fderiv_apply_const hdg]
    noncomm_ring
  have hdh : ∀ ζ : E, fderiv ℝ h x ζ = -(h x * fderiv ℝ g x ζ * h x) :=
    fun ζ => fderiv_inv_apply_of_mem hUx hg1 hhx hhg (hgh x hx) ζ
  have hsym := ContDiffAt.isSymmSndFDerivAt hgx (by simp)
  unfold curvature
  rw [hD η ξ, hD ξ η, gaugeTransform_apply, gaugeTransform_apply, hdh η, hdh ξ, hsym η ξ]
  have hz : h x * g x - 1 = 0 := by rw [hhg x hx, sub_self]
  rw [← sub_eq_zero]
  -- `LHS - RHS` is a combination of `h g - 1` (computed by hand), which vanishes
  calc _ = g x * A x η * (h x * g x - 1) * A x ξ * h x - g x * A x ξ * (h x * g x - 1) * A x η * h x -
        fderiv ℝ g x η * (h x * g x - 1) * A x ξ * h x + fderiv ℝ g x ξ * (h x * g x - 1) * A x η * h x := by
        noncomm_ring
    _ = 0 := by rw [hz]; simp

/-- **The transition formula on an overlap** (Svetlichny eq. (38) on `U ∩ V` implies eq. (63)): if
`A_V = g A_U g⁻¹ - dg g⁻¹` on `U ∩ V` (with `g = g_{VU}` `C²` and `h = g⁻¹` differentiable there, and `A_U`
differentiable on `U`), then `F_V = g F_U g⁻¹` at every point of `U ∩ V`. -/
theorem curvature_transition {AU AV : E → E →L[ℝ] 𝔄} {g h : E → 𝔄} {U V : Set E} (hU : IsOpen U)
    (hV : IsOpen V) (hAU : DifferentiableOn ℝ AU U) (hg : ContDiffOn ℝ 2 g (U ∩ V))
    (hh : DifferentiableOn ℝ h (U ∩ V)) (hhg : ∀ y ∈ U ∩ V, h y * g y = 1) (hgh : ∀ y ∈ U ∩ V, g y * h y = 1)
    (h38 : ∀ y ∈ U ∩ V, AV y = gaugeTransform g h AU y) {x : E} (hx : x ∈ U ∩ V) (η ξ : E) :
    curvature AV x η ξ = g x * curvature AU x η ξ * h x := by
  rw [curvature_congr (Filter.eventually_of_mem ((hU.inter hV).mem_nhds hx) h38)]
  exact curvature_gaugeTransform (hU.inter hV) hg hh (hAU.mono inter_subset_left) hhg hgh hx η ξ

end Lightlike.Gauge
