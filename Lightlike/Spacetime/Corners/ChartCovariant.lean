import Lightlike.Spacetime.ChartConnection
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.ChartCovariant

/-!
# A connection in the trivialization of a chart

For a manifold `M` modelled on a finite-dimensional space `E` and a point `x₀`:

* `contMDiffAt_covW`: a smooth connection applied to a vector field smooth near `x` is smooth at `x`
  (Hausdorff `M`; the proof uses a smooth bump function);
* `hatW`: the components `M → E` of a vector field in the tangent trivialization at `x₀`;
* `cov0W`: the connection `∇⁰_u σ = e⁻¹ (D σ̂ (u))` of that trivialization, a covariant derivative on the
  chart domain (`cov0_isCovW`). The difference of a connection with `cov0W` is a tensor (Mathlib's
  `IsCovariantDerivativeOn.difference`), the Christoffel symbols of the connection in the chart; the curvature
  is computed from it in `ChartCurvature.lean` (when present).

**Limits.** Boundaryless manifolds modelled on `E`; the smoothness statement needs `T2Space M`.

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartCovariant.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **A locally smooth connection**: `cov σ` is smooth at `x` whenever `σ` is smooth near `x`. This is the local form of Mathlib's
`ContMDiffCovariantDerivative cov ∞` (stated for sections smooth on the whole manifold); the two agree on a Hausdorff manifold
(`contMDiffAt_cov_of_global`), but only the local form is used below, so that no Hausdorff hypothesis is needed. -/
class LocallySmoothConnectionW (cov : Connection I M) : Prop where
  contMDiffAt : ∀ {σ : Π y : M, TangentSpace I y} {x : M},
    (∀ᶠ y in 𝓝 x, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle I M)) y) →
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x


/-- **Local smoothness of a locally smooth connection.** -/
theorem contMDiffAt_covW (cov : Connection I M) [LocallySmoothConnectionW cov]
    {σ : Π y : M, TangentSpace I y} {x : M}
    (hσ : ∀ᶠ y in 𝓝 x, ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle I M)) y) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y))) x :=
  LocallySmoothConnectionW.contMDiffAt hσ

/-- The tangent trivialization at `x₀`. -/
abbrev tTrivW (x₀ : M) : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M) :=
  trivializationAt E (TangentSpace I : M → Type _) x₀

/-- A vector field in the trivialization at `x₀`: a function `M → E`. -/
def hatW (x₀ : M) (σ : Π y : M, TangentSpace I y) : M → E :=
  fun z => (tTrivW (I := I) (E := E) x₀ (⟨z, σ z⟩ : TotalSpace E (TangentSpace I : M → Type _))).2

/-- A vector field is differentiable at `z` in the chart domain iff its components in the trivialization are. -/
theorem mdiffAt_hat_iffW (x₀ : M) (σ : Π y : M, TangentSpace I y) {z : M}
    (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q : M => (⟨q, σ q⟩ : TangentBundle I M)) z ↔
    MDifferentiableAt I 𝓘(ℝ, E) (hatW x₀ σ) z := by
  exact (tTrivW (I := I) (E := E) x₀).mdifferentiableAt_section_iff I σ hz

variable (x₀ : M)

/-- The components in the trivialization are additive on the chart domain. -/
theorem hat_addW {σ σ' : Π y : M, TangentSpace I y} {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    hatW x₀ (σ + σ') z = hatW x₀ σ z + hatW x₀ σ' z :=
  ((tTrivW (I := I) (E := E) x₀).linear ℝ hz).map_add _ _

/-- The components in the trivialization are homogeneous on the chart domain. -/
theorem hat_smulW {σ : Π y : M, TangentSpace I y} (f : M → ℝ) {z : M}
    (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    hatW x₀ (f • σ) z = f z • hatW x₀ σ z :=
  ((tTrivW (I := I) (E := E) x₀).linear ℝ hz).map_smul _ _

/-- The covariant derivative of the trivialization at `x₀`: `∇⁰_u σ = e⁻¹ (D σ̂ (u))`. -/
def cov0W (σ : Π y : M, TangentSpace I y) (z : M) :
    TangentSpace I z →L[ℝ] TangentSpace I z :=
  ((tTrivW (I := I) (E := E) x₀).symmL ℝ z).comp (mvfderiv I (hatW x₀ σ) z)

/-- Reading a field in the trivialization and returning gives back the field. -/
theorem symmL_hatW {σ : Π y : M, TangentSpace I y} {z : M} (hz : z ∈ (tTrivW (I := I) (E := E) x₀).baseSet) :
    (tTrivW (I := I) (E := E) x₀).symmL ℝ z (hatW x₀ σ z) = σ z := by
  rw [Trivialization.symmL_apply _ hz]
  exact (tTrivW (I := I) (E := E) x₀).symm_apply_apply_mk hz (σ z)

/-- `mvfderiv` only depends on the germ. -/
theorem mvfderiv_congrW {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv I f₁ x = mvfderiv I f₂ x := by
  unfold mvfderiv
  rw [h.mfderiv_eq]
  ext v
  simp [tangentSpaceCast, fromTangentSpace]
  rfl

/-- The connection `cov0W` of the trivialization is a covariant derivative on the chart domain. -/
theorem cov0_isCovW : IsCovariantDerivativeOn E (cov0W (I := I) (E := E) (M := M) x₀) (tTrivW (I := I) (E := E) x₀).baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    have h1 := (mdiffAt_hat_iffW x₀ σ hx).1 hσ
    have h2 := (mdiffAt_hat_iffW x₀ σ' hx).1 hσ'
    have heq : hatW x₀ (σ + σ') =ᶠ[𝓝 x] hatW x₀ σ + hatW x₀ σ' := by
      filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hx] with z hz
      exact hat_addW x₀ hz
    unfold cov0W
    rw [mvfderiv_congrW heq, mvfderiv_add h1 h2, ContinuousLinearMap.comp_add]
  leibniz {σ g} {x} hσ hg hx := by
    have h1 := (mdiffAt_hat_iffW x₀ σ hx).1 hσ
    have heq : hatW x₀ (g • σ) =ᶠ[𝓝 x] g • hatW x₀ σ := by
      filter_upwards [(tTrivW (I := I) (E := E) x₀).open_baseSet.mem_nhds hx] with z hz
      exact hat_smulW x₀ g hz
    unfold cov0W
    rw [mvfderiv_congrW heq, mvfderiv_smul hg h1]
    ext u
    simp [symmL_hatW x₀ hx]
end Lightlike
