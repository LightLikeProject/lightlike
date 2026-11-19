import Lightlike.Spacetime.ChartConnection

/-!
# A connection in the trivialization of a chart

For a manifold `M` modelled on a finite-dimensional space `E` and a point `x₀`:

* `contMDiffAt_cov`: a smooth connection applied to a vector field smooth near `x` is smooth at `x`
  (Hausdorff `M`; the proof uses a smooth bump function);
* `hat`: the components `M → E` of a vector field in the tangent trivialization at `x₀`;
* `cov0`: the connection `∇⁰_u σ = e⁻¹ (D σ̂ (u))` of that trivialization, a covariant derivative on the
  chart domain (`cov0_isCov`). The difference of a connection with `cov0` is a tensor (Mathlib's
  `IsCovariantDerivativeOn.difference`), the Christoffel symbols of the connection in the chart; the curvature
  is computed from it in `ChartCurvature.lean` (when present).

**Limits.** Boundaryless manifolds modelled on `E`; the smoothness statement needs `T2Space M`.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **A locally smooth connection**: `cov σ` is smooth at `x` whenever `σ` is smooth near `x`. This is the local form of Mathlib's
`ContMDiffCovariantDerivative cov ∞` (stated for sections smooth on the whole manifold); the two agree on a Hausdorff manifold
(`contMDiffAt_cov_of_global`), but only the local form is used below, so that no Hausdorff hypothesis is needed. -/
class LocallySmoothConnection (cov : Connection 𝓘(ℝ, E) M) : Prop where
  contMDiffAt : ∀ {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M},
    (∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) →
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y))) x

section
variable [T2Space M]

/-- **Local smoothness of a smooth connection.** If the vector field `σ` is smooth near `x`, a connection that is smooth (in Mathlib's sense, for sections smooth on the whole manifold) has `y ↦ cov σ y` smooth at `x`. The proof cuts `σ` off with a smooth bump function, which needs the manifold to be Hausdorff. -/
theorem contMDiffAt_cov_of_global (cov : Connection 𝓘(ℝ, E) M)
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hσ : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y))) x := by
  have hs : {y | ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) y} ∈ 𝓝 x := hσ
  obtain ⟨f, hf⟩ := (SmoothBumpFunction.nhds_basis_support (I := 𝓘(ℝ, E)) (c := x) hs).ex_mem
  set σ' : Π y : M, TangentSpace 𝓘(ℝ, E) y := fun y => f y • σ y with hσ'
  have hsm : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ' q⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    intro y
    by_cases hy : y ∈ tsupport f
    · exact (f.contMDiffAt (x := y)).smul_section (hf hy)
    · have h0 : (fun q : M => (⟨q, σ' q⟩ : TangentBundle 𝓘(ℝ, E) M)) =ᶠ[𝓝 y]
          (fun q : M => (⟨q, 0⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
        filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with q hq
        simp [σ', image_eq_zero_of_notMem_tsupport hq]
      exact (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, E)) y).congr_of_eventuallyEq h0
  have hcov := (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative cov ∞).contMDiff
  have h1 := hcov.contMDiff (σ := σ') (by simpa using hsm.contMDiffOn)
  have hnear : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) y ∧ f =ᶠ[𝓝 y] 1 := by
    filter_upwards [hσ, f.eventuallyEq_one.eventuallyEq_nhds] with y hy hy1
    exact ⟨hy, hy1⟩
  have heq : (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y))) =ᶠ[𝓝 x]
      (fun y => ⟨y, cov σ' y⟩) := by
    filter_upwards [hnear] with y ⟨hy, hy1⟩
    have hmσ : MDiffAt (T% σ) y := hy.mdifferentiableAt (by simp)
    have hmσ' : MDiffAt (T% σ') y := (hsm y).mdifferentiableAt (by simp)
    have := (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hmσ hmσ'
      Filter.univ_mem (by filter_upwards [hy1] with q hq; simp [σ', hq])
    simp [this]
  exact ((h1 x (mem_univ x)).contMDiffAt Filter.univ_mem).congr_of_eventuallyEq heq

/-- On a Hausdorff manifold a smooth connection in Mathlib's sense is locally smooth. -/
instance (cov : Connection 𝓘(ℝ, E) M) [CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    LocallySmoothConnection cov :=
  ⟨fun hσ => contMDiffAt_cov_of_global cov hσ⟩

end

/-- **Local smoothness of a locally smooth connection.** -/
theorem contMDiffAt_cov (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov]
    {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} {x : M}
    (hσ : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) y) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y => (⟨y, cov σ y⟩ : TotalSpace (E →L[ℝ] E) (fun y : M => TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y))) x :=
  LocallySmoothConnection.contMDiffAt hσ

/-- The tangent trivialization at `x₀`. -/
abbrev tTriv (x₀ : M) : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _) → M) :=
  trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type _) x₀

/-- A vector field in the trivialization at `x₀`: a function `M → E`. -/
def hat (x₀ : M) (σ : Π y : M, TangentSpace 𝓘(ℝ, E) y) : M → E :=
  fun z => (tTriv (E := E) x₀ (⟨z, σ z⟩ : TotalSpace E (TangentSpace 𝓘(ℝ, E) : M → Type _))).2

/-- A vector field is differentiable at `z` in the chart domain iff its components in the trivialization are. -/
theorem mdiffAt_hat_iff (x₀ : M) (σ : Π y : M, TangentSpace 𝓘(ℝ, E) y) {z : M}
    (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun q : M => (⟨q, σ q⟩ : TangentBundle 𝓘(ℝ, E) M)) z ↔
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ σ) z := by
  exact (tTriv (E := E) x₀).mdifferentiableAt_section_iff 𝓘(ℝ, E) σ hz

variable (x₀ : M)

/-- The components in the trivialization are additive on the chart domain. -/
theorem hat_add {σ σ' : Π y : M, TangentSpace 𝓘(ℝ, E) y} {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    hat x₀ (σ + σ') z = hat x₀ σ z + hat x₀ σ' z :=
  ((tTriv (E := E) x₀).linear ℝ hz).map_add _ _

/-- The components in the trivialization are homogeneous on the chart domain. -/
theorem hat_smul {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} (f : M → ℝ) {z : M}
    (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    hat x₀ (f • σ) z = f z • hat x₀ σ z :=
  ((tTriv (E := E) x₀).linear ℝ hz).map_smul _ _

/-- The covariant derivative of the trivialization at `x₀`: `∇⁰_u σ = e⁻¹ (D σ̂ (u))`. -/
def cov0 (σ : Π y : M, TangentSpace 𝓘(ℝ, E) y) (z : M) :
    TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace 𝓘(ℝ, E) z :=
  ((tTriv (E := E) x₀).symmL ℝ z).comp (mvfderiv 𝓘(ℝ, E) (hat x₀ σ) z)

/-- Reading a field in the trivialization and returning gives back the field. -/
theorem symmL_hat {σ : Π y : M, TangentSpace 𝓘(ℝ, E) y} {z : M} (hz : z ∈ (tTriv (E := E) x₀).baseSet) :
    (tTriv (E := E) x₀).symmL ℝ z (hat x₀ σ z) = σ z := by
  rw [Trivialization.symmL_apply _ hz]
  exact (tTriv (E := E) x₀).symm_apply_apply_mk hz (σ z)

/-- `mvfderiv` only depends on the germ. -/
theorem mvfderiv_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₁ f₂ : M → F} {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv 𝓘(ℝ, E) f₁ x = mvfderiv 𝓘(ℝ, E) f₂ x := by
  unfold mvfderiv
  rw [h.mfderiv_eq]
  ext v
  simp [tangentSpaceCast, fromTangentSpace]
  rfl

/-- The connection `cov0` of the trivialization is a covariant derivative on the chart domain. -/
theorem cov0_isCov : IsCovariantDerivativeOn E (cov0 (E := E) (M := M) x₀) (tTriv (E := E) x₀).baseSet where
  add {σ σ'} {x} hσ hσ' hx := by
    have h1 := (mdiffAt_hat_iff x₀ σ hx).1 hσ
    have h2 := (mdiffAt_hat_iff x₀ σ' hx).1 hσ'
    have heq : hat x₀ (σ + σ') =ᶠ[𝓝 x] hat x₀ σ + hat x₀ σ' := by
      filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hx] with z hz
      exact hat_add x₀ hz
    unfold cov0
    rw [mvfderiv_congr heq, mvfderiv_add h1 h2, ContinuousLinearMap.comp_add]
  leibniz {σ g} {x} hσ hg hx := by
    have h1 := (mdiffAt_hat_iff x₀ σ hx).1 hσ
    have heq : hat x₀ (g • σ) =ᶠ[𝓝 x] g • hat x₀ σ := by
      filter_upwards [(tTriv (E := E) x₀).open_baseSet.mem_nhds hx] with z hz
      exact hat_smul x₀ g hz
    unfold cov0
    rw [mvfderiv_congr heq, mvfderiv_smul hg h1]
    ext u
    simp [symmL_hat x₀ hx]
end Lightlike
