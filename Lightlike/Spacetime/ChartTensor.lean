import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.GR.Einstein
/-!
# Tensoriality of covariant derivatives of bilinear fields, in a chart (step 1 of the divergence-free Einstein tensor)

For a bilinear form field with components `B̂ : M → E →L E →L ℝ` in the tangent trivialization at `x₀`, the
covariant derivative `(∇_X B)(v, w)` is given by the components formula
`D B̂ (X) (v, w) - B̂ (Γ̂(v, X), w) - B̂ (v, Γ̂(w, X))` (`covDerivBilinAt_bilOf`). It is therefore independent of the
extensions of `v, w` and trilinear. Applied to the coordinate components of the Einstein tensor of a Levi-Civita
connection (`covDerivBilinAt_einstein`). Also: smoothness of the coordinate Riemann, Ricci, scalar curvature and Einstein
tensors on the domain of a coordinate metric.

**Limits.** Boundaryless Hausdorff manifold modelled on `Fin n → ℝ`, `C^∞` connection and `C²` structure. No statement
about the divergence yet; this is a supporting layer for `T-GE1-P8`, which stays open.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
section Coord
variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The Riemann tensor is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetric.contDiffOn_riemann (hg : IsCoordMetric g U) (ρ σ μ ν : Fin n) :
    ContDiffOn ℝ ∞ (riemann g ρ σ μ ν) U := by
  have hΓ := hg.contDiffOn_christoffel
  unfold riemann
  refine ContDiffOn.add (ContDiffOn.sub (contDiffOn_pd (hΓ _ _ _) hg.isOpen _)
    (contDiffOn_pd (hΓ _ _ _) hg.isOpen _)) ?_
  exact ContDiffOn.sum fun l _ => ((hΓ _ _ _).mul (hΓ _ _ _)).sub ((hΓ _ _ _).mul (hΓ _ _ _))

/-- The Ricci tensor is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetric.contDiffOn_ricci (hg : IsCoordMetric g U) (σ ν : Fin n) :
    ContDiffOn ℝ ∞ (ricci g σ ν) U := by
  unfold ricci
  exact ContDiffOn.sum fun ρ _ => hg.contDiffOn_riemann ρ σ ρ ν

/-- The scalar curvature is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetric.contDiffOn_scalarCurvature (hg : IsCoordMetric g U) :
    ContDiffOn ℝ ∞ (scalarCurvature g) U := by
  unfold scalarCurvature
  exact ContDiffOn.sum fun σ _ => ContDiffOn.sum fun ν _ =>
    (hg.contDiffOn_inv σ ν).mul (hg.contDiffOn_ricci σ ν)

/-- The Einstein tensor is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetric.contDiffOn_einsteinTensor (hg : IsCoordMetric g U) (μ ν : Fin n) :
    ContDiffOn ℝ ∞ (einsteinTensor g μ ν) U := by
  unfold einsteinTensor
  exact (hg.contDiffOn_ricci μ ν).sub (((contDiffOn_const).mul hg.contDiffOn_scalarCurvature).mul (hg.smooth μ ν))
end Coord
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
variable (cov : Connection 𝓘(ℝ, E) M) [LocallySmoothConnection cov] (x₀ : M)

/-- A bilinear form field with components `B̂ y : E →L E →L ℝ` in the trivialization at `x₀`. -/
def bilOf (B : M → E →L[ℝ] E →L[ℝ] ℝ) (y : M) (u v : TangentSpace 𝓘(ℝ, E) y) : ℝ :=
  B y (hv x₀ y u) (hv x₀ y v)

/-- **The covariant derivative of a bilinear form field in components.** -/
theorem covDeriv_bil_components {B : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}
    (hx : x ∈ (tTriv (E := E) x₀).baseSet)
    (hB : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) B x)
    {V W : Π y : M, TangentSpace 𝓘(ℝ, E) y} (hV : SmoothNear V x) (hW : SmoothNear W x)
    (X₀ : TangentSpace 𝓘(ℝ, E) x) :
    (mvfderiv 𝓘(ℝ, E) (fun y => bilOf x₀ B y (V y) (W y)) x X₀
        - bilOf x₀ B x (cov V x X₀) (W x) - bilOf x₀ B x (V x) (cov W x X₀)) =
      (mvfderiv 𝓘(ℝ, E) B x X₀) (hv x₀ x (V x)) (hv x₀ x (W x))
        - B x (gamHat cov x₀ x (hv x₀ x (V x)) (hv x₀ x X₀)) (hv x₀ x (W x))
        - B x (hv x₀ x (V x)) (gamHat cov x₀ x (hv x₀ x (W x)) (hv x₀ x X₀)) := by
  have mV := mdiffAt_of_smoothNear hV
  have mW := mdiffAt_of_smoothNear hW
  have hV' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ V) x := (mdiffAt_hat_iff x₀ V hx).1 mV
  have hW' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hat x₀ W) x := (mdiffAt_hat_iff x₀ W hx).1 mW
  have hG : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℝ) (fun y => B y (hat x₀ V y)) x := hB.clm_apply hV'
  have e1 : (fun y => bilOf x₀ B y (V y) (W y)) = fun y => (fun y => B y (hat x₀ V y)) y (hat x₀ W y) := rfl
  rw [e1, mvfderiv_clm_apply _ _ x hG hW' X₀, mvfderiv_clm_apply _ _ x hB hV' X₀,
    bilOf, bilOf, hat_cov cov x₀ hx mV X₀, hat_cov cov x₀ hx mW X₀]
  simp only [map_add, add_apply]
  have e2 : hat x₀ V x = hv x₀ x (V x) := rfl
  have e3 : hat x₀ W x = hv x₀ x (W x) := rfl
  rw [e2, e3]
  abel

/-- **`covDerivBilinAt` of a bilinear form with components `B̂` is given by the components formula**, so it is
independent of the extensions and trilinear in `X₀, v₀, w₀`. -/
theorem covDerivBilinAt_bilOf {B : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}
    (hx : x ∈ (tTriv (E := E) x₀).baseSet)
    (hB : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) B x)
    (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, E) x) :
    cov.covDerivBilinAt (bilOf x₀ B) x X₀ v₀ w₀ =
      (mvfderiv 𝓘(ℝ, E) B x X₀) (hv x₀ x v₀) (hv x₀ x w₀)
        - B x (gamHat cov x₀ x (hv x₀ x v₀) (hv x₀ x X₀)) (hv x₀ x w₀)
        - B x (hv x₀ x v₀) (gamHat cov x₀ x (hv x₀ x w₀) (hv x₀ x X₀)) := by
  have h := covDeriv_bil_components cov x₀ hx hB (eventually_extend x v₀) (eventually_extend x w₀) X₀
  simp only [FiberBundle.extend_apply_self] at h
  exact h

/-- A finite sum of smooth scalar coefficients times constant vectors is differentiable. -/
theorem differentiableAt_sum_smul {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → κ → F → ℝ) (K : ι → κ → V) {y : F} (hc : ∀ i j, DifferentiableAt ℝ (c i j) y) :
    DifferentiableAt ℝ (fun y' => ∑ i, ∑ j, c i j y' • K i j) y :=
  DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => (hc i j).smul_const _

section Einstein
set_option synthInstance.maxHeartbeats 400000
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- The components of the Einstein tensor of the coordinate metric, as a bilinear form on `ℝⁿ`. -/
def einsteinComp (x₀ : M) (y' : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ σ, ∑ ν, einsteinTensor (g.coordMetric x₀) σ ν y' •
    (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)

/-- The component field of the Einstein tensor in the chart at `x₀`. -/
def BE (x₀ : M) (y : M) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  einsteinComp g x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y)

/-- The value of the component form `einsteinComp` on two vectors of `ℝⁿ`. -/
theorem einsteinComp_apply (x₀ : M) (y' : Fin n → ℝ) (a b : Fin n → ℝ) :
    einsteinComp g x₀ y' a b = ∑ σ, ∑ ν, a σ * b ν * einsteinTensor (g.coordMetric x₀) σ ν y' := by
  unfold einsteinComp
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- The component field `BE` of the Einstein tensor is differentiable on the chart domain. -/
theorem mdiffAt_BE {x₀ x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) :
    MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (BE g x₀) x := by
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hx
  have hgc := g.isCoordMetric_coordMetric x₀
  have hd : DifferentiableAt ℝ (einsteinComp g x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) := by
    unfold einsteinComp
    have hc : ∀ σ ν : Fin n, DifferentiableAt ℝ (fun y' => einsteinTensor (g.coordMetric x₀) σ ν y')
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ x) := fun σ ν =>
      differentiableAt_of_contDiffOn (hgc.contDiffOn_einsteinTensor σ ν) hgc.isOpen hy
    exact differentiableAt_sum_smul (fun σ ν y' => einsteinTensor (g.coordMetric x₀) σ ν y')
      (fun σ ν => (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)) hc
  have hφ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀) x :=
    mdifferentiableAt_extChartAt (by simpa using hx)
  exact (hd.mdifferentiableAt).comp x hφ
variable (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) [LocallySmoothConnection cov]

/-- **`einsteinField` equals the bilinear form with components `BE`** on the trivialization domain. -/
theorem einsteinField_eq_bilOf (x₀ : M) (h : cov.IsLeviCivita g) {y : M}
    (hy : y ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    cov.einsteinField g y u v = bilOf x₀ (BE g x₀) y u v := by
  have hzs : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hy
  have hty : extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).map_source hzs
  have c1 : ∀ σ ν : Fin n, cov.ricciAt y (coordField x₀ σ y) (coordField x₀ ν y) =
      ricci (g.coordMetric x₀) σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y) := fun σ ν => by
    have hr := ricciAt_coord cov x₀ g h hty ν σ
    rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hzs] at hr
    rw [ricciAt_symm_proved cov g h.1 h.2 y _ _]
    exact hr
  have c2 : cov.scalarCurvatureAt g y = scalarCurvature (g.coordMetric x₀) (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y) := by
    have hs := scalarCurvatureAt_coord cov x₀ g h hty
    rwa [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hzs] at hs
  have c3 : ∀ σ ν : Fin n, g.g y (coordField x₀ σ y) (coordField x₀ ν y) =
      g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y) σ ν := fun σ ν => by
    have hg := g_coordField g x₀ σ ν hty
    rwa [(extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).left_inv hzs] at hg
  have expand : ∀ w : TangentSpace 𝓘(ℝ, Fin n → ℝ) y,
      w = ∑ σ, hv x₀ y w σ • coordField x₀ σ y := fun w => by
    have hpi : hv x₀ y w = ∑ σ, hv x₀ y w σ • (Pi.single σ 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    calc w = (tTriv (E := Fin n → ℝ) x₀).symmL ℝ y (hv x₀ y w) := (symmL_hv x₀ hy w).symm
      _ = (tTriv (E := Fin n → ℝ) x₀).symmL ℝ y (∑ σ, hv x₀ y w σ • (Pi.single σ 1 : Fin n → ℝ)) := by
          exact congrArg _ hpi
      _ = ∑ σ, hv x₀ y w σ • coordField x₀ σ y := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [map_smul, symmL_eq_coordField x₀ hy σ]
  unfold Connection.einsteinField bilOf
  rw [BE, einsteinComp_apply]
  have hRic : cov.ricciAt y u v = ∑ σ, ∑ ν, hv x₀ y u σ * hv x₀ y v ν *
      ricci (g.coordMetric x₀) σ ν (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y) := by
    have e : RicB cov x₀ hy u v = RicB cov x₀ hy (∑ σ, hv x₀ y u σ • coordField x₀ σ y)
        (∑ ν, hv x₀ y v ν • coordField x₀ ν y) := by rw [← expand u, ← expand v]
    have e' : cov.ricciAt y u v = RicB cov x₀ hy u v := rfl
    rw [e', e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    have : RicB cov x₀ hy (coordField x₀ σ y) (coordField x₀ ν y) = cov.ricciAt y (coordField x₀ σ y) (coordField x₀ ν y) := rfl
    rw [this, c1]; ring
  have hg : g.g y u v = ∑ σ, ∑ ν, hv x₀ y u σ * hv x₀ y v ν *
      g.coordMetric x₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ y) σ ν := by
    have e : g.g y u v = g.g y (∑ σ, hv x₀ y u σ • coordField x₀ σ y)
        (∑ ν, hv x₀ y v ν • coordField x₀ ν y) := by rw [← expand u, ← expand v]
    rw [e]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [c3]; ring
  rw [hRic, hg, c2]
  unfold einsteinTensor
  rw [Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- **The covariant derivative of the Einstein tensor in components**: `covDerivBilinAt` of `einsteinField` is the
components formula with the coordinate Einstein tensor (so it is independent of the extensions and trilinear). -/
theorem covDerivBilinAt_einstein (x₀ : M) (h : cov.IsLeviCivita g) {x : M}
    (hx : x ∈ (tTriv (E := Fin n → ℝ) x₀).baseSet) (X₀ v₀ w₀ : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X₀ v₀ w₀ =
      (mvfderiv 𝓘(ℝ, Fin n → ℝ) (BE g x₀) x X₀) (hv x₀ x v₀) (hv x₀ x w₀)
        - BE g x₀ x (gamHat cov x₀ x (hv x₀ x v₀) (hv x₀ x X₀)) (hv x₀ x w₀)
        - BE g x₀ x (hv x₀ x v₀) (gamHat cov x₀ x (hv x₀ x w₀) (hv x₀ x X₀)) := by
  have hxs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source := by
    rw [extChartAt_source]; simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hx
  rw [← covDerivBilinAt_bilOf cov x₀ hx (mdiffAt_BE g hxs)]
  unfold Connection.covDerivBilinAt
  have heq : (fun y => cov.einsteinField g y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y))
      =ᶠ[nhds x] fun y => bilOf x₀ (BE g x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y) := by
    filter_upwards [(tTriv (E := Fin n → ℝ) x₀).open_baseSet.mem_nhds hx] with y hy
    exact einsteinField_eq_bilOf g cov x₀ h hy _ _
  have hm : mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun y => cov.einsteinField g y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun y => bilOf x₀ (BE g x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ := by
    rw [heq.mfderiv_eq]
    simp [tangentSpaceCast]
    rfl
  simp only [einsteinField_eq_bilOf g cov x₀ h hx]
  rw [hm]
end Einstein
end Lightlike
