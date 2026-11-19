import Lightlike.Spacetime.BianchiSecond
import Lightlike.Spacetime.Corners.BianchiSecond
import Lightlike.Spacetime.ChartAgreement
import Lightlike.Spacetime.Corners.ChartAgreement
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.RiemannSymmetryWithin
import Lightlike.Spacetime.CurvatureWithin
import Lightlike.GR.Einstein
import Lightlike.Spacetime.Corners.ChartCovariant
/-!
# Tensoriality of covariant derivatives of bilinear fields, in a chart (step 1 of the divergence-free Einstein tensor)

For a bilinear form field with components `B̂ : M → E →L E →L ℝ` in the tangent trivialization at `x₀`, the
covariant derivative `(∇_X B)(v, w)` is given by the components formula
`D B̂ (X) (v, w) - B̂ (Γ̂(v, X), w) - B̂ (v, Γ̂(w, X))` (`covDerivBilinAt_bilOfW`). It is therefore independent of the
extensions of `v, w` and trilinear. Applied to the coordinate components of the Einstein tensor of a Levi-Civita
connection (`covDerivBilinAt_einsteinW`). Also: smoothness of the coordinate Riemann, Ricci, scalar curvature and
Einstein tensors on the domain of a coordinate metric (`IsCoordMetricW.contDiffOn_einsteinTensorW`).

**Limits.** Manifold with corners (any `ModelWithCorners`); the coordinate Einstein tensor is differentiated within `range I`; locally smooth connection and `C²` structure. The
divergence of the Einstein tensor built on this file is `einstein_divergence_free_provedW` (`Lightlike/Spacetime/Corners/DivergenceFree.lean`);
`T-GE1-P8` stays open (the model space there is `Fin n → ℝ`).

This is the Corners layer of the CO30 branch: the versions for any model with corners of the declarations of
`Lightlike/Spacetime/ChartTensor.lean` that the CO30 and GE11 files use, with a `W` suffix where the boundaryless file owns the name.
-/

open Bundle Manifold Set VectorField NormedSpace FiberBundle Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Lightlike
section Coord
variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The Riemann tensor within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_riemannW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) (ρ σ μ ν : Fin n) :
    ContDiffOn ℝ ∞ (riemannW S g ρ σ μ ν) U := by
  have hΓ := hg.contDiffOn_christoffel
  unfold riemannW
  refine ContDiffOn.add (ContDiffOn.sub (hg.contDiffOn_pdW (hΓ _ _ _) _) (hg.contDiffOn_pdW (hΓ _ _ _) _)) ?_
  exact ContDiffOn.sum fun l _ => ((hΓ _ _ _).mul (hΓ _ _ _)).sub ((hΓ _ _ _).mul (hΓ _ _ _))

/-- The Ricci tensor within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_ricciW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) (σ ν : Fin n) :
    ContDiffOn ℝ ∞ (ricciW S g σ ν) U := by
  unfold ricciW
  exact ContDiffOn.sum fun ρ _ => hg.contDiffOn_riemannW ρ σ ρ ν

/-- The scalar curvature within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_scalarCurvatureW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) :
    ContDiffOn ℝ ∞ (scalarCurvatureW S g) U := by
  unfold scalarCurvatureW
  exact ContDiffOn.sum fun σ _ => ContDiffOn.sum fun ν _ =>
    (hg.contDiffOn_inv σ ν).mul (hg.contDiffOn_ricciW σ ν)


/-- The Einstein tensor within `S` is smooth on the domain of a coordinate metric. -/
theorem IsCoordMetricW.contDiffOn_einsteinTensorW {S : Set (Fin n → ℝ)} (hg : IsCoordMetricW S g U) (μ ν : Fin n) :
    ContDiffOn ℝ ∞ (einsteinTensorW S g μ ν) U := by
  unfold einsteinTensorW
  exact (hg.contDiffOn_ricciW μ ν).sub (((contDiffOn_const).mul hg.contDiffOn_scalarCurvatureW).mul (hg.smooth μ ν))
end Coord
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [CompleteSpace E]
variable (cov : Connection I M) [LocallySmoothConnectionW cov] (x₀ : M)

/-- A bilinear form field with components `B̂ y : E →L E →L ℝ` in the trivialization at `x₀`. -/
def bilOfW (B : M → E →L[ℝ] E →L[ℝ] ℝ) (y : M) (u v : TangentSpace I y) : ℝ :=
  B y (hvW x₀ y u) (hvW x₀ y v)

/-- **The covariant derivative of a bilinear form field in components.** -/
theorem covDeriv_bil_componentsW {B : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}
    (hx : x ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    (hB : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) B x)
    {V W : Π y : M, TangentSpace I y} (hV : SmoothNearW V x) (hW : SmoothNearW W x)
    (X₀ : TangentSpace I x) :
    (mvfderiv I (fun y => bilOfW x₀ B y (V y) (W y)) x X₀
        - bilOfW x₀ B x (cov V x X₀) (W x) - bilOfW x₀ B x (V x) (cov W x X₀)) =
      (mvfderiv I B x X₀) (hvW x₀ x (V x)) (hvW x₀ x (W x))
        - B x (gamHatW cov x₀ x (hvW x₀ x (V x)) (hvW x₀ x X₀)) (hvW x₀ x (W x))
        - B x (hvW x₀ x (V x)) (gamHatW cov x₀ x (hvW x₀ x (W x)) (hvW x₀ x X₀)) := by
  have mV := mdiffAt_of_smoothNearW hV
  have mW := mdiffAt_of_smoothNearW hW
  have hV' : MDifferentiableAt I 𝓘(ℝ, E) (hatW x₀ V) x := (mdiffAt_hat_iffW x₀ V hx).1 mV
  have hW' : MDifferentiableAt I 𝓘(ℝ, E) (hatW x₀ W) x := (mdiffAt_hat_iffW x₀ W hx).1 mW
  have hG : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ) (fun y => B y (hatW x₀ V y)) x := hB.clm_apply hV'
  have e1 : (fun y => bilOfW x₀ B y (V y) (W y)) = fun y => (fun y => B y (hatW x₀ V y)) y (hatW x₀ W y) := rfl
  rw [e1, mvfderiv_clm_applyW _ _ x hG hW' X₀, mvfderiv_clm_applyW _ _ x hB hV' X₀,
    bilOfW, bilOfW, hat_covW cov x₀ hx mV X₀, hat_covW cov x₀ hx mW X₀]
  simp only [map_add, add_apply]
  have e2 : hatW x₀ V x = hvW x₀ x (V x) := rfl
  have e3 : hatW x₀ W x = hvW x₀ x (W x) := rfl
  rw [e2, e3]
  abel

/-- **`covDerivBilinAt` of a bilinear form with components `B̂` is given by the components formula**, so it is
independent of the extensions and trilinear in `X₀, v₀, w₀`. -/
theorem covDerivBilinAt_bilOfW {B : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}
    (hx : x ∈ (tTrivW (I := I) (E := E) x₀).baseSet)
    (hB : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) B x)
    (X₀ v₀ w₀ : TangentSpace I x) :
    cov.covDerivBilinAt (bilOfW x₀ B) x X₀ v₀ w₀ =
      (mvfderiv I B x X₀) (hvW x₀ x v₀) (hvW x₀ x w₀)
        - B x (gamHatW cov x₀ x (hvW x₀ x v₀) (hvW x₀ x X₀)) (hvW x₀ x w₀)
        - B x (hvW x₀ x v₀) (gamHatW cov x₀ x (hvW x₀ x w₀) (hvW x₀ x X₀)) := by
  have h := covDeriv_bil_componentsW cov x₀ hx hB (eventually_extendW x v₀) (eventually_extendW x w₀) X₀
  simp only [FiberBundle.extend_apply_self] at h
  exact h

/-- A finite sum of coefficients differentiable within a set times constant vectors is differentiable within it. -/
theorem differentiableWithinAt_sum_smul {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ι κ : Type*} [Fintype ι] [Fintype κ] {s : Set F}
    (c : ι → κ → F → ℝ) (K : ι → κ → V) {y : F} (hc : ∀ i j, DifferentiableWithinAt ℝ (c i j) s y) :
    DifferentiableWithinAt ℝ (fun y' => ∑ i, ∑ j, c i j y' • K i j) s y :=
  DifferentiableWithinAt.fun_sum fun i _ => DifferentiableWithinAt.fun_sum fun j _ => (hc i j).smul_const _


section Einstein
set_option synthInstance.maxHeartbeats 400000
variable {n : ℕ} {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (Fin n → ℝ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 2 M]
  (g : NondegMetric I M)

/-- The components of the Einstein tensor of the coordinate metric, as a bilinear form on `ℝⁿ`. -/
def einsteinCompW (x₀ : M) (y' : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ σ, ∑ ν, einsteinTensorW (range I) (g.coordMetricW x₀) σ ν y' •
    (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)

/-- The component field of the Einstein tensor in the chart at `x₀`. -/
def BEW (x₀ : M) (y : M) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  einsteinCompW g x₀ (extChartAt I x₀ y)

/-- The value of the component form `einsteinCompW` on two vectors of `ℝⁿ`. -/
theorem einsteinComp_applyW (x₀ : M) (y' : Fin n → ℝ) (a b : Fin n → ℝ) :
    einsteinCompW g x₀ y' a b = ∑ σ, ∑ ν, a σ * b ν * einsteinTensorW (range I) (g.coordMetricW x₀) σ ν y' := by
  unfold einsteinCompW
  simp only [sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- The component field `BEW` of the Einstein tensor is differentiable on the chart domain. -/
theorem mdiffAt_BEW {x₀ x : M} (hx : x ∈ (extChartAt I x₀).source) :
    MDifferentiableAt I 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (BEW g x₀) x := by
  have hy : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx
  have hgc := g.isCoordMetricW_coordMetric x₀
  have hd : DifferentiableWithinAt ℝ (einsteinCompW g x₀) (range I) (extChartAt I x₀ x) := by
    unfold einsteinCompW
    have hc : ∀ σ ν : Fin n, DifferentiableWithinAt ℝ
        (fun y' => einsteinTensorW (range I) (g.coordMetricW x₀) σ ν y') (range I) (extChartAt I x₀ x) := fun σ ν =>
      differentiableWithinAt_of_contDiffOn hgc (hgc.contDiffOn_einsteinTensorW σ ν) hy
    exact differentiableWithinAt_sum_smul (fun σ ν y' => einsteinTensorW (range I) (g.coordMetricW x₀) σ ν y')
      (fun σ ν => (ContinuousLinearMap.proj σ : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj ν : (Fin n → ℝ) →L[ℝ] ℝ)) hc
  have hφ : MDifferentiableAt I 𝓘(ℝ, Fin n → ℝ) (extChartAt I x₀) x :=
    mdifferentiableAt_extChartAt (by simpa using hx)
  have hd' : MDifferentiableWithinAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
      (einsteinCompW g x₀) (range I) (extChartAt I x₀ x) := mdifferentiableWithinAt_iff_differentiableWithinAt.2 hd
  have h1 := MDifferentiableWithinAt.comp (s := (univ : Set M)) x hd'
    hφ.mdifferentiableWithinAt (fun q _ => mem_range_self _)
  exact mdifferentiableWithinAt_univ.1 h1

variable (cov : Connection I M) [LocallySmoothConnectionW cov]


/-- **`einsteinField` equals the bilinear form with components `BEW`** on the trivialization domain. -/
theorem einsteinField_eq_bilOfW (x₀ : M) (h : cov.IsLeviCivita g) {y : M}
    (hy : y ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (u v : TangentSpace I y) :
    cov.einsteinField g y u v = bilOfW x₀ (BEW g x₀) y u v := by
  have hzs : y ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hy
  have hty : extChartAt I x₀ y ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hzs
  have c1 : ∀ σ ν : Fin n, cov.ricciAt y (coordFieldW x₀ σ y) (coordFieldW x₀ ν y) =
      ricciW (range I) (g.coordMetricW x₀) σ ν (extChartAt I x₀ y) := fun σ ν => by
    have hr := ricciAt_coordW cov x₀ g h hty ν σ
    rw [(extChartAt I x₀).left_inv hzs] at hr
    rw [ricciAt_symm_provedW cov g h.1 h.2 y _ _]
    exact hr
  have c2 : cov.scalarCurvatureAt g y = scalarCurvatureW (range I) (g.coordMetricW x₀) (extChartAt I x₀ y) := by
    have hs := scalarCurvatureAt_coordW cov x₀ g h hty
    rwa [(extChartAt I x₀).left_inv hzs] at hs
  have c3 : ∀ σ ν : Fin n, g.g y (coordFieldW x₀ σ y) (coordFieldW x₀ ν y) =
      g.coordMetricW x₀ (extChartAt I x₀ y) σ ν := fun σ ν => by
    have hg := g_coordFieldW g x₀ σ ν hty
    rwa [(extChartAt I x₀).left_inv hzs] at hg
  have expand : ∀ w : TangentSpace I y,
      w = ∑ σ, hvW x₀ y w σ • coordFieldW x₀ σ y := fun w => by
    have hpi : hvW x₀ y w = ∑ σ, hvW x₀ y w σ • (Pi.single σ 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    calc w = (tTrivW (I := I) (E := Fin n → ℝ) x₀).symmL ℝ y (hvW x₀ y w) := (symmL_hvW x₀ hy w).symm
      _ = (tTrivW (I := I) (E := Fin n → ℝ) x₀).symmL ℝ y (∑ σ, hvW x₀ y w σ • (Pi.single σ 1 : Fin n → ℝ)) := by
          exact congrArg _ hpi
      _ = ∑ σ, hvW x₀ y w σ • coordFieldW x₀ σ y := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [map_smul, symmL_eq_coordFieldW x₀ hy σ]
  unfold Connection.einsteinField bilOfW
  rw [BEW, einsteinComp_applyW]
  have hRic : cov.ricciAt y u v = ∑ σ, ∑ ν, hvW x₀ y u σ * hvW x₀ y v ν *
      ricciW (range I) (g.coordMetricW x₀) σ ν (extChartAt I x₀ y) := by
    have e : RicBW cov x₀ hy u v = RicBW cov x₀ hy (∑ σ, hvW x₀ y u σ • coordFieldW x₀ σ y)
        (∑ ν, hvW x₀ y v ν • coordFieldW x₀ ν y) := by rw [← expand u, ← expand v]
    have e' : cov.ricciAt y u v = RicBW cov x₀ hy u v := rfl
    rw [e', e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    have : RicBW cov x₀ hy (coordFieldW x₀ σ y) (coordFieldW x₀ ν y) = cov.ricciAt y (coordFieldW x₀ σ y) (coordFieldW x₀ ν y) := rfl
    rw [this, c1]; ring
  have hg : g.g y u v = ∑ σ, ∑ ν, hvW x₀ y u σ * hvW x₀ y v ν *
      g.coordMetricW x₀ (extChartAt I x₀ y) σ ν := by
    have e : g.g y u v = g.g y (∑ σ, hvW x₀ y u σ • coordFieldW x₀ σ y)
        (∑ ν, hvW x₀ y v ν • coordFieldW x₀ ν y) := by rw [← expand u, ← expand v]
    rw [e]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [c3]; ring
  rw [hRic, hg, c2]
  unfold einsteinTensorW
  rw [Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- **The covariant derivative of the Einstein tensor in components**: `covDerivBilinAt` of `einsteinField` is the
components formula with the coordinate Einstein tensor (so it is independent of the extensions and trilinear). -/
theorem covDerivBilinAt_einsteinW (x₀ : M) (h : cov.IsLeviCivita g) {x : M}
    (hx : x ∈ (tTrivW (I := I) (E := Fin n → ℝ) x₀).baseSet) (X₀ v₀ w₀ : TangentSpace I x) :
    cov.covDerivBilinAt (cov.einsteinField g) x X₀ v₀ w₀ =
      (mvfderiv I (BEW g x₀) x X₀) (hvW x₀ x v₀) (hvW x₀ x w₀)
        - BEW g x₀ x (gamHatW cov x₀ x (hvW x₀ x v₀) (hvW x₀ x X₀)) (hvW x₀ x w₀)
        - BEW g x₀ x (hvW x₀ x v₀) (gamHatW cov x₀ x (hvW x₀ x w₀) (hvW x₀ x X₀)) := by
  have hxs : x ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]; simpa [tTrivW, TangentBundle.trivializationAt_baseSet] using hx
  rw [← covDerivBilinAt_bilOfW cov x₀ hx (mdiffAt_BEW g hxs)]
  unfold Connection.covDerivBilinAt
  have heq : (fun y => cov.einsteinField g y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y))
      =ᶠ[nhds x] fun y => bilOfW x₀ (BEW g x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y) := by
    filter_upwards [(tTrivW (I := I) (E := Fin n → ℝ) x₀).open_baseSet.mem_nhds hx] with y hy
    exact einsteinField_eq_bilOfW g cov x₀ h hy _ _
  have hm : mfderiv I 𝓘(ℝ, ℝ) (fun y => cov.einsteinField g y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ =
      mfderiv I 𝓘(ℝ, ℝ) (fun y => bilOfW x₀ (BEW g x₀) y (FiberBundle.extend (Fin n → ℝ) v₀ y) (FiberBundle.extend (Fin n → ℝ) w₀ y)) x X₀ := by
    rw [heq.mfderiv_eq]
    simp [tangentSpaceCast]
    rfl
  simp only [einsteinField_eq_bilOfW g cov x₀ h hx]
  rw [hm]

end Einstein
end Lightlike
