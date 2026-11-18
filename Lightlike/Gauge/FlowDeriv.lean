import Lightlike.Gauge.GaugeFlow
import Lightlike.Gauge.LinearODE
import Mathlib.Analysis.ODE.ExistUnique

/-!
# The derivative of an observable along a curve in phase space

For an observable `F` of the phase space `X × X` (jointly differentiable) and a curve `γ` with derivative `γ'` at `t`,
`d/dt F (γ t) = pairing (∇F) γ'` with `∇F = phaseGrad F` the partial gradients: the chain rule in the form used for the
invariance of the constraint surface under a Hamiltonian flow. Along a Hamiltonian curve `γ' = X_g (γ)` this is the
Poisson bracket `{F, g}` (`pairing_hamField`).
-/

open InnerProductSpace
open ClassicalMechanics

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **The differential of an observable on a tangent vector**: `dF (u, v) = ⟨∇_p F, u⟩ + ⟨∇_q F, v⟩`. -/
theorem fderiv_apply_eq_pairing (F : X → X → ℝ) {p q : X} (hF : DifferentiableAt ℝ (fun z : X × X => F z.1 z.2) (p, q))
    (w : X × X) : fderiv ℝ (fun z : X × X => F z.1 z.2) (p, q) w = pairing (phaseGrad F p q) w := by
  set Fz : X × X → ℝ := fun z => F z.1 z.2 with hFz
  have h1 : HasFDerivAt (fun p' : X => F p' q) ((fderiv ℝ Fz (p, q)).comp (ContinuousLinearMap.inl ℝ X X)) p := by
    have := HasFDerivAt.comp p (show HasFDerivAt Fz _ (p, q) from hF.hasFDerivAt) (hasFDerivAt_prodMk_left (𝕜 := ℝ) p q)
    exact this
  have h2 : HasFDerivAt (fun q' : X => F p q') ((fderiv ℝ Fz (p, q)).comp (ContinuousLinearMap.inr ℝ X X)) q := by
    have := HasFDerivAt.comp q (show HasFDerivAt Fz _ (p, q) from hF.hasFDerivAt) (hasFDerivAt_prodMk_right (𝕜 := ℝ) p q)
    exact this
  have e1 : ⟪gradient (fun p' : X => F p' q) p, w.1⟫_ℝ = fderiv ℝ Fz (p, q) (w.1, 0) := by
    rw [gradient, toDual_symm_apply, h1.fderiv]; rfl
  have e2 : ⟪gradient (fun q' : X => F p q') q, w.2⟫_ℝ = fderiv ℝ Fz (p, q) (0, w.2) := by
    rw [gradient, toDual_symm_apply, h2.fderiv]; rfl
  have hw : w = (w.1, 0) + (0, w.2) := by simp
  conv_lhs => rw [hw, map_add]
  simp only [pairing, phaseGrad, e1, e2]

/-- **The chain rule along a curve**: `d/dt F (γ t) = pairing (∇F) γ'`. -/
theorem hasDerivAt_comp_curve (F : X → X → ℝ) (γ : ℝ → X × X) {γ' : X × X} {t : ℝ}
    (hF : DifferentiableAt ℝ (fun z : X × X => F z.1 z.2) (γ t)) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => F (γ s).1 (γ s).2) (pairing (phaseGrad F (γ t).1 (γ t).2) γ') t := by
  have h := HasFDerivAt.comp_hasDerivAt t (show HasFDerivAt (fun z : X × X => F z.1 z.2) _ (γ t) from
    hF.hasFDerivAt) hγ
  rw [show (γ t) = ((γ t).1, (γ t).2) from rfl, fderiv_apply_eq_pairing F (by simpa using hF)] at h
  exact h

/-- The partial gradients are, as functions of the point, continuous linear images of `fderiv`. -/
theorem phaseGrad_eq (F : X → X → ℝ) (hF : Differentiable ℝ (fun z : X × X => F z.1 z.2)) (z : X × X) :
    phaseGrad F z.1 z.2 =
      ((toDual ℝ X).symm ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip (ContinuousLinearMap.inl ℝ X X)
          (fderiv ℝ (fun z : X × X => F z.1 z.2) z)),
        (toDual ℝ X).symm ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip (ContinuousLinearMap.inr ℝ X X)
          (fderiv ℝ (fun z : X × X => F z.1 z.2) z))) := by
  obtain ⟨p, q⟩ := z
  have h1 : HasFDerivAt (fun p' : X => F p' q) ((fderiv ℝ (fun z : X × X => F z.1 z.2) (p, q)).comp
      (ContinuousLinearMap.inl ℝ X X)) p := by
    have := HasFDerivAt.comp p (show HasFDerivAt (fun z : X × X => F z.1 z.2) _ (p, q) from
      (hF (p, q)).hasFDerivAt) (hasFDerivAt_prodMk_left (𝕜 := ℝ) p q)
    exact this
  have h2 : HasFDerivAt (fun q' : X => F p q') ((fderiv ℝ (fun z : X × X => F z.1 z.2) (p, q)).comp
      (ContinuousLinearMap.inr ℝ X X)) q := by
    have := HasFDerivAt.comp q (show HasFDerivAt (fun z : X × X => F z.1 z.2) _ (p, q) from
      (hF (p, q)).hasFDerivAt) (hasFDerivAt_prodMk_right (𝕜 := ℝ) p q)
    exact this
  simp only [phaseGrad, gradient, h1.fderiv, h2.fderiv]
  rfl

/-- The Riesz map `StrongDual ℝ X → X` as a continuous real-linear map. -/
noncomputable def rieszL : StrongDual ℝ X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := (toDual ℝ X).symm
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c a => by simpa using (toDual ℝ X).symm.map_smulₛₗ c a } 1
    (fun a => by simp)

/-- **The Hamiltonian field of a `C²` observable is `C¹`**. -/
theorem contDiff_hamField (F : X → X → ℝ) (hF : ContDiff ℝ 2 (fun z : X × X => F z.1 z.2)) :
    ContDiff ℝ 1 (fun z : X × X => hamField F z.1 z.2) := by
  have hd : ContDiff ℝ 1 (fun z : X × X => fderiv ℝ (fun z : X × X => F z.1 z.2) z) :=
    hF.fderiv_right (by norm_num)
  have hA1 : ContDiff ℝ 1 (fun z : X × X => rieszL ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inl ℝ X X) (fderiv ℝ (fun z : X × X => F z.1 z.2) z))) := by
    have := rieszL.contDiff.comp (((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inl ℝ X X)).contDiff.comp hd)
    exact this
  have hA2 : ContDiff ℝ 1 (fun z : X × X => rieszL ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inr ℝ X X) (fderiv ℝ (fun z : X × X => F z.1 z.2) z))) := by
    have := rieszL.contDiff.comp (((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inr ℝ X X)).contDiff.comp hd)
    exact this
  have heq : (fun z : X × X => hamField F z.1 z.2) = fun z => (-(rieszL ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inr ℝ X X) (fderiv ℝ (fun z : X × X => F z.1 z.2) z))), rieszL ((ContinuousLinearMap.compL ℝ X (X × X) ℝ).flip
      (ContinuousLinearMap.inl ℝ X X) (fderiv ℝ (fun z : X × X => F z.1 z.2) z))) := by
    funext z
    have := phaseGrad_eq F (hF.differentiable (by norm_num)) z
    simp only [hamField, this]
    rfl
  rw [heq]
  exact hA2.neg.prodMk hA1

variable {m : ℕ}

/-- **The constraint surface is invariant under the flow of a constraint, for an involutive set**: let `γ` solve
`γ' = X_{φ_a}(γ)` on `[0, T]`, let the brackets `{φ_b, φ_a}` be combinations `∑_c f_{bc} φ_c` with continuous
coefficients (involutivity), and let `γ 0` lie on the surface. Then `γ t` lies on the surface for `t ∈ [0, T]`. -/
theorem surface_invariant (φ : Fin m → X → X → ℝ) (a : Fin m)
    (hφ : ∀ b, Differentiable ℝ (fun z : X × X => φ b z.1 z.2))
    (f : Fin m → Fin m → X × X → ℝ) (hf : ∀ b c, Continuous (f b c))
    (hinv : ∀ b z, poissonBracket (φ b) (φ a) z.1 z.2 = ∑ c, f b c z * φ c z.1 z.2)
    (γ : ℝ → X × X) {T : ℝ} (hγ : ∀ t ∈ Set.Icc 0 T, HasDerivAt γ (hamField (φ a) (γ t).1 (γ t).2) t)
    (h0 : ∀ b, φ b (γ 0).1 (γ 0).2 = 0) : ∀ t ∈ Set.Icc 0 T, ∀ b, φ b (γ t).1 (γ t).2 = 0 := by
  have hdiff : ∀ b t, t ∈ Set.Icc 0 T → HasDerivAt (fun s => φ b (γ s).1 (γ s).2)
      (∑ c, f b c (γ t) * φ c (γ t).1 (γ t).2) t := by
    intro b t ht
    have := hasDerivAt_comp_curve (φ b) γ ((hφ b) _) (hγ t ht)
    rwa [pairing_hamField, hinv] at this
  have hγc : ContinuousOn γ (Set.Icc 0 T) := fun t ht => (hγ t ht).continuousAt.continuousWithinAt
  have hy : ContinuousOn (fun t => fun b => φ b (γ t).1 (γ t).2) (Set.Icc 0 T) :=
    continuousOn_pi.mpr fun b => fun t ht => (hdiff b t ht).continuousAt.continuousWithinAt
  have hA : ∀ i j, ContinuousOn (fun t => (fun t => Matrix.of (fun b c => f b c (γ t))) t i j) (Set.Icc 0 T) :=
    fun i j => ((hf i j).comp_continuousOn hγc)
  have key := eq_zero_of_linear_ode (fun t b => φ b (γ t).1 (γ t).2) (fun t => Matrix.of fun b c => f b c (γ t))
    (T := T) hA (fun t ht => by
      refine HasDerivAt.hasDerivWithinAt ?_
      refine hasDerivAt_pi.mpr fun b => ?_
      simpa [Matrix.mulVec, dotProduct] using hdiff b t ⟨ht.1, ht.2.le⟩) hy (funext h0)
  intro t ht b
  exact congrFun (key t ht) b

/-- **A local gauge flow that stays on the surface**: if `φ_a` is `C²` (so that its Hamiltonian vector field is `C¹`,
`contDiff_hamField`), the constraints are differentiable and involutive with continuous coefficients, there is a curve `γ` with `γ 0 = x₀` solving `γ' = X_{φ_a}(γ)` on an open interval around `0`, and
`γ t` stays on the surface for `t` in the forward half of it. Local existence is Mathlib's Picard-Lindelöf
(`ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`). -/
theorem exists_flow_on_surface (φ : Fin m → X → X → ℝ) (a : Fin m)
    (hφ : ∀ b, Differentiable ℝ (fun z : X × X => φ b z.1 z.2))
    (f : Fin m → Fin m → X × X → ℝ) (hf : ∀ b c, Continuous (f b c))
    (hinv : ∀ b z, poissonBracket (φ b) (φ a) z.1 z.2 = ∑ c, f b c z * φ c z.1 z.2)
    {x₀ : X × X} (hx₀ : ∀ b, φ b x₀.1 x₀.2 = 0)
    (hφa : ContDiff ℝ 2 (fun z : X × X => φ a z.1 z.2)) :
    ∃ γ : ℝ → X × X, γ 0 = x₀ ∧ ∃ ε > (0 : ℝ),
      (∀ t ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt γ (hamField (φ a) (γ t).1 (γ t).2) t) ∧
        ∀ t ∈ Set.Icc 0 (ε / 2), ∀ b, φ b (γ t).1 (γ t).2 = 0 := by
  obtain ⟨γ, hγ0, ε, hε, hsol⟩ := ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (contDiff_hamField (φ a) hφa).contDiffAt 0
  refine ⟨γ, hγ0, ε, hε, hsol, ?_⟩
  exact surface_invariant φ a hφ f hf hinv γ (T := ε / 2)
    (fun t ht => hsol t ⟨by linarith [ht.1], by linarith [ht.2]⟩) (by simpa [hγ0] using hx₀)

end Lightlike.Gauge
