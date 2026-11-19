import Lightlike.ODE.FlowAlong
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The variational equation for a smooth flow

If `(t, y) ↦ Φ t y` is `C²` near a point and each `t ↦ Φ t y` solves `ẋ = V x` there, the
derivative of the flow in the initial point solves the first variational equation
`d/dt D_y Φ_t ζ = DV (Φ t y) (D_y Φ_t ζ)` (`Lightlike.ODE.hasDerivAt_fderiv_flow_of_contDiffOn`).
For flow boxes this is `IsFlowBox.hasDerivAt_fderiv_flow`; here it is derived from the regularity
of the flow, by the symmetry of second derivatives, so that it applies to the flow along a whole
trajectory (`exists_flow_along`).

## References

* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, equations
  (2.46)–(2.49), pages 45–46 of the author's version, where the variational equation is derived
  by interchanging the derivatives.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The first variational equation for a smooth flow.** Let `(t, y) ↦ Φ t y` be smooth on an
open set `S` of `ℝ × E`, with `t ↦ Φ t y` a solution of `ẋ = V x` at every point of `S`, and let
`V` be differentiable at `Φ t y`. Then for `(t, y) ∈ S` and every `ζ`,
`τ ↦ D_y Φ_τ ζ` has derivative `DV (Φ t y) (D_y Φ_t ζ)` at `t`. -/
theorem hasDerivAt_fderiv_flow_of_contDiffOn {V : E → E} {Φ : ℝ → E → E} {S : Set (ℝ × E)}
    (hS : IsOpen S) (hΦ : ContDiffOn ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) S)
    (hsol : ∀ q ∈ S, HasDerivAt (fun τ => Φ τ q.2) (V (Φ q.1 q.2)) q.1) {t : ℝ} {y : E}
    (hty : (t, y) ∈ S) (hV : DifferentiableAt ℝ V (Φ t y)) (ζ : E) :
    HasDerivAt (fun τ => fderiv ℝ (Φ τ) y ζ) (fderiv ℝ V (Φ t y) (fderiv ℝ (Φ t) y ζ)) t := by
  set Ft : ℝ × E → E := fun p => Φ p.1 p.2 with hFt
  set D : ℝ × E → (ℝ × E →L[ℝ] E) := fderiv ℝ Ft with hD
  have hat : ∀ q ∈ S, ContDiffAt ℝ ∞ Ft q := fun q hq => hΦ.contDiffAt (hS.mem_nhds hq)
  have hFd : ∀ q ∈ S, HasFDerivAt Ft (D q) q := fun q hq =>
    ((hat q hq).differentiableAt (by simp)).hasFDerivAt
  have hDd : HasFDerivAt D (fderiv ℝ D (t, y)) (t, y) :=
    (((hat _ hty).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  -- the derivative in the initial point through `D`
  have hslice : ∀ τ : ℝ, (τ, y) ∈ S → fderiv ℝ (Φ τ) y ζ = D (τ, y) ((0 : ℝ), ζ) := by
    intro τ hτ
    have h1 : HasFDerivAt (fun y' : E => ((τ, y') : ℝ × E))
        (ContinuousLinearMap.inr ℝ ℝ E) y := hasFDerivAt_prodMk_right τ y
    have h2 : HasFDerivAt (Ft ∘ fun y' : E => ((τ, y') : ℝ × E))
        ((D (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y := (hFd _ hτ).comp y h1
    have h3 : fderiv ℝ (Φ τ) y = (D (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) := h2.fderiv
    rw [h3]; rfl
  have hcurve : HasDerivAt (fun τ : ℝ => ((τ, y) : ℝ × E)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hSt : ∀ᶠ τ in 𝓝 t, ((τ, y) : ℝ × E) ∈ S :=
    (hcurve.continuousAt).eventually (hS.mem_nhds hty)
  have hev : (fun τ => fderiv ℝ (Φ τ) y ζ) =ᶠ[𝓝 t] fun τ => D (τ, y) ((0 : ℝ), ζ) := by
    filter_upwards [hSt] with τ hτ using hslice τ hτ
  have h2 : HasDerivAt (fun τ => D (τ, y) ((0 : ℝ), ζ))
      (fderiv ℝ D (t, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), ζ)) t := by
    have h3 : HasDerivAt (fun τ : ℝ => D (τ, y)) (fderiv ℝ D (t, y) ((1 : ℝ), (0 : E))) t :=
      hDd.comp_hasDerivAt t hcurve
    have h4 := h3.clm_apply (hasDerivAt_const t (((0 : ℝ), ζ) : ℝ × E))
    simpa using h4
  -- symmetry of the second derivative
  have hsymm : fderiv ℝ D (t, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), ζ) =
      fderiv ℝ D (t, y) ((0 : ℝ), ζ) ((1 : ℝ), (0 : E)) :=
    ((hat _ hty).isSymmSndFDerivAt (by simp)).eq _ _
  -- the time derivative of the flow is `V ∘ Φ`
  have htime : ∀ q ∈ S, D q ((1 : ℝ), (0 : E)) = V (Ft q) := by
    intro q hq
    have h5 : HasDerivAt (fun τ : ℝ => ((τ, q.2) : ℝ × E)) ((1 : ℝ), (0 : E)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    have h6 : HasDerivAt (Ft ∘ fun τ : ℝ => ((τ, q.2) : ℝ × E)) (D q ((1 : ℝ), (0 : E))) q.1 :=
      (hFd q hq).comp_hasDerivAt q.1 h5
    exact h6.unique (hsol q hq)
  have hev2 : (fun q => D q ((1 : ℝ), (0 : E))) =ᶠ[𝓝 ((t, y) : ℝ × E)] fun q => V (Ft q) := by
    filter_upwards [hS.mem_nhds hty] with q hq using htime q hq
  have h7 : HasFDerivAt (fun q => D q ((1 : ℝ), (0 : E)))
      ((fderiv ℝ D (t, y)).flip ((1 : ℝ), (0 : E))) (t, y) := by
    have := hDd.clm_apply (hasFDerivAt_const (((1 : ℝ), (0 : E)) : ℝ × E) ((t, y) : ℝ × E))
    simpa using this
  have h8 : HasFDerivAt (fun q => V (Ft q)) ((fderiv ℝ V (Φ t y)).comp (D (t, y))) (t, y) :=
    HasFDerivAt.comp (t, y) (g := V) hV.hasFDerivAt (hFd _ hty)
  have h9 := (h8.congr_of_eventuallyEq hev2).unique h7
  have h10 : fderiv ℝ D (t, y) ((0 : ℝ), ζ) ((1 : ℝ), (0 : E)) =
      fderiv ℝ V (Φ t y) (D (t, y) ((0 : ℝ), ζ)) := by
    have := congrArg (fun L : ℝ × E →L[ℝ] E => L ((0 : ℝ), ζ)) h9
    simpa using this.symm
  rw [hslice t hty, ← h10, ← hsymm]
  exact h2.congr_of_eventuallyEq hev

end Lightlike.ODE
