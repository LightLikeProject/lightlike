import Mathlib
import Lightlike.Dirac.SphereTransition

/-!
# The Kelvin transform of the flat Dirac operator on the plane

The inversion `ι w = w / ‖w‖²` of `ℝ² \ {0}` is an orientation-reversing conformal map.  For a spinor
`ψ : ℝ² → V` on a `Cl₂`-module, the Kelvin transform `K_J ψ (w) = ‖w‖⁻² ρ(w) J ψ (ι w)`, with
`ρ(w) = w₀γ₀ + w₁γ₁` and `J = γ₀γ₁`, satisfies

`D₀ (K_J ψ) = ‖w‖⁻² K_J (D₀ ψ)`  (`dirac_kelvin`).

Without the factor `J` the sign flips (`D₀ (K ψ) = -‖w‖⁻² K (D₀ ψ)`), because `ι` reverses the orientation
and `J` anticommutes with `D₀`.  This is the transition between the two stereographic charts of the
round `S²`, used for the spinor bundle of the sphere (`Lightlike/Dirac/SphereSpectrum.lean`).
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The Kelvin transform `K_J ψ (w) = ‖w‖⁻² ρ(w) J ψ(ι w)`. -/
noncomputable def kelvin (ρ : CliffordRep 2 V) (ψ : E 2 → V) (w : E 2) : V :=
  (‖w‖ ^ 2)⁻¹ • cliffV ρ w (Jop ρ (ψ (inv2 w)))

/-- The derivative of the inversion at `w ≠ 0`:
`v ↦ ‖w‖⁻² v - 2 ⟪w, v⟫ ‖w‖⁻⁴ w`. -/
lemma hasFDerivAt_inv2 {w : E 2} (hw : w ≠ 0) :
    ∃ L : E 2 →L[ℝ] E 2, HasFDerivAt inv2 L w ∧
      ∀ v : E 2, L v = (‖w‖ ^ 2)⁻¹ • v - (2 * inner ℝ w v * ((‖w‖ ^ 2) ^ 2)⁻¹) • w := by
  have h1 : HasFDerivAt (fun x : E 2 => ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 : ‖w‖ ^ 2 ≠ 0 := by positivity
  have h3 := (hasFDerivAt_inv h2).comp w h1
  have h4 := h3.smul (hasFDerivAt_id w)
  refine ⟨_, h4, fun v => ?_⟩
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply, id]
  simp
  module

/-- **Kelvin covariance of the flat Dirac operator on the plane.**  For `w ≠ 0` and `ψ` differentiable at
`ι w`: `D₀ (K_J ψ) (w) = ‖w‖⁻² K_J (D₀ ψ) (w)`. -/
theorem dirac_kelvin (ρ : CliffordRep 2 V) {ψ : E 2 → V} {w : E 2} (hw : w ≠ 0)
    (hψ : DifferentiableAt ℝ ψ (inv2 w)) :
    dirac ρ (kelvin ρ ψ) w = (‖w‖ ^ 2)⁻¹ • kelvin ρ (dirac ρ ψ) w := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_inv2 hw
  have hψ' : HasFDerivAt ψ (fderiv ℝ ψ (inv2 w)) (inv2 w) := hψ.hasFDerivAt
  have hX := (Jop ρ).hasFDerivAt.comp w (hψ'.comp w hL)
  have h0 := (gam ρ 0).hasFDerivAt.comp w hX
  have h1 := (gam ρ 1).hasFDerivAt.comp w hX
  have hc0 := (EuclideanSpace.proj (0 : Fin 2) : E 2 →L[ℝ] ℝ).hasFDerivAt (x := w)
  have hc1 := (EuclideanSpace.proj (1 : Fin 2) : E 2 →L[ℝ] ℝ).hasFDerivAt (x := w)
  have hn : HasFDerivAt (fun x : E 2 => (‖x‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖w‖ ^ 2) ^ 2)⁻¹) : ℝ →L[ℝ] ℝ).comp
        (2 • innerSL ℝ w)) w :=
    (hasFDerivAt_inv (by positivity)).comp w (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hsum := ((hc0.smul h0).add (hc1.smul h1))
  have hall : HasFDerivAt (kelvin ρ ψ) _ w := hn.smul hsum
  have hdiff : ∀ i : Fin 2, fderiv ℝ ψ (inv2 w) (L (e i)) =
      (‖w‖ ^ 2)⁻¹ • fderiv ℝ ψ (inv2 w) (e i) -
        (2 * w i * ((‖w‖ ^ 2) ^ 2)⁻¹) • (w 0 • fderiv ℝ ψ (inv2 w) (e 0) + w 1 • fderiv ℝ ψ (inv2 w) (e 1)) := by
    have hlin : ∀ (φ : E 2 →L[ℝ] V) (u : E 2), φ u = u 0 • φ (e 0) + u 1 • φ (e 1) := by
      intro φ u
      conv_lhs => rw [eq_smul_e_add u]
      rw [map_add, map_smul, map_smul]
    intro i
    rw [hLv, inner_e, map_sub, map_smul, map_smul, hlin (fderiv ℝ ψ (inv2 w)) w]
  simp only [dirac, hall.fderiv, Fin.sum_univ_two]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
  have hp0 : ∀ x : E 2, (EuclideanSpace.proj (0 : Fin 2)) x = x 0 := fun x => rfl
  have hp1 : ∀ x : E 2, (EuclideanSpace.proj (1 : Fin 2)) x = x 1 := fun x => rfl
  have hn2 := norm_sq_E2 w
  simp only [hdiff, hp0, hp1, Function.comp, inner_e, kelvin, cliffV, dirac, Fin.sum_univ_two,
    e00, e01, e10, e11, Jop_apply, map_add, map_sub, map_smul, map_neg, gam_sq ρ 0, gam_sq ρ 1, gam10,
    neg_neg, smul_neg, nsmul_eq_mul, smul_eq_mul]
  generalize fderiv ℝ ψ (inv2 w) (e 0) = a
  generalize fderiv ℝ ψ (inv2 w) (e 1) = b
  generalize ψ (inv2 w) = u
  have hN : w 0 ^ 2 + w 1 ^ 2 ≠ 0 := by rw [← hn2]; positivity
  simp only [hn2]
  match_scalars <;> field_simp <;> ring

end Lightlike.Dirac
