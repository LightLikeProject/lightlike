import Lightlike.Asymptotics.Lorentzian.Vertex
import Lightlike.Asymptotics.Lorentzian.Parity

/-!
# The critical spinors and the maximum of the real part

For a configuration `X` satisfying the z-eliminated critical equations (20), (21) of BDFHP
(arXiv:0907.2440, Sec. 4.2.2; `IsLorCritical`), the spinors `z_e = (X_a†)⁻¹ ξ_ab` (`critZ`) give
`Z_ab = ξ_ab` and `Z_ba = r c J ξ_ba` on every edge (`critZ_src`, `critZ_tgt`), hence the maximum
`Re S = 0` of the real part of the action (`re_lorAction_critZ`; eqs. (18)–(19) through
`triWeight_eq_one_iff`).

First step towards the critical points of the action in a chart (step 4a of the plan): the
vanishing of the gradient (stationarity in `z` and in `X`, that is, closure of the normals and the
second critical equation) is not proved here.
-/

open Complex
open scoped ComplexConjugate Matrix
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian


/-- The spinors of the critical configuration: `z_e = (X_a†)⁻¹ ξ_ab`, so that `Z_ab = X_a† z_e = ξ_ab`. -/
noncomputable def critZ (g : BdryData) (X : Fin 5 → SL2C) : Fin 10 → Spinor := fun e =>
  spinAct (parityMap (X (edgeSrc e)) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0))

/-- `X† · (X†)⁻¹ = 1`. -/
theorem conjTranspose_mul_parityMap (X : SL2C) :
    (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (parityMap X : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  have hu : IsUnit ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).det := by
    have hd : (X : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := X.2
    rw [Matrix.det_conjTranspose, hd]
    simp
  rw [coe_parityMap]
  exact Matrix.mul_nonsing_inv _ hu

/-- `Z_ab = X_a† z_e = ξ_ab` at the critical spinors. -/
theorem critZ_src (g : BdryData) (X : Fin 5 → SL2C) (e : Fin 10) :
    spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e) = firstCol (g e 0) := by
  unfold critZ
  rw [← spinAct_mul, conjTranspose_mul_parityMap, spinAct_one]

/-- `Z_ba = X_b† z_e = r c J ξ_ba` when equation (20) of `IsLorCritical` holds on the edge. -/
theorem critZ_tgt (g : BdryData) (X : Fin 5 → SL2C) (e : Fin 10) (r : ℝ) (c : ℂ)
    (h20 : spinAct (parityMap (X (edgeSrc e)) : Matrix (Fin 2) (Fin 2) ℂ) (firstCol (g e 0)) =
        ((r : ℂ) * c) • spinAct (parityMap (X (edgeTgt e)) : Matrix (Fin 2) (Fin 2) ℂ)
          (jMap (firstCol (g e 1)))) :
    spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e) =
      ((r : ℂ) * c) • jMap (firstCol (g e 1)) := by
  unfold critZ
  rw [h20, spinAct_smul, ← spinAct_mul, conjTranspose_mul_parityMap, spinAct_one]

/-- **A configuration satisfying (20), (21) with the critical spinors has `Re S = 0`** (BDFHP
eqs. (18)–(20)): on every edge `Z = ξ` and `Z' = r c J ξ'`, so the weight `|e^{S_e}| = triWeight`
is `1` (`triWeight_eq_one_iff`), for positive spin parameters and unit boundary spinors. -/
theorem re_lorAction_critZ {j p : Fin 10 → ℝ} (hj : ∀ e, 0 < j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    {X : Fin 5 → SL2C} (h : IsLorCritical g X) :
    (lorAction j p g X (critZ g X)).re = 0 := by
  unfold lorAction
  rw [Complex.re_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  obtain ⟨r, hr, c, hc, h20, -⟩ := h e
  have hZ : spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e) ≠ 0 := by
    rw [critZ_src]; intro h0; have := hξ e; rw [h0] at this; simp at this
  have hrc : ((r : ℂ) * c) ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') (fun h0 => by
    rw [h0] at hc; simp at hc)
  have hjξ : jMap (firstCol (g e 1)) ≠ 0 := jMap_ne_zero (fun h0 => by
    have := hξ' e; rw [h0] at this; simp at this)
  have hZ' : spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e) ≠ 0 := by
    rw [critZ_tgt g X e r c h20]
    exact smul_ne_zero hrc hjξ
  have hw : triWeight (j e)
      (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e)) (firstCol (g e 0))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e)) (firstCol (g e 1)) = 1 := by
    refine (triWeight_eq_one_iff (hj e) hZ hZ' (hξ e) (hξ' e)).mpr ⟨⟨1, one_ne_zero, ?_⟩, ⟨_, hrc, ?_⟩⟩
    · rw [critZ_src]; simp
    · exact critZ_tgt g X e r c h20
  have h1 : inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e))
      (firstCol (g e 0)) ≠ 0 := by
    rw [critZ_src, inner_self_eq_norm_sq_to_K, hξ e]; simp
  have h2 : inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (critZ g X e)) ≠ 0 := by
    rw [critZ_tgt g X e r c h20, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_jMap, hξ' e]
    simpa using hrc
  have hn := norm_exp_triAction (k := j e) (p := p e) hZ hZ' h1 h2
  rw [hw, Complex.norm_exp] at hn
  exact Real.exp_eq_one_iff _ |>.mp hn

end Lightlike.Asymptotics.Lorentzian
