import Lightlike.Asymptotics.Lorentzian.Vertex
import Lightlike.Lorentz.StarBound

/-!
# The gauge-fixed Lorentzian vertex amplitude

BDFHP, eq. before (17) (Barrett, Dowdall, Fairbairn, Hellmann, Pereira, arXiv:0907.2440, §4):
`f₄ = (-1)^χ ∫_{SL(2,ℂ)^5} δ(X₅) ∏_a dX_a ∫_{(ℂP¹)^10} e^{S} ∏_{a<b} c_{ab} dk_{ab} Ω_{ab}`,
`Ω_{ab} = Ω / (⟨Z_{ab}, Z_{ab}⟩ ⟨Z_{ba}, Z_{ba}⟩)`, `Z_{ab} = X_a† z_{ab}`, `Z_{ba} = X_b† z_{ab}`.
This file writes the integrand and the amplitude, with the integration over `SL(2,ℂ)^4` (the
fifth element fixed to `1`, since the integral over all five copies diverges) and over the chart
`z = (1, w)`, `w ∈ ℂ`, of each `ℂP¹`, where `Ω` is Lebesgue measure `dw`.

What is **not** here, so that nothing reads stronger than it is: (i) the finiteness of the
integral (that of the principal-series form of the same amplitude is
`Lightlike.Lorentz.integrable_eprlIntegrand`, after Engle and Pereira 2009, Section 4; the
equality of that form with this one is not proved), (ii) the constants `c_{ab} dk_{ab}`, the
normalisation of `Ω` and the sign `(-1)^χ`, which `lorVertex` takes as the parameters `c_e` and
omits, and (iii) the spinors with `z_0 = 0`, a null set missed by the chart. The logarithms of the
action take junk values only where a spinor or an overlap vanishes, a null set.
-/

open MeasureTheory Complex Matrix
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

theorem continuous_spinAct :
    Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => spinAct p.1 p.2 := by
  unfold spinAct
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp (continuous_pi fun i => ?_)
  have h00 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.1 0 0 := by fun_prop
  have h01 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.1 0 1 := by fun_prop
  have h10 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.1 1 0 := by fun_prop
  have h11 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.1 1 1 := by fun_prop
  have v0 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.2 0 := by fun_prop
  have v1 : Continuous fun p : Matrix (Fin 2) (Fin 2) ℂ × Spinor => p.2 1 := by fun_prop
  fin_cases i
  · exact (h00.mul v0).add (h01.mul v1)
  · exact (h10.mul v0).add (h11.mul v1)

/-- The spinor `(1, w)` of the chart `w ↦ [1 : w]` of `ℂP¹`. -/
def lorSpinor (w : ℂ) : Spinor := !₂[1, w]

theorem continuous_lorSpinor : Continuous lorSpinor := by
  unfold lorSpinor
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_const
  · exact continuous_id

/-- The density `1 / (⟨Z_{ab}, Z_{ab}⟩ ⟨Z_{ba}, Z_{ba}⟩)` of `Ω_{ab}` (BDFHP §4) on the triangle `e`,
with `Z_{ab} = X_a† z_e` and `Z_{ba} = X_b† z_e`. -/
noncomputable def lorEdgeDensity (X : Fin 5 → SL2C) (z : Fin 10 → Spinor) (e : Fin 10) : ℝ :=
  (‖spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)‖ ^ 2 *
    ‖spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)‖ ^ 2)⁻¹

/-- **The integrand of the Lorentzian vertex** in the chart `z_e = (1, w_e)` of each `ℂP¹`:
`e^{S[X, z]} ∏_e 1 / (⟨Z_{ab}, Z_{ab}⟩ ⟨Z_{ba}, Z_{ba}⟩)`, with `S = lorAction`. -/
noncomputable def lorIntegrand (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C)
    (w : Fin 10 → ℂ) : ℂ :=
  cexp (lorAction j p g X fun e => lorSpinor (w e)) *
    ∏ e, ((lorEdgeDensity X (fun e => lorSpinor (w e)) e : ℝ) : ℂ)

/-- **The gauge-fixed Lorentzian vertex amplitude** (BDFHP §4):
`(∏_e c_e) ∫_{SL(2,ℂ)^4} ∫_{ℂ^10} e^{S} ∏_e Ω_e`, with `X₄ = 1` and the Haar measure on each
`SL(2,ℂ)`. The constants `c_e` stand for `c_{ab} dk_{ab}` and the normalisation of `Ω`; the sign
`(-1)^χ` is not included. Finiteness is a separate statement. -/
noncomputable def lorVertex (j p : Fin 10 → ℝ) (c : Fin 10 → ℂ) (g : BdryData) : ℂ :=
  (∏ e, c e) * ∫ x : Fin 4 → SL2C, ∫ w : Fin 10 → ℂ,
    lorIntegrand j p g (Lightlike.Lorentz.gauge x) w ∂volume
      ∂(Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.SL2C.haar)


/-- The gauge-fixed vertex variables are continuous in `x`. -/
theorem continuous_gauge_apply' (a : Fin 5) :
    Continuous fun x : Fin 4 → SL2C => Lightlike.Lorentz.gauge x a := by
  induction a using Fin.lastCases with
  | last => simp only [Lightlike.Lorentz.gauge_last]; exact continuous_const
  | cast i => simp only [Lightlike.Lorentz.gauge_castSucc]; exact continuous_apply i

/-- The spinor `Z = X_a† z` at the node `a`, for the chart point `w`, is continuous in
`(x, w)`. -/
theorem continuous_nodeSpinor (a : Fin 5) (e : Fin 10) :
    Continuous fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      spinAct (Lightlike.Lorentz.gauge q.1 a : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (q.2 e)) := by
  have hX : Continuous fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      ((Lightlike.Lorentz.gauge q.1 a : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
    (continuous_subtype_val.comp ((continuous_gauge_apply' a).comp continuous_fst)).matrix_conjTranspose
  have hz : Continuous fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) => lorSpinor (q.2 e) :=
    continuous_lorSpinor.comp ((continuous_apply e).comp continuous_snd)
  exact continuous_spinAct.comp (hX.prodMk hz)


section Measurability

variable {Q : Type*} [TopologicalSpace Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]

/-- The one-triangle action is measurable in continuous spinor arguments. -/
theorem measurable_triAction (k p : ℝ) {Z Z' : Q → Spinor} (hZ : Continuous Z)
    (hZ' : Continuous Z') (ξ ξ' : Spinor) :
    Measurable fun q => triAction k p (Z q) ξ (Z' q) ξ' := by
  have n1 : Continuous fun q => (inner ℂ (Z q) ξ) ^ 2 * (inner ℂ (jMap ξ') (Z' q)) ^ 2 :=
    ((hZ.inner continuous_const).pow 2).mul ((continuous_const.inner hZ').pow 2)
  have d1 : Continuous fun q => ((‖Z q‖ ^ 2 : ℝ) : ℂ) * ((‖Z' q‖ ^ 2 : ℝ) : ℂ) :=
    (Complex.continuous_ofReal.comp (hZ.norm.pow 2)).mul
      (Complex.continuous_ofReal.comp (hZ'.norm.pow 2))
  unfold triAction
  refine Measurable.add ?_ ?_
  · exact (Complex.measurable_log.comp (n1.measurable.div d1.measurable)).const_mul _
  · exact (Complex.measurable_log.comp
      ((Complex.continuous_ofReal.comp (hZ'.norm.pow 2)).measurable.div
        (Complex.continuous_ofReal.comp (hZ.norm.pow 2)).measurable)).const_mul _

end Measurability


/-- **The integrand is measurable** on `SL(2,ℂ)^4 × ℂ^10`, so the amplitude is an iterated integral
of a measurable function (the logarithms in the action take junk values only where a spinor or an
overlap vanishes, a null set). -/
theorem measurable_lorIntegrand (j p : Fin 10 → ℝ) (g : BdryData) :
    Measurable fun q : (Fin 4 → SL2C) × (Fin 10 → ℂ) =>
      lorIntegrand j p g (Lightlike.Lorentz.gauge q.1) q.2 := by
  unfold lorIntegrand lorAction lorEdgeDensity
  refine (Complex.measurable_exp.comp (Finset.measurable_sum _ fun e _ => ?_)).mul
    (Finset.measurable_prod _ fun e _ => ?_)
  · exact measurable_triAction _ _ (continuous_nodeSpinor _ e) (continuous_nodeSpinor _ e) _ _
  · refine Complex.measurable_ofReal.comp (Measurable.inv (Measurable.mul ?_ ?_))
    · exact ((continuous_nodeSpinor (edgeSrc e) e).norm.pow 2).measurable
    · exact ((continuous_nodeSpinor (edgeTgt e) e).norm.pow 2).measurable

/-! ### Trust check -/

/-- **Known value**: at `X = 1` the density of `Ω_e` on the chart `z = (1, w)` is the
Fubini–Study density `(1 + |w|²)⁻²` of `ℂP¹`. -/
theorem lorEdgeDensity_one (w : Fin 10 → ℂ) (e : Fin 10) :
    lorEdgeDensity (fun _ => 1) (fun e => lorSpinor (w e)) e = (1 + ‖w e‖ ^ 2)⁻¹ ^ 2 := by
  have h : ‖lorSpinor (w e)‖ ^ 2 = 1 + ‖w e‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [lorSpinor, Fin.sum_univ_two]
  unfold lorEdgeDensity
  have h1 : ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Matrix.SpecialLinearGroup.coe_one
  simp only [h1, conjTranspose_one, spinAct_one, h]
  rw [sq (_ : ℝ)⁻¹, mul_inv]

end Lightlike.Asymptotics.Lorentzian
