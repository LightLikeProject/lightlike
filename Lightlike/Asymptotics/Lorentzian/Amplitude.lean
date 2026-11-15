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

/-- The spinor `(1, w)` is nonzero. -/
theorem lorSpinor_ne_zero (w : ℂ) : lorSpinor w ≠ 0 := by
  intro h
  have := congrArg (fun v : Spinor => v 0) h
  simp [lorSpinor] at this

/-- The adjoint of an element of `SL(2, ℂ)` acts injectively on spinors: it has determinant `1`. -/
theorem spinAct_conjTranspose_ne_zero (X : SL2C) {v : Spinor} (hv : v ≠ 0) :
    spinAct (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v ≠ 0 := by
  intro h
  apply hv
  have hdet : ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose, X.2, star_one]
  have h1 : (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have h2 := congrArg (spinAct ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate)) h
  rw [← spinAct_mul, h1, spinAct_one] at h2
  rw [h2]
  ext i; fin_cases i <;> simp [spinAct]

/-- **The integrand is bounded by the density of `Ω`** where no overlap vanishes:
`‖e^S Π_e ρ_e‖ ≤ Π_e ρ_e`, because `Re S ≤ 0` (`re_lorAction_le_zero`). The spinors `X† (1, w)`
never vanish, and the overlaps vanish on a null set only, so the hypotheses `h1`, `h2` are the
only ones left. -/
theorem norm_lorIntegrand_le {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    {X : Fin 5 → SL2C} {w : Fin 10 → ℂ}
    (h1 : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (w e)))
      (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ e, inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor (w e))) ≠ 0) :
    ‖lorIntegrand j p g X w‖ ≤ ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e := by
  unfold lorIntegrand
  rw [norm_mul, Complex.norm_exp]
  have hS := re_lorAction_le_zero hj (p := p) (X := X) (z := fun e => lorSpinor (w e))
    (fun e => spinAct_conjTranspose_ne_zero _ (lorSpinor_ne_zero _))
    (fun e => spinAct_conjTranspose_ne_zero _ (lorSpinor_ne_zero _)) hξ hξ' h1 h2
  have hexp : Real.exp (lorAction j p g X fun e => lorSpinor (w e)).re ≤ 1 :=
    Real.exp_le_one_iff.mpr hS
  have hprod : ‖∏ e, ((lorEdgeDensity X (fun e => lorSpinor (w e)) e : ℝ) : ℂ)‖ =
      ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    unfold lorEdgeDensity
    positivity
  rw [hprod]
  calc _ ≤ 1 * ∏ e, lorEdgeDensity X (fun e => lorSpinor (w e)) e :=
        mul_le_mul_of_nonneg_right hexp (Finset.prod_nonneg fun e _ => by
          unfold lorEdgeDensity; positivity)
    _ = _ := one_mul _

/-- `‖M v‖² ≤ (Σ_{ij} |M_{ij}|²) ‖v‖²` for the action of a `2 × 2` matrix on a spinor. -/
theorem norm_spinAct_sq_le (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Spinor) :
    ‖spinAct M v‖ ^ 2 ≤ (‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * ‖v‖ ^ 2 := by
  have e : ∀ u : Spinor, ‖u‖ ^ 2 = ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 := fun u => by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
  rw [e, e]
  simp only [spinAct_zero_apply, spinAct_one_apply]
  have h0 : ‖M 0 0 * v 0 + M 0 1 * v 1‖ ≤ ‖M 0 0‖ * ‖v 0‖ + ‖M 0 1‖ * ‖v 1‖ :=
    (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have h1 : ‖M 1 0 * v 0 + M 1 1 * v 1‖ ≤ ‖M 1 0‖ * ‖v 0‖ + ‖M 1 1‖ * ‖v 1‖ :=
    (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
  have a0 := norm_nonneg (M 0 0); have a1 := norm_nonneg (M 0 1)
  have a2 := norm_nonneg (M 1 0); have a3 := norm_nonneg (M 1 1)
  have b0 := norm_nonneg (v 0); have b1 := norm_nonneg (v 1)
  have c0 := norm_nonneg (M 0 0 * v 0 + M 0 1 * v 1)
  have c1 := norm_nonneg (M 1 0 * v 0 + M 1 1 * v 1)
  have s0 : ‖M 0 0 * v 0 + M 0 1 * v 1‖ ^ 2 ≤ (‖M 0 0‖ * ‖v 0‖ + ‖M 0 1‖ * ‖v 1‖) ^ 2 :=
    pow_le_pow_left₀ c0 h0 2
  have s1 : ‖M 1 0 * v 0 + M 1 1 * v 1‖ ^ 2 ≤ (‖M 1 0‖ * ‖v 0‖ + ‖M 1 1‖ * ‖v 1‖) ^ 2 :=
    pow_le_pow_left₀ c1 h1 2
  nlinarith [sq_nonneg (‖M 0 0‖ * ‖v 1‖ - ‖M 0 1‖ * ‖v 0‖),
    sq_nonneg (‖M 1 0‖ * ‖v 1‖ - ‖M 1 1‖ * ‖v 0‖)]


/-- **`X†` is bounded below on spinors**: `‖v‖² ≤ C ‖X† v‖²` with `C` the sum of the squared
moduli of the entries of the adjugate of `X†` (its inverse). -/
theorem norm_sq_le_spinAct_conjTranspose (X : SL2C) (v : Spinor) :
    ‖v‖ ^ 2 ≤ (‖((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 0‖ ^ 2 +
      ‖((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 1‖ ^ 2 +
      ‖((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 0‖ ^ 2 +
      ‖((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 1‖ ^ 2) *
      ‖spinAct (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v‖ ^ 2 := by
  have hdet : ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose, X.2, star_one]
  have h1 : (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate * (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 1 := by
    rw [Matrix.adjugate_mul, hdet, one_smul]
  have := norm_spinAct_sq_le ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate)
    (spinAct (X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ v)
  rwa [← spinAct_mul, h1, spinAct_one] at this

/-- The density of `Ω_e` is continuous in `w`, since the spinors `X† (1, w)` never vanish. -/
theorem continuous_lorEdgeDensity_aux (A B : SL2C) :
    Continuous fun w : ℂ => (‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
      ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ := by
  refine Continuous.inv₀ ?_ fun w => ?_
  · exact ((continuous_spinAct.comp (continuous_const.prodMk continuous_lorSpinor)).norm.pow 2).mul
      ((continuous_spinAct.comp (continuous_const.prodMk continuous_lorSpinor)).norm.pow 2)
  · exact mul_ne_zero
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (spinAct_conjTranspose_ne_zero A (lorSpinor_ne_zero w))))
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (spinAct_conjTranspose_ne_zero B (lorSpinor_ne_zero w))))


/-- `‖(1, w)‖² = 1 + ‖w‖²`. -/
theorem norm_lorSpinor_sq (w : ℂ) : ‖lorSpinor w‖ ^ 2 = 1 + ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [lorSpinor, Fin.sum_univ_two]

/-- **The density of `Ω_e` is integrable on the chart `ℂ`** (BDFHP §4): it is continuous and
`O(|w|⁻⁴)`, because `X†` is bounded below on spinors. At `A = B = 1` it is the Fubini–Study density
`lorEdgeDensity_one`. -/
theorem integrable_lorEdgeDensity (A B : SL2C) :
    Integrable fun w : ℂ => (‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
      ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ := by
  set CA := ‖((A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 0‖ ^ 2 +
      ‖((A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 1‖ ^ 2 +
      ‖((A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 0‖ ^ 2 +
      ‖((A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 1‖ ^ 2 with hCA
  set CB := ‖((B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 0‖ ^ 2 +
      ‖((B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 0 1‖ ^ 2 +
      ‖((B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 0‖ ^ 2 +
      ‖((B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ.adjugate) 1 1‖ ^ 2 with hCB
  have hg : Integrable fun w : ℂ => (CA * CB * 4) * (1 + ‖w‖) ^ (-(4 : ℝ)) :=
    (integrable_one_add_norm (E := ℂ) (μ := volume) (r := 4) (by
      simp only [Complex.finrank_real_complex]; norm_num)).const_mul _
  refine hg.mono' (continuous_lorEdgeDensity_aux A B).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  have hn : 0 < ‖lorSpinor w‖ ^ 2 := by
    have := norm_pos_iff.mpr (lorSpinor_ne_zero w); positivity
  have hA := norm_sq_le_spinAct_conjTranspose A (lorSpinor w)
  have hB := norm_sq_le_spinAct_conjTranspose B (lorSpinor w)
  set a := ‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2
  set b := ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2
  set n := ‖lorSpinor w‖ ^ 2 with hn_def
  have ha : 0 < a := by
    have := (spinAct_conjTranspose_ne_zero A (lorSpinor_ne_zero w)); positivity
  have hb : 0 < b := by
    have := (spinAct_conjTranspose_ne_zero B (lorSpinor_ne_zero w)); positivity
  have hprod : n * n ≤ (CA * CB) * (a * b) := by
    calc n * n ≤ (CA * a) * (CB * b) := mul_le_mul hA hB hn.le (by
            have : 0 ≤ CA := by positivity
            positivity)
      _ = _ := by ring
  have h1w : 0 < 1 + ‖w‖ := by positivity
  have hq : (1 + ‖w‖) ^ 2 ≤ 2 * n := by
    rw [hn_def, norm_lorSpinor_sq]; nlinarith [sq_nonneg (1 - ‖w‖), norm_nonneg w]
  have hq4 : (1 + ‖w‖) ^ 4 ≤ 4 * (n * n) := by
    have : ((1 + ‖w‖) ^ 2) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
    nlinarith
  rw [norm_inv, Real.norm_eq_abs, abs_of_pos (mul_pos ha hb), Real.rpow_neg h1w.le,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hrhs : CA * CB * ((4 : ℕ) : ℝ) * ((1 + ‖w‖) ^ 4)⁻¹ = (CA * CB * 4) / (1 + ‖w‖) ^ 4 := by
    push_cast; ring
  rw [hrhs, inv_eq_one_div, div_le_div_iff₀ (mul_pos ha hb) (by positivity)]
  have hCpos : 0 ≤ CA * CB := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq4 hCpos, hprod]

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
