import Lightlike.Poincare.IrreducibleMassless
import Lightlike.Poincare.ShellSourceMeasure

/-!
# The measure `d³p / (2|p|)` on the light cone is Lorentz invariant

The light-cone coordinates `(w, t) ∈ ℂ × ℝ` of the forward light cone, `P = [[|w|² e^{-t}, w], [w̄, e^t]]`
(`lcInvC`, the projection onto `v = (w e^{-t/2}, e^{t/2})`), cover the cone outside the null half-line `P₁₁ = 0`.
Upper triangular matrices act on them exactly as on the mass shell (`upperF`), and the Weyl element as `weylF 0`
off the null set `w = 0`; both preserve the Lebesgue measure, so its image `lcMeasureC` is invariant
(`measurePreserving_lcMeasureC`). The source's measure `δ(p²) Θ(p⁰) d⁴p`, which is `d³p / (2|p|)` in the chart
`p ↦ (|p|, p)` (`coneSourceMeasure`), is half of `lcMeasureC` (`coneSourceMeasure_eq`), hence invariant, and the
massless one-particle representations on `L²(d³p / 2|p|)` are irreducible (`irreducible_massless_coneSourceMeasure`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2, Remarks (page 11 of v2): the invariant scalar product
  `∫ dᴰp δ(p² + m²) Θ(p⁰) Σ_σ Ψ*_{p,σ} Φ_{p,σ}` for `p² ≤ 0`, here with `m = 0`.
* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §6, Theorem 6.2, page 149.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace Lightlike.Poincare

noncomputable section

/-! ## Light-cone coordinates of the cone -/

/-- The vector `(w e^{-t/2}, e^{t/2})`. -/
def lcVecC (z : ℂ × ℝ) : Fin 2 → ℂ := ![z.1 * (Real.exp (-z.2 / 2) : ℂ), (Real.exp (z.2 / 2) : ℂ)]

lemma lcVecC_ne (z : ℂ × ℝ) : lcVecC z ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [lcVecC, Real.exp_ne_zero] at this

/-- The point of the cone with light-cone coordinates `(w, t)`. -/
def lcInvC (z : ℂ × ℝ) : LightCone := ⟨proj (lcVecC z), proj_mem_lightCone (lcVecC_ne z)⟩

lemma continuous_lcInvC : Continuous lcInvC := by
  apply continuous_induced_rng.2
  change Continuous fun z : ℂ × ℝ => proj (lcVecC z)
  refine continuous_proj.comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact continuous_fst.mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_snd.neg.div_const 2)))
  · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_snd.div_const 2))

lemma lcInvC_apply (z : ℂ × ℝ) : ((lcInvC z : LightCone) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![((‖z.1‖ ^ 2 * Real.exp (-z.2) : ℝ) : ℂ), z.1; conj z.1, (Real.exp z.2 : ℂ)] := by
  have h1 : Real.exp (-z.2 / 2) * Real.exp (-z.2 / 2) = Real.exp (-z.2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-z.2 / 2) * Real.exp (z.2 / 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h3 : Real.exp (z.2 / 2) * Real.exp (z.2 / 2) = Real.exp z.2 := by
    rw [← Real.exp_add]; ring_nf
  have hn : (‖z.1‖ ^ 2 : ℂ) = z.1 * conj z.1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  change proj (lcVecC z) = _
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [proj, lcVecC, Matrix.vecMulVec_apply, Pi.star_apply, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, RCLike.star_def, map_mul,
      Complex.conj_ofReal]
    rw [← h1]
    push_cast
    rw [hn]
    ring
  · simp only [proj, lcVecC, Matrix.vecMulVec_apply, Pi.star_apply, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.star_def, Complex.conj_ofReal, Fin.mk_one, Matrix.head_cons]
    rw [mul_assoc, ← Complex.ofReal_mul, h2, Complex.ofReal_one, mul_one]
  · simp only [proj, lcVecC, Matrix.vecMulVec_apply, Pi.star_apply, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.star_def, map_mul, Complex.conj_ofReal, Fin.mk_one, Matrix.head_cons]
    rw [mul_comm (conj z.1), ← mul_assoc, ← Complex.ofReal_mul, mul_comm (Real.exp _), h2, Complex.ofReal_one,
      one_mul]
  · simp only [proj, lcVecC, Matrix.vecMulVec_apply, Pi.star_apply, Fin.mk_one, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, h3]

lemma lcInvC_01 (z : ℂ × ℝ) : ((lcInvC z : LightCone) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = z.1 := by
  rw [lcInvC_apply]; simp

lemma lcInvC_11 (z : ℂ × ℝ) : ((lcInvC z : LightCone) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = Real.exp z.2 := by
  rw [lcInvC_apply]; simp

/-- A point of the cone with `P₁₁ ≠ 0` is determined by `P₀₁` and `P₁₁`. -/
lemma cone_ext {P Q : LightCone} (h01 : P.1 0 1 = Q.1 0 1) (h11 : P.1 1 1 = Q.1 1 1) (hQ : Q.1 1 1 ≠ 0) :
    P = Q := by
  have hPh := P.2.1.isHermitian
  have hQh := Q.2.1.isHermitian
  have h10 : P.1 1 0 = Q.1 1 0 := by rw [← hPh.apply 1 0, ← hQh.apply 1 0, h01]
  have hdP := P.2.2.1
  have hdQ := Q.2.2.1
  rw [Matrix.det_fin_two] at hdP hdQ
  rw [h01, h10, h11] at hdP
  have h00 : P.1 0 0 = Q.1 0 0 := by
    have : P.1 0 0 * Q.1 1 1 = Q.1 0 0 * Q.1 1 1 := by linear_combination hdP - hdQ
    exact mul_right_cancel₀ hQ this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ## Invariance -/

lemma smul_upper_lcInvC (a b : ℂ) (ha : a ≠ 0) (z : ℂ × ℝ) :
    upperSL a b ha • lcInvC z = lcInvC (upperF a b z) := by
  have hca : conj a ≠ 0 := by simpa using ha
  apply cone_ext
  · rw [lcInvC_01, coe_smul_lightCone, actP, lcInvC_apply]
    simp [upperSL, upperF, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · rw [lcInvC_11, coe_smul_lightCone, actP, lcInvC_apply]
    have hn : (0 : ℝ) < ‖a‖ := norm_pos_iff.2 ha
    have e : Real.exp (z.2 - 2 * Real.log ‖a‖) = Real.exp z.2 / ‖a‖ ^ 2 := by
      rw [Real.exp_sub, show 2 * Real.log ‖a‖ = Real.log (‖a‖ ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    simp only [upperF, e]
    simp [upperSL, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  · rw [lcInvC_11]; exact Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

lemma smul_weyl_lcInvC {z : ℂ × ℝ} (hz : z.1 ≠ 0) : weylSL • lcInvC z = lcInvC (weylF 0 z) := by
  apply cone_ext
  · rw [lcInvC_01, coe_smul_lightCone, actP, lcInvC_apply]
    simp [weylSL, weylF, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [lcInvC_11, coe_smul_lightCone, actP, lcInvC_apply]
    have hpos : 0 < ‖z.1‖ ^ 2 := by have := norm_pos_iff.2 hz; positivity
    have e : Real.exp (Real.log ((0 : ℝ) ^ 2 + ‖z.1‖ ^ 2) - z.2) = ‖z.1‖ ^ 2 * Real.exp (-z.2) := by
      rw [Real.exp_sub, zero_pow two_ne_zero, zero_add, Real.exp_log hpos, Real.exp_neg, div_eq_mul_inv]
    simp only [weylF, e]
    simp [weylSL, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [lcInvC_11]; exact Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

/-- The image of the Lebesgue measure of `ℂ × ℝ` under the light-cone coordinates of the cone. -/
def lcMeasureC : Measure LightCone := Measure.map lcInvC volume

lemma ae_ne_zero_fst : ∀ᵐ z : ℂ × ℝ ∂volume, z.1 ≠ 0 := by
  rw [Measure.volume_eq_prod, ae_iff]
  have e : {a : ℂ × ℝ | ¬a.1 ≠ 0} = ({0} : Set ℂ) ×ˢ Set.univ := by ext z; simp
  rw [e, Measure.prod_prod, measure_singleton, zero_mul]

lemma measurePreserving_of_lcC (A : SL2C) {F : ℂ × ℝ → ℂ × ℝ} (hF : MeasurePreserving F volume volume)
    (h : ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), A • lcInvC z = lcInvC (F z)) :
    MeasurePreserving (fun Q : LightCone => A • Q) lcMeasureC lcMeasureC := by
  refine ⟨(continuous_smul_cone_right A).measurable, ?_⟩
  rw [lcMeasureC, Measure.map_map (continuous_smul_cone_right A).measurable continuous_lcInvC.measurable]
  have hc : Measure.map ((fun P : LightCone => A • P) ∘ lcInvC) volume = Measure.map (lcInvC ∘ F) volume :=
    Measure.map_congr (h.mono fun z hz => hz)
  rw [hc, ← Measure.map_map continuous_lcInvC.measurable hF.measurable, hF.map_eq]

/-- **`lcMeasureC` is invariant under `SL(2,ℂ)`.** -/
theorem measurePreserving_lcMeasureC (A : SL2C) :
    MeasurePreserving (fun Q : LightCone => A • Q) lcMeasureC lcMeasureC := by
  have hU : ∀ (a b : ℂ) (ha : a ≠ 0),
      MeasurePreserving (fun Q : LightCone => upperSL a b ha • Q) lcMeasureC lcMeasureC :=
    fun a b ha => measurePreserving_of_lcC _ (measurePreserving_upperF a b ha)
      (Filter.Eventually.of_forall (smul_upper_lcInvC a b ha))
  have hW : MeasurePreserving (fun Q : LightCone => weylSL • Q) lcMeasureC lcMeasureC :=
    measurePreserving_of_lcC _ (measurePreserving_weylF (m := 0))
      (ae_ne_zero_fst.mono fun z hz => smul_weyl_lcInvC hz)
  rcases eq_upper_or_eq_upper_mul_weyl_mul_upper A with ⟨a, b, ha, rfl⟩ | ⟨a, b, ha, a', b', ha', rfl⟩
  · exact hU a b ha
  · have e : (fun Q : LightCone => (upperSL a b ha * weylSL * upperSL a' b' ha') • Q) =
        (fun Q : LightCone => upperSL a b ha • Q) ∘ (fun Q : LightCone => weylSL • Q) ∘
          (fun Q : LightCone => upperSL a' b' ha' • Q) := by
      funext P
      simp only [Function.comp_apply, mul_smul]
    rw [e]
    exact (hU a b ha).comp (hW.comp (hU a' b' ha'))

/-! ## The source's measure `d³p / (2|p|)` -/

/-- The light-cone coordinates `(p₁ − i p₂, log(|p| − p₃))` of a momentum `p`. -/
def coneLC (p : Fin 3 → ℝ) : ℂ × ℝ := (⟨p 0, -p 1⟩, Real.log (Real.sqrt (sqV p) - p 2))

/-- The chart `p ↦ (|p|, p)` of the cone, through the light-cone coordinates: `coneChart p = |p| + p·σ` whenever
`p₃ < |p|`, that is off the null half-line `p₁ = p₂ = 0 ≤ p₃` (`coneChart_eq_momH`). -/
def coneChart (p : Fin 3 → ℝ) : LightCone := lcInvC (coneLC p)

lemma coneChart_eq_momH {p : Fin 3 → ℝ} (hp : p 2 < Real.sqrt (sqV p)) :
    (coneChart p).1 = momH (Real.sqrt (sqV p)) p := by
  have hpos : 0 < Real.sqrt (sqV p) - p 2 := by linarith
  have hsq : Real.sqrt (sqV p) ^ 2 = sqV p := Real.sq_sqrt (sqV_nonneg p)
  have hn : ‖(⟨p 0, -p 1⟩ : ℂ)‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hreal : ‖(⟨p 0, -p 1⟩ : ℂ)‖ ^ 2 * (Real.sqrt (sqV p) - p 2)⁻¹ = Real.sqrt (sqV p) + p 2 := by
    rw [hn]
    field_simp
    simp only [sqV] at hsq ⊢
    first | linear_combination hsq | linear_combination -hsq
  rw [coneChart, lcInvC_apply, coneLC]
  simp only [Real.exp_neg, Real.exp_log hpos, hreal]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [momH]

lemma measurable_coneChart : Measurable coneChart := by
  refine continuous_lcInvC.measurable.comp ?_
  refine Measurable.prodMk ?_ ?_
  · have e : (fun p : Fin 3 → ℝ => (⟨p 0, -p 1⟩ : ℂ)) =
        fun p => (p 0 : ℂ) + ((-p 1 : ℝ) : ℂ) * Complex.I := by
      funext p; apply Complex.ext <;> simp
    change Measurable fun p : Fin 3 → ℝ => (⟨p 0, -p 1⟩ : ℂ)
    rw [e]
    fun_prop
  · exact Real.measurable_log.comp (continuous_sqV.sqrt.measurable.sub (measurable_pi_apply 2))

lemma coneLC_lcVec (z : ℂ × ℝ) : coneLC (lcVec 0 z) = z := by
  have hs : Real.sqrt (sqV (lcVec 0 z)) = (‖z.1‖ ^ 2 * Real.exp (-z.2) + Real.exp z.2) / 2 := by
    have := sqrt_lcVec (m := 0) z
    simpa using this
  have h2 : (‖z.1‖ ^ 2 * Real.exp (-z.2) + Real.exp z.2) / 2 - lcVec 0 z 2 = Real.exp z.2 := by
    simp [lcVec]; ring
  apply Prod.ext
  · apply Complex.ext <;> simp [coneLC, lcVec]
  · simp only [coneLC]
    rw [hs, h2, Real.log_exp]

/-- **The light-cone coordinates carry `d²w dt` to `d³p / |p|`.** -/
lemma lintegral_comp_lcVec_zero (g : (Fin 3 → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ z : ℂ × ℝ, g (lcVec 0 z) = ∫⁻ p, g p * ENNReal.ofReal (1 / Real.sqrt (sqV p)) := by
  have hF : Measurable fun p : Fin 3 → ℝ => g p * ENNReal.ofReal (1 / Real.sqrt (sqV p)) :=
    hg.mul (ENNReal.measurable_ofReal.comp (measurable_const.div continuous_sqV.sqrt.measurable))
  rw [Measure.volume_eq_prod, lintegral_prod (fun z : ℂ × ℝ => g (lcVec 0 z))
    (hg.comp continuous_lcVec.measurable).aemeasurable]
  have hae : ∀ᵐ w : ℂ, w ≠ 0 := by
    rw [ae_iff]; simpa using Measure.addHaar_singleton (volume : Measure ℂ) 0
  have hin : ∀ᵐ w : ℂ, ∫⁻ t, g (lcVec 0 (w, t)) =
      ∫⁻ z, (fun p => g p * ENNReal.ofReal (1 / Real.sqrt (sqV p))) (lcTheta (w, z)) := by
    filter_upwards [hae] with w hw
    have hc : 0 < (0 : ℝ) ^ 2 + ‖w‖ ^ 2 := by have := norm_pos_iff.2 hw; positivity
    simp only [lcVec_eq]
    rw [lintegral_comp_lcFib hc (fun z => g (lcTheta (w, z)))]
    refine lintegral_congr fun z => ?_
    rw [sqV_lcTheta, zero_pow two_ne_zero, zero_add]
  rw [lintegral_congr_ae hin]
  rw [← lintegral_prod (fun z : ℂ × ℝ => g (lcTheta z) * ENNReal.ofReal (1 / Real.sqrt (sqV (lcTheta z))))
    (hF.comp measurePreserving_lcTheta.measurable).aemeasurable, ← Measure.volume_eq_prod]
  exact measurePreserving_lcTheta.lintegral_comp hF

lemma map_lcVec_zero : Measure.map (lcVec 0) volume =
    volume.withDensity fun p => ENNReal.ofReal (1 / Real.sqrt (sqV p)) := by
  ext S hS
  rw [Measure.map_apply continuous_lcVec.measurable hS, withDensity_apply _ hS, ← lintegral_indicator_one
    (continuous_lcVec.measurable hS)]
  have h := lintegral_comp_lcVec_zero (S.indicator 1) (measurable_one.indicator hS)
  calc ∫⁻ a, (lcVec 0 ⁻¹' S).indicator 1 a = ∫⁻ z, S.indicator 1 (lcVec 0 z) :=
        lintegral_congr fun z => by by_cases hz : lcVec 0 z ∈ S <;> simp [hz]
    _ = _ := h
    _ = _ := by
        rw [← lintegral_indicator hS]
        exact lintegral_congr fun p => by by_cases hp : p ∈ S <;> simp [hp]

/-- **The source's invariant measure on the light cone**, `δ(p²) Θ(p⁰) d⁴p = d³p / (2|p|)`, through the chart
`p ↦ (|p|, p)`. -/
def coneSourceMeasure : Measure LightCone :=
  Measure.map coneChart (volume.withDensity fun p => ENNReal.ofReal (1 / (2 * Real.sqrt (sqV p))))

/-- `d³p / (2|p|)` is half the image of the Lebesgue measure under the light-cone coordinates. -/
theorem coneSourceMeasure_eq : coneSourceMeasure = (2⁻¹ : ENNReal) • lcMeasureC := by
  have hρ : Measurable fun p : Fin 3 → ℝ => ENNReal.ofReal (1 / Real.sqrt (sqV p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div continuous_sqV.sqrt.measurable)
  have e : (fun p : Fin 3 → ℝ => ENNReal.ofReal (1 / (2 * Real.sqrt (sqV p)))) =
      (2⁻¹ : ENNReal) • fun p => ENNReal.ofReal (1 / Real.sqrt (sqV p)) := by
    funext p
    rw [Pi.smul_apply, smul_eq_mul, show 1 / (2 * Real.sqrt (sqV p)) = 2⁻¹ * (1 / Real.sqrt (sqV p)) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [coneSourceMeasure, e, withDensity_smul _ hρ, Measure.map_smul _ measurable_coneChart.aemeasurable,
    ← map_lcVec_zero, Measure.map_map measurable_coneChart continuous_lcVec.measurable]
  have e2 : coneChart ∘ lcVec 0 = lcInvC := funext fun z => by
    simp only [Function.comp_apply, coneChart, coneLC_lcVec]
  rw [e2]
  rfl

/-- **`d³p / (2|p|)` is Lorentz invariant.** -/
theorem measurePreserving_coneSourceMeasure (A : SL2C) :
    MeasurePreserving (fun Q : LightCone => A • Q) coneSourceMeasure coneSourceMeasure := by
  rw [coneSourceMeasure_eq]
  exact ⟨(continuous_smul_cone_right A).measurable, by
    rw [Measure.map_smul _ (continuous_smul_cone_right A).aemeasurable, (measurePreserving_lcMeasureC A).map_eq]⟩

lemma measurableEmbedding_lcInvC : MeasurableEmbedding lcInvC := by
  refine MeasurableEmbedding.of_measurable_inverse continuous_lcInvC.measurable ?_
    (g := fun P : LightCone => ((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1, Real.log (deltaC P.1))) ?_ ?_
  · have e : Set.range lcInvC = {P : LightCone | 0 < deltaC P.1} := by
      ext P
      constructor
      · rintro ⟨z, rfl⟩
        rw [Set.mem_setOf_eq, deltaC, lcInvC_11, Complex.ofReal_re]
        exact Real.exp_pos _
      · intro hP
        refine ⟨((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 1, Real.log (deltaC P.1)), ?_⟩
        have h11 : (P.1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = (deltaC P.1 : ℂ) := by
          have h := P.2.1.isHermitian.apply 1 1
          apply Complex.ext
          · simp [deltaC]
          · have : (star ((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1)).im = ((P.1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1).im := by
              rw [h]
            simp at this
            simp; linarith
        refine cone_ext ?_ ?_ ?_
        · rw [lcInvC_01]
        · rw [lcInvC_11, Real.exp_log hP, h11]
        · rw [h11]; exact Complex.ofReal_ne_zero.2 hP.ne'
    rw [e]
    exact measurableSet_lt measurable_const measurable_deltaC
  · exact measurable_entry01.prodMk (Real.measurable_log.comp measurable_deltaC)
  · intro z
    simp only [deltaC, lcInvC_01, lcInvC_11, Complex.ofReal_re, Real.log_exp]

instance sigmaFinite_lcMeasureC : SigmaFinite lcMeasureC := measurableEmbedding_lcInvC.sigmaFinite_map

instance sigmaFinite_coneSourceMeasure : SigmaFinite coneSourceMeasure := by
  rw [coneSourceMeasure_eq]
  refine MeasureTheory.Measure.sigmaFinite_of_le lcMeasureC ?_
  calc (2⁻¹ : ENNReal) • lcMeasureC ≤ (1 : ENNReal) • lcMeasureC := by
        gcongr; norm_num
    _ = lcMeasureC := one_smul _ _

/-! ## Irreducibility on `L²(d³p / 2|p|)` -/

/-- **The massless one-particle representations on `L²(d³p / 2|p|)` are irreducible (Schur form).** -/
theorem commutant_eq_scalar_coneSourceMeasure (n : ℤ) (B : Lp ℂ 2 coneSourceMeasure →L[ℂ] Lp ℂ 2 coneSourceMeasure)
    (hT : ∀ a f, B (translCone a f) = translCone a (B f))
    (hU : ∀ A f, B (helL2 n measurePreserving_coneSourceMeasure A f) =
      helL2 n measurePreserving_coneSourceMeasure A (B f)) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ _ :=
  commutant_eq_scalar_cone n measurePreserving_coneSourceMeasure B hT hU

/-- **The massless one-particle representations on `L²(d³p / 2|p|)` are irreducible.** -/
theorem irreducible_massless_coneSourceMeasure (n : ℤ) (K : Submodule ℂ (Lp ℂ 2 coneSourceMeasure))
    (hK : IsClosed (K : Set (Lp ℂ 2 coneSourceMeasure))) (hT : ∀ a, ∀ f ∈ K, translCone a f ∈ K)
    (hU : ∀ A, ∀ f ∈ K, helL2 n measurePreserving_coneSourceMeasure A f ∈ K) : K = ⊥ ∨ K = ⊤ :=
  irreducible_massless n measurePreserving_coneSourceMeasure K hK hT hU

end

end Lightlike.Poincare
