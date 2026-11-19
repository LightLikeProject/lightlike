import Lightlike.Poincare.IrreducibleMassive

/-!
# The measure `d³p / (2ω_p)` on the mass shell is Lorentz invariant

In the light-cone coordinates `(w, t) ∈ ℂ × ℝ` of the mass shell, `P = [[(m² + |w|²) e^{-t}, w], [w̄, e^t]]`
(`lcInv`), an upper triangular `B = [[a, b], [0, a⁻¹]]` acts by `(w, t) ↦ ((a/ā) w + (b/ā) e^t, t − 2 log |a|)` and
the Weyl element `[[0, −1], [1, 0]]` by `(w, t) ↦ (−w̄, log(m² + |w|²) − t)`; both preserve the Lebesgue measure of
`ℂ × ℝ` (skew products of isometries and translations). These generate `SL(2,ℂ)` (Bruhat decomposition,
`eq_upper_or_eq_upper_mul_weyl_mul_upper`), so the image `lcMeasure` of the Lebesgue measure is invariant
(`measurePreserving_shellAct_lcMeasure`).

The source's measure `δ(p² − m²) Θ(p⁰) d⁴p`, which is `d³p / (2ω_p)` in the chart `p ↦ (ω_p, p)` (`sourceMeasure`), is
half of `lcMeasure` (`sourceMeasure_eq`: the change of variables `t ↦ ((m² + |w|²) e^{-t} − e^t)/2` along each
light-cone fibre has Jacobian `ω_p`), hence invariant (`measurePreserving_shellAct_sourceMeasure`), and the massive
one-particle representations on `L²(d³p / 2ω_p)` are irreducible (`irreducible_massive_sourceMeasure`,
`commutant_eq_scalar_sourceMeasure`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2, Remarks (page 11 of v2): the invariant scalar product
  `∫ dᴰp δ(p² + m²) Θ(p⁰) Σ_σ Ψ*_{p,σ} Φ_{p,σ}` (signature `(−,+,+,+)`).
* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §6, Theorem 6.2, page 148.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace Lightlike.Poincare

noncomputable section

variable {m : ℝ} (hm : 0 < m)

/-! ## Light-cone coordinates -/

/-- The spatial momentum of the light-cone point `(w, t)`: `(Re w, −Im w, ((m² + |w|²) e^{-t} − e^t)/2)`. -/
def lcVec (m : ℝ) (z : ℂ × ℝ) : Fin 3 → ℝ :=
  ![z.1.re, -z.1.im, ((m ^ 2 + ‖z.1‖ ^ 2) * Real.exp (-z.2) - Real.exp z.2) / 2]

/-- The point of the shell with light-cone coordinates `(w, t)`. -/
def lcInv (z : ℂ × ℝ) : MassShell m := chartInv hm (lcVec m z)

lemma continuous_lcVec : Continuous (lcVec m) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_re.comp continuous_fst
  · exact (Complex.continuous_im.comp continuous_fst).neg
  · exact (((continuous_const.add ((continuous_norm.comp continuous_fst).pow 2)).mul
      (Real.continuous_exp.comp continuous_snd.neg)).sub (Real.continuous_exp.comp continuous_snd)).div_const _

lemma continuous_lcInv : Continuous (lcInv (m := m) hm) := (continuous_chartInv hm).comp continuous_lcVec

lemma sqrt_lcVec (z : ℂ × ℝ) : Real.sqrt (m ^ 2 + sqV (lcVec m z)) =
    ((m ^ 2 + ‖z.1‖ ^ 2) * Real.exp (-z.2) + Real.exp z.2) / 2 := by
  have he : Real.exp (-z.2) * Real.exp z.2 = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hn : ‖z.1‖ ^ 2 = z.1.re ^ 2 + z.1.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  simp only [sqV, lcVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (m ^ 2 + ‖z.1‖ ^ 2) * he + hn

lemma lcInv_apply (z : ℂ × ℝ) : ((lcInv hm z : MassShell m) : Matrix (Fin 2) (Fin 2) ℂ) =
    !![(((m ^ 2 + ‖z.1‖ ^ 2) * Real.exp (-z.2) : ℝ) : ℂ), z.1; conj z.1, (Real.exp z.2 : ℂ)] := by
  change momH (Real.sqrt (m ^ 2 + sqV (lcVec m z))) (lcVec m z) = _
  rw [sqrt_lcVec]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [momH, lcVec] <;> ring

lemma lcInv_01 (z : ℂ × ℝ) : ((lcInv hm z : MassShell m) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = z.1 := by
  rw [lcInv_apply]; simp

lemma lcInv_11 (z : ℂ × ℝ) : ((lcInv hm z : MassShell m) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = Real.exp z.2 := by
  rw [lcInv_apply]; simp

/-- A point of the shell is determined by its entries `P₀₁` and `P₁₁`. -/
lemma shell_ext {P Q : MassShell m} (h01 : P.1 0 1 = Q.1 0 1) (h11 : P.1 1 1 = Q.1 1 1) : P = Q := by
  have hP := P.2
  have hQ := Q.2
  have hPh := hP.1.isHermitian
  have hQh := hQ.1.isHermitian
  have h10 : P.1 1 0 = Q.1 1 0 := by
    rw [← hPh.apply 1 0, ← hQh.apply 1 0, h01]
  have hpos : Q.1 1 1 ≠ 0 := (hQ.1.diag_pos (i := 1)).ne'
  have hdP := hP.2
  have hdQ := hQ.2
  rw [Matrix.det_fin_two] at hdP hdQ
  rw [h01, h10, h11] at hdP
  have h00 : P.1 0 0 = Q.1 0 0 := by
    have : P.1 0 0 * Q.1 1 1 = Q.1 0 0 * Q.1 1 1 := by linear_combination hdP - hdQ
    exact mul_right_cancel₀ hpos this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-! ## Two families of generators and their action -/

/-- `[[a, b], [0, a⁻¹]]`. -/
def upperSL (a b : ℂ) (ha : a ≠ 0) : SL2C :=
  ⟨!![a, b; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

/-- The Weyl element `[[0, −1], [1, 0]]`. -/
def weylSL : SL2C := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- The action of `[[a, b], [0, a⁻¹]]` in light-cone coordinates. -/
def upperF (a b : ℂ) (z : ℂ × ℝ) : ℂ × ℝ :=
  (a / conj a * z.1 + b / conj a * (Real.exp z.2 : ℂ), z.2 - 2 * Real.log ‖a‖)

/-- The action of the Weyl element in light-cone coordinates. -/
def weylF (m : ℝ) (z : ℂ × ℝ) : ℂ × ℝ := (-conj z.1, Real.log (m ^ 2 + ‖z.1‖ ^ 2) - z.2)

lemma shellAct_upper_lcInv (a b : ℂ) (ha : a ≠ 0) (z : ℂ × ℝ) :
    shellAct (upperSL a b ha) (lcInv hm z) = lcInv (m := m) hm (upperF a b z) := by
  have hca : conj a ≠ 0 := by simpa using ha
  apply shell_ext
  · rw [lcInv_01]
    change actP (upperSL a b ha) (lcInv hm z).1 0 1 = _
    rw [actP, lcInv_apply]
    simp [upperSL, upperF, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  · rw [lcInv_11]
    change actP (upperSL a b ha) (lcInv hm z).1 1 1 = _
    rw [actP, lcInv_apply]
    have hn : (0 : ℝ) < ‖a‖ := norm_pos_iff.2 ha
    have e : Real.exp (z.2 - 2 * Real.log ‖a‖) = Real.exp z.2 / ‖a‖ ^ 2 := by
      rw [Real.exp_sub, show 2 * Real.log ‖a‖ = Real.log (‖a‖ ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    simp only [upperF, e]
    simp [upperSL, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

lemma shellAct_weyl_lcInv (z : ℂ × ℝ) : shellAct weylSL (lcInv hm z) = lcInv (m := m) hm (weylF m z) := by
  apply shell_ext
  · rw [lcInv_01]
    change actP weylSL (lcInv hm z).1 0 1 = _
    rw [actP, lcInv_apply]
    simp [weylSL, weylF, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [lcInv_11]
    change actP weylSL (lcInv hm z).1 1 1 = _
    rw [actP, lcInv_apply]
    have e : Real.exp (Real.log (m ^ 2 + ‖z.1‖ ^ 2) - z.2) = (m ^ 2 + ‖z.1‖ ^ 2) * Real.exp (-z.2) := by
      rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg, div_eq_mul_inv]
    simp only [weylF, e]
    simp [weylSL, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## They preserve the Lebesgue measure of `ℂ × ℝ` -/

lemma measurePreserving_unit_mul_add (a : ℂ) (ha : a ≠ 0) (c : ℂ) :
    MeasurePreserving (fun w : ℂ => a / conj a * w + c) := by
  have hca : conj a ≠ 0 := by simpa using ha
  have h1 : MeasurePreserving (fun w : ℂ => a / conj a * w) := by
    have h := (rotation (Circle.ofConjDivSelf (conj a) hca)).measurePreserving
    have e : (fun w : ℂ => a / conj a * w) = ⇑(rotation (Circle.ofConjDivSelf (conj a) hca)) := by
      funext w; rw [rotation_apply, Circle.ofConjDivSelf_coe, Complex.conj_conj]
    rw [e]; exact h
  exact (measurePreserving_add_right volume c).comp h1

lemma measurePreserving_upperF (a b : ℂ) (ha : a ≠ 0) :
    MeasurePreserving (upperF a b) (volume : Measure (ℂ × ℝ)) volume := by
  rw [Measure.volume_eq_prod]
  have hG : MeasurePreserving (fun p : ℝ × ℂ => (p.1 - 2 * Real.log ‖a‖,
      a / conj a * p.2 + b / conj a * (Real.exp p.1 : ℂ))) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
    refine (measurePreserving_sub_right volume (2 * Real.log ‖a‖)).skew_product
      (g := fun t w => a / conj a * w + b / conj a * (Real.exp t : ℂ)) ?_
      (Filter.Eventually.of_forall fun t => (measurePreserving_unit_mul_add a ha _).map_eq)
    exact Continuous.measurable (by fun_prop)
  exact (Measure.measurePreserving_swap.comp hG).comp (Measure.measurePreserving_swap (μ := (volume : Measure ℂ))
    (ν := (volume : Measure ℝ)))

lemma measurePreserving_weylF : MeasurePreserving (weylF m) (volume : Measure (ℂ × ℝ)) volume := by
  rw [Measure.volume_eq_prod]
  have hf : MeasurePreserving (fun w : ℂ => -conj w) := by
    have h := (Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ (E := ℂ))).measurePreserving
    have e : (fun w : ℂ => -conj w) = ⇑(Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ (E := ℂ))) := by
      funext w; simp
    rw [e]; exact h
  have hfib : ∀ c : ℝ, MeasurePreserving (fun t : ℝ => c - t) := by
    intro c
    have h1 : MeasurePreserving (fun t : ℝ => -t) := Measure.measurePreserving_neg volume
    have h2 := measurePreserving_add_left volume c
    simpa [Function.comp_def, sub_eq_add_neg] using h2.comp h1
  exact hf.skew_product (g := fun w t => Real.log (m ^ 2 + ‖w‖ ^ 2) - t)
    (by
      change Measurable fun p : ℂ × ℝ => Real.log (m ^ 2 + ‖p.1‖ ^ 2) - p.2
      fun_prop)
    (Filter.Eventually.of_forall fun w => (hfib _).map_eq)

/-! ## Bruhat decomposition -/

/-- **Bruhat decomposition**: every element of `SL(2,ℂ)` is upper triangular, or a product
`[[1, x], [0, 1]] · [[0, −1], [1, 0]] · [[γ, δ], [0, γ⁻¹]]`. -/
lemma eq_upper_or_eq_upper_mul_weyl_mul_upper (A : SL2C) :
    (∃ (a b : ℂ) (ha : a ≠ 0), A = upperSL a b ha) ∨
      ∃ (a b : ℂ) (ha : a ≠ 0) (a' b' : ℂ) (ha' : a' ≠ 0), A = upperSL a b ha * weylSL * upperSL a' b' ha' := by
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  by_cases hγ : (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0
  · left
    rw [hγ, mul_zero, sub_zero] at hdet
    have ha : (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    refine ⟨_, (A : Matrix (Fin 2) (Fin 2) ℂ) 0 1, ha, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact hγ
    · change (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0)⁻¹
      exact (eq_inv_of_mul_eq_one_right hdet)
  · right
    refine ⟨1, (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 / (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0, one_ne_zero,
      (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1, hγ, ?_⟩
    apply Subtype.ext
    change (A : Matrix (Fin 2) (Fin 2) ℂ) = !![1, (A : Matrix (Fin 2) (Fin 2) ℂ) 0 0 /
      (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0; 0, 1⁻¹] * !![0, -1; 1, 0] * !![(A : Matrix (Fin 2) (Fin 2) ℂ) 1 0,
      (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1; 0, ((A : Matrix (Fin 2) (Fin 2) ℂ) 1 0)⁻¹]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals (try field_simp)
    all_goals first | linear_combination hdet | linear_combination -hdet

/-! ## The invariant measure -/

/-- The image of the Lebesgue measure of `ℂ × ℝ` under the light-cone coordinates. -/
def lcMeasure : Measure (MassShell m) := Measure.map (lcInv hm) volume

lemma measurePreserving_of_lc (A : SL2C) {F : ℂ × ℝ → ℂ × ℝ} (hF : MeasurePreserving F volume volume)
    (h : ∀ z, shellAct A (lcInv hm z) = lcInv (m := m) hm (F z)) :
    MeasurePreserving (shellAct A) (lcMeasure (m := m) hm) (lcMeasure hm) := by
  refine ⟨(continuous_shellAct A).measurable, ?_⟩
  rw [lcMeasure, Measure.map_map (continuous_shellAct A).measurable (continuous_lcInv hm).measurable]
  have e : shellAct A ∘ lcInv (m := m) hm = lcInv hm ∘ F := funext h
  rw [e, ← Measure.map_map (continuous_lcInv hm).measurable hF.measurable, hF.map_eq]

/-- **`lcMeasure` is invariant under `SL(2,ℂ)`.** -/
theorem measurePreserving_shellAct_lcMeasure (A : SL2C) :
    MeasurePreserving (shellAct A) (lcMeasure (m := m) hm) (lcMeasure hm) := by
  have hU : ∀ (a b : ℂ) (ha : a ≠ 0),
      MeasurePreserving (shellAct (upperSL a b ha)) (lcMeasure (m := m) hm) (lcMeasure hm) :=
    fun a b ha => measurePreserving_of_lc hm _ (measurePreserving_upperF a b ha)
      (shellAct_upper_lcInv hm a b ha)
  have hW : MeasurePreserving (shellAct weylSL) (lcMeasure (m := m) hm) (lcMeasure hm) :=
    measurePreserving_of_lc hm _ measurePreserving_weylF (shellAct_weyl_lcInv hm)
  rcases eq_upper_or_eq_upper_mul_weyl_mul_upper A with ⟨a, b, ha, rfl⟩ | ⟨a, b, ha, a', b', ha', rfl⟩
  · exact hU a b ha
  · have e : shellAct (m := m) (upperSL a b ha * weylSL * upperSL a' b' ha') =
        shellAct (upperSL a b ha) ∘ shellAct weylSL ∘ shellAct (upperSL a' b' ha') := by
      funext P
      simp only [Function.comp_apply, shellAct_mul]
    rw [e]
    exact (hU a b ha).comp (hW.comp (hU a' b' ha'))

/-! ## The source's measure `d³p / (2ω_p)` -/

/-- `h_c(t) = (c e^{-t} − e^t) / 2`, the third momentum coordinate along a light-cone fibre. -/
def lcFib (c t : ℝ) : ℝ := (c * Real.exp (-t) - Real.exp t) / 2

lemma hasDerivAt_lcFib (c t : ℝ) : HasDerivAt (lcFib c) (-(c * Real.exp (-t) + Real.exp t) / 2) t := by
  have h1 := ((hasDerivAt_neg t).exp).const_mul c
  have h2 := (hasDerivAt_id t).exp
  have h := (h1.sub h2).div_const 2
  convert h using 1
  · funext x; simp [lcFib]
  · simp; ring

lemma sqrt_lcFib {c : ℝ} (hc : 0 ≤ c) (t : ℝ) :
    Real.sqrt (c + lcFib c t ^ 2) = (c * Real.exp (-t) + Real.exp t) / 2 := by
  have he : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), lcFib]
  linear_combination c * he

lemma strictAnti_lcFib {c : ℝ} (hc : 0 ≤ c) : StrictAnti (lcFib c) :=
  strictAnti_of_deriv_neg fun t => by
    rw [(hasDerivAt_lcFib c t).deriv]
    have : 0 < c * Real.exp (-t) + Real.exp t := by positivity
    linarith

lemma surjective_lcFib {c : ℝ} (hc : 0 < c) : Function.Surjective (lcFib c) := by
  intro z
  have hs : z < Real.sqrt (c + z ^ 2) := by
    calc z ≤ |z| := le_abs_self z
      _ = Real.sqrt (z ^ 2) := (Real.sqrt_sq_eq_abs z).symm
      _ < Real.sqrt (c + z ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg z) (by linarith)
  have hpos : 0 < Real.sqrt (c + z ^ 2) - z := by linarith
  have hsq : Real.sqrt (c + z ^ 2) ^ 2 = c + z ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨Real.log (Real.sqrt (c + z ^ 2) - z), ?_⟩
  rw [lcFib, Real.exp_neg, Real.exp_log hpos]
  field_simp
  linear_combination -hsq

/-- **The one-dimensional change of variables**: `∫ G(h_c(t)) dt = ∫ G(z) / √(c + z²) dz`. -/
lemma lintegral_comp_lcFib {c : ℝ} (hc : 0 < c) (G : ℝ → ENNReal) :
    ∫⁻ t, G (lcFib c t) = ∫⁻ z, G z * ENNReal.ofReal (1 / Real.sqrt (c + z ^ 2)) := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (hasDerivAt_lcFib c x).hasDerivWithinAt) (strictAnti_lcFib hc.le).injective.injOn
    (fun z => G z * ENNReal.ofReal (1 / Real.sqrt (c + z ^ 2)))
  rw [Set.image_univ, (surjective_lcFib hc).range_eq, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun t => ?_
  have ha : 0 < (c * Real.exp (-t) + Real.exp t) / 2 := by positivity
  rw [sqrt_lcFib hc.le, show |(-(c * Real.exp (-t) + Real.exp t) / 2)| = (c * Real.exp (-t) + Real.exp t) / 2 by
    rw [neg_div, abs_neg, abs_of_pos ha], mul_comm (G _), ← mul_assoc, ← ENNReal.ofReal_mul ha.le,
    mul_one_div_cancel ha.ne', ENNReal.ofReal_one, one_mul]

/-- The momentum `(Re w, −Im w, z)`. -/
def lcTheta (z : ℂ × ℝ) : Fin 3 → ℝ := ![z.1.re, -z.1.im, z.2]

lemma measurePreserving_lcTheta : MeasurePreserving lcTheta (volume : Measure (ℂ × ℝ)) volume := by
  have hφ : MeasurePreserving (fun w : ℂ => (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (w.re, -w.im)) := by
    have h1 := Complex.volume_preserving_equiv_real_prod
    have h2 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) (volume : Measure (ℝ × ℝ)) volume := by
      rw [Measure.volume_eq_prod]
      exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)
    have h3 := (volume_preserving_finTwoArrow ℝ).symm
    exact h3.comp (h2.comp h1)
  have hK : MeasurePreserving (fun z : ℂ × ℝ => (z.2, (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (z.1.re, -z.1.im)))
      (volume : Measure (ℂ × ℝ)) volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap.comp (hφ.prod (MeasurePreserving.id volume))
  have hΞ := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm
  have e : lcTheta = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)).symm ∘
      fun z : ℂ × ℝ => (z.2, (MeasurableEquiv.finTwoArrow (α := ℝ)).symm (z.1.re, -z.1.im)) := by
    funext z i
    fin_cases i <;> rfl
  rw [e]
  exact hΞ.comp hK

lemma lcVec_eq (z : ℂ × ℝ) : lcVec m z = lcTheta (z.1, lcFib (m ^ 2 + ‖z.1‖ ^ 2) z.2) := rfl

lemma sqV_lcTheta (z : ℂ × ℝ) : sqV (lcTheta z) = ‖z.1‖ ^ 2 + z.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sqV, lcTheta]
  ring

include hm in
/-- **The light-cone coordinates carry `d²w dt` to `d³p / ω_p`.** -/
lemma lintegral_comp_lcVec (g : (Fin 3 → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ z : ℂ × ℝ, g (lcVec m z) =
      ∫⁻ p, g p * ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p)) := by
  have hF : Measurable fun p : Fin 3 → ℝ => g p * ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p)) :=
    hg.mul (ENNReal.measurable_ofReal.comp (measurable_const.div (continuous_const.add
      continuous_sqV).sqrt.measurable))
  rw [Measure.volume_eq_prod, lintegral_prod (fun z : ℂ × ℝ => g (lcVec m z))
    (hg.comp continuous_lcVec.measurable).aemeasurable]
  have hin : ∀ w : ℂ, ∫⁻ t, g (lcVec m (w, t)) =
      ∫⁻ z, (fun p => g p * ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p))) (lcTheta (w, z)) := by
    intro w
    have hc : 0 < m ^ 2 + ‖w‖ ^ 2 := by have := sq_pos_of_pos hm; positivity
    simp only [lcVec_eq]
    rw [lintegral_comp_lcFib hc (fun z => g (lcTheta (w, z)))]
    refine lintegral_congr fun z => ?_
    rw [sqV_lcTheta, ← add_assoc]
  simp_rw [hin]
  rw [← lintegral_prod (fun z : ℂ × ℝ => g (lcTheta z) * ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV (lcTheta z))))
    (hF.comp measurePreserving_lcTheta.measurable).aemeasurable, ← Measure.volume_eq_prod]
  exact measurePreserving_lcTheta.lintegral_comp hF

include hm in
lemma map_lcVec : Measure.map (lcVec m) volume =
    volume.withDensity fun p => ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p)) := by
  ext S hS
  rw [Measure.map_apply continuous_lcVec.measurable hS, withDensity_apply _ hS, ← lintegral_indicator_one
    (continuous_lcVec.measurable hS)]
  have h := lintegral_comp_lcVec hm (S.indicator 1) (measurable_one.indicator hS)
  calc ∫⁻ a, (lcVec m ⁻¹' S).indicator 1 a = ∫⁻ z, S.indicator 1 (lcVec m z) :=
        lintegral_congr fun z => by by_cases hz : lcVec m z ∈ S <;> simp [hz]
    _ = _ := h
    _ = _ := by
        rw [← lintegral_indicator hS]
        exact lintegral_congr fun p => by by_cases hp : p ∈ S <;> simp [hp]

/-- **The source's invariant measure** `δ(p² − m²) Θ(p⁰) d⁴p = d³p / (2ω_p)`, `ω_p = √(m² + |p|²)`, on the mass shell,
through the chart `p ↦ (ω_p, p)`. -/
def sourceMeasure : Measure (MassShell m) :=
  Measure.map (chartInv hm) (volume.withDensity fun p => ENNReal.ofReal (1 / (2 * Real.sqrt (m ^ 2 + sqV p))))

/-- `d³p / (2ω_p)` is half the image of the Lebesgue measure under the light-cone coordinates. -/
theorem sourceMeasure_eq : sourceMeasure (m := m) hm = (2⁻¹ : ENNReal) • lcMeasure hm := by
  have hρ : Measurable fun p : Fin 3 → ℝ => ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (continuous_const.add continuous_sqV).sqrt.measurable)
  have e : (fun p : Fin 3 → ℝ => ENNReal.ofReal (1 / (2 * Real.sqrt (m ^ 2 + sqV p)))) =
      (2⁻¹ : ENNReal) • fun p => ENNReal.ofReal (1 / Real.sqrt (m ^ 2 + sqV p)) := by
    funext p
    rw [Pi.smul_apply, smul_eq_mul, show 1 / (2 * Real.sqrt (m ^ 2 + sqV p)) = 2⁻¹ * (1 / Real.sqrt (m ^ 2 + sqV p))
      by ring, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [sourceMeasure, e, withDensity_smul _ hρ, Measure.map_smul _ (continuous_chartInv hm).aemeasurable,
    ← map_lcVec hm, Measure.map_map (continuous_chartInv hm).measurable continuous_lcVec.measurable]
  rfl

/-- **`d³p / (2ω_p)` is Lorentz invariant.** -/
theorem measurePreserving_shellAct_sourceMeasure (A : SL2C) :
    MeasurePreserving (shellAct A) (sourceMeasure (m := m) hm) (sourceMeasure hm) := by
  rw [sourceMeasure_eq]
  exact ⟨(continuous_shellAct A).measurable, by
    rw [Measure.map_smul _ (continuous_shellAct A).aemeasurable, (measurePreserving_shellAct_lcMeasure hm A).map_eq]⟩

lemma measurableEmbedding_chartInv : MeasurableEmbedding (chartInv (m := m) hm) :=
  MeasurableEmbedding.of_measurable_inverse (continuous_chartInv hm).measurable
    (by
      have hs : Function.Surjective (chartInv (m := m) hm) := fun P => ⟨coordV P.1, chartInv_coordV hm P⟩
      rw [hs.range_eq]
      exact MeasurableSet.univ)
    (continuous_coordV.comp continuous_subtype_val).measurable (fun p => coordV_chartInv hm p)

instance sigmaFinite_sourceMeasure : SigmaFinite (sourceMeasure (m := m) hm) :=
  (measurableEmbedding_chartInv hm).sigmaFinite_map

/-! ## Irreducibility on `L²(d³p / 2ω_p)` -/

variable {n : ℕ}

/-- **Irreducibility of the massive one-particle representations on `L²(d³p / 2ω_p)` (Schur form)**: every bounded
operator commuting with the translations and with the induced action `U(A)` of spin `n/2` is a scalar. -/
theorem commutant_eq_scalar_sourceMeasure
    (B : Lp (Spinor n) 2 (sourceMeasure (m := m) hm) →L[ℂ] Lp (Spinor n) 2 (sourceMeasure hm))
    (hT : ∀ a f, B (translL2 n a f) = translL2 n a (B f))
    (hU : ∀ A f, B (inducedL2 hm n (measurePreserving_shellAct_sourceMeasure hm) A f) =
      inducedL2 hm n (measurePreserving_shellAct_sourceMeasure hm) A (B f)) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ _ :=
  commutant_eq_scalar hm (measurePreserving_shellAct_sourceMeasure hm) B hT hU

/-- **The massive one-particle representations on `L²(d³p / 2ω_p)` are irreducible**: a closed subspace invariant
under every translation and every `U(A)` is `0` or everything. -/
theorem irreducible_massive_sourceMeasure (K : Submodule ℂ (Lp (Spinor n) 2 (sourceMeasure (m := m) hm)))
    (hK : IsClosed (K : Set (Lp (Spinor n) 2 (sourceMeasure (m := m) hm))))
    (hT : ∀ a, ∀ f ∈ K, translL2 n a f ∈ K)
    (hU : ∀ A, ∀ f ∈ K, inducedL2 hm n (measurePreserving_shellAct_sourceMeasure hm) A f ∈ K) :
    K = ⊥ ∨ K = ⊤ :=
  irreducible_massive hm (measurePreserving_shellAct_sourceMeasure hm) K hK hT hU

end

end Lightlike.Poincare
