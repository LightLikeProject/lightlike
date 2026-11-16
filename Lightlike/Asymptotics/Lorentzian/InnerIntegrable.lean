import Lightlike.Asymptotics.Lorentzian.CoherentVertex

/-!
# The inner integral of the Lorentzian vertex converges

`integrable_lorInner`: for boundary data of unit spinors and nonnegative spin parameters, the
integrand of `lorVertex` is integrable on `ℂ^10` at every point of `SL(2,ℂ)^5`. It is a product over
the ten edges of functions of one variable (`integrable_edge`), each bounded by the density of `Ω`
(from `Re S ≤ 0`, off the null set where an overlap vanishes, `ae_overlap_src`, `ae_overlap_tgt`),
which is integrable (`integrable_lorEdgeDensity`): no joint bound on `ℂ^10` is needed.
With `integrable_lorOuter` this makes `lorVertex` a genuine integral for the coherent boundary data
(`integrable_lorInner_coh`).
-/

open MeasureTheory Finset Matrix
open scoped NNReal ENNReal ComplexConjugate
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian


/-- An affine function of `conj w` vanishes on a null set unless it is identically zero. -/
theorem ae_affine_conj_ne_zero (α β : ℂ) (h : α ≠ 0 ∨ β ≠ 0) :
    ∀ᵐ w : ℂ ∂MeasureTheory.volume, α * conj w + β ≠ 0 := by
  by_cases hα : α = 0
  · have hβ : β ≠ 0 := by simpa [hα] using h
    exact Filter.Eventually.of_forall fun w => by simpa [hα] using hβ
  · have : {w : ℂ | α * conj w + β = 0} ⊆ {conj (-β / α)} := by
      intro w hw
      have hw' : α * conj w + β = 0 := hw
      simp only [Set.mem_singleton_iff]
      have : conj w = -β / α := by field_simp; linear_combination hw'
      rw [← this, Complex.conj_conj]
    rw [MeasureTheory.ae_iff]
    exact MeasureTheory.measure_mono_null (by simpa using this) (MeasureTheory.measure_singleton _)

/-- **The overlap with the source spinor vanishes on a null set only**: for `M` of determinant `1`
and `ξ ≠ 0`, `⟨Mᴴ (w, 1), ξ⟩ ≠ 0` for almost every `w`. -/
theorem ae_overlap_src (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) {ξ : Spinor} (hξ : ξ ≠ 0) :
    ∀ᵐ w : ℂ ∂MeasureTheory.volume, inner ℂ (spinAct Mᴴ (lorSpinor w)) ξ ≠ 0 := by
  have h : (M 0 0 * ξ 0 + M 0 1 * ξ 1) ≠ 0 ∨ (M 1 0 * ξ 0 + M 1 1 * ξ 1) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have h0 : spinAct M ξ = 0 := by
      ext i; fin_cases i <;> simp [spinAct, hcon.1, hcon.2]
    exact spinAct_ne_zero_of_det M (by rw [hM]; exact one_ne_zero) hξ h0
  filter_upwards [ae_affine_conj_ne_zero _ _ h] with w hw
  have e : inner ℂ (spinAct Mᴴ (lorSpinor w)) ξ =
      (M 0 0 * ξ 0 + M 0 1 * ξ 1) * conj w + (M 1 0 * ξ 0 + M 1 1 * ξ 1) := by
    simp [PiLp.inner_apply, spinAct, lorSpinor, Fin.sum_univ_two, conjTranspose_apply]
    ring
  rw [e]; exact hw

/-- **The overlap with the target spinor vanishes on a null set only**: for `M` of determinant `1`
and `ξ' ≠ 0`, `⟨Jξ', Mᴴ (w, 1)⟩ ≠ 0` for almost every `w`. -/
theorem ae_overlap_tgt (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1) {ξ : Spinor} (hξ : ξ ≠ 0) :
    ∀ᵐ w : ℂ ∂MeasureTheory.volume, inner ℂ (jMap ξ) (spinAct Mᴴ (lorSpinor w)) ≠ 0 := by
  have hdet : (M.map star).det = 1 := by
    have := (starRingEnd ℂ).map_det M
    rw [hM, map_one] at this
    exact this.symm
  set v : Spinor := !₂[-ξ 1, ξ 0] with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply hξ
    have h0 := congrArg (fun u : Spinor => u 0) h
    have h1 := congrArg (fun u : Spinor => u 1) h
    ext i; fin_cases i <;> simp [hv] at h0 h1 ⊢ <;> simp [h0, h1]
  have h : (-ξ 1 * conj (M 0 0) + ξ 0 * conj (M 0 1)) ≠ 0 ∨
      (-ξ 1 * conj (M 1 0) + ξ 0 * conj (M 1 1)) ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have h0 : spinAct (M.map star) v = 0 := by
      ext i
      fin_cases i
      · simp [spinAct, hv]; linear_combination hcon.1
      · simp [spinAct, hv]; linear_combination hcon.2
    exact spinAct_ne_zero_of_det _ (by rw [hdet]; exact one_ne_zero) hv0 h0
  filter_upwards [ae_affine_ne_zero _ _ h] with w hw
  have e : inner ℂ (jMap ξ) (spinAct Mᴴ (lorSpinor w)) =
      (-ξ 1 * conj (M 0 0) + ξ 0 * conj (M 0 1)) * w + (-ξ 1 * conj (M 1 0) + ξ 0 * conj (M 1 1)) := by
    simp [PiLp.inner_apply, spinAct, lorSpinor, jMap, Fin.sum_univ_two, conjTranspose_apply]
    ring
  rw [e]; exact hw

/-- **One edge of the inner integrand is integrable on `ℂ`**: it is bounded by the density of `Ω`
(from `Re S ≤ 0`, off the null set where an overlap vanishes), which is integrable. -/
theorem integrable_edge (k p : ℝ) (hk : 0 ≤ k) (A B : SL2C) {ξ ξ' : Spinor} (hξ : ‖ξ‖ = 1)
    (hξ' : ‖ξ'‖ = 1) :
    Integrable (fun w : ℂ => Complex.exp (triAction k p
        (spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ
        (spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ') *
      (((‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
        ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ)) volume := by
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hξ
  have hξ0' : ξ' ≠ 0 := fun h => by simp [h] at hξ'
  have hZc : Continuous fun w : ℂ => spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w) :=
    continuous_spinAct.comp (continuous_const.prodMk continuous_lorSpinor)
  have hZc' : Continuous fun w : ℂ => spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w) :=
    continuous_spinAct.comp (continuous_const.prodMk continuous_lorSpinor)
  have hmeas : Measurable fun w : ℂ => Complex.exp (triAction k p
        (spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ
        (spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ') *
      (((‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
        ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
    refine (Complex.measurable_exp.comp (measurable_triAction k p hZc hZc' ξ ξ')).mul ?_
    exact Complex.measurable_ofReal.comp (Measurable.inv (Measurable.mul
      (hZc.norm.pow 2).measurable (hZc'.norm.pow 2).measurable))
  refine (integrable_lorEdgeDensity A B).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_overlap_src (A : Matrix (Fin 2) (Fin 2) ℂ) A.2 hξ0,
    ae_overlap_tgt (B : Matrix (Fin 2) (Fin 2) ℂ) B.2 hξ0'] with w h1 h2
  have hS := re_triAction_le_zero (p := p) hk (spinAct_conjTranspose_ne_zero A (lorSpinor_ne_zero w))
    (spinAct_conjTranspose_ne_zero B (lorSpinor_ne_zero w)) hξ hξ' h1 h2
  have hexp : ‖Complex.exp (triAction k p
        (spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ
        (spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)) ξ')‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr hS
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc _ ≤ 1 * (‖spinAct (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2 *
        ‖spinAct (B : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w)‖ ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = _ := one_mul _

/-- **The inner integrand is integrable on `ℂ^10` for every point of `SL(2,ℂ)^5`**, for boundary
data of unit spinors and nonnegative spin parameters: it is a product over the ten edges of
integrable functions of one variable each (`integrable_edge`), so no joint bound is needed. Together
with `integrable_lorOuter` this makes `lorVertex` a genuine integral for the coherent data. -/
theorem integrable_lorInner (j p : Fin 10 → ℝ) (hj : ∀ e, 0 ≤ j e) (g : BdryData)
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (X : Fin 5 → SL2C) :
    Integrable (fun w : Fin 10 → ℂ => lorIntegrand j p g X w) volume := by
  have h := Integrable.fintype_prod (ι := Fin 10) (μ := fun _ : Fin 10 => (volume : Measure ℂ))
    (f := fun e (w' : ℂ) => Complex.exp (triAction (j e) (p e)
        (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w')) (firstCol (g e 0))
        (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w')) (firstCol (g e 1))) *
      (((‖spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w')‖ ^ 2 *
        ‖spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (lorSpinor w')‖ ^ 2)⁻¹ : ℝ) : ℂ))
    (fun e => integrable_edge (j e) (p e) (hj e) (X (edgeSrc e)) (X (edgeTgt e)) (hξ e) (hξ' e))
  rw [← volume_pi] at h
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  unfold lorIntegrand lorAction lorEdgeDensity
  beta_reduce
  rw [Complex.exp_sum, ← Finset.prod_mul_distrib]

/-- The first column of an `SU(2)` matrix is a unit spinor. -/
theorem norm_firstCol_su2 (g : SU2) :
    ‖firstCol (g : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
  obtain ⟨-, -, h⟩ := su2_entries g
  rw [firstCol, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two]
  simp only [Complex.normSq_eq_norm_sq] at h
  simp [h]

/-- The boundary spinors of the coherent data are unit spinors. -/
theorem bdry_norm (G : Fin 5 → Fin 5 → SU2) (e : Fin 10) :
    ‖firstCol (bdry G e 0)‖ = 1 ∧ ‖firstCol (bdry G e 1)‖ = 1 := by
  obtain ⟨-, -, h⟩ := su2_entries (G (edgeSrc e) (edgeTgt e))
  obtain ⟨-, -, h'⟩ := su2_entries (G (edgeTgt e) (edgeSrc e))
  simp only [Complex.normSq_eq_norm_sq] at h h'
  constructor
  · simp only [bdry, ite_true, firstCol, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [h]
  · simp only [bdry, show ¬((1 : Fin 2) = 0) by decide, ite_false, firstCol, EuclideanSpace.norm_eq,
      Fin.sum_univ_two]
    simp [wM, Matrix.mul_apply, Fin.sum_univ_two]
    linarith

/-- **`lorVertex` is a genuine integral for the coherent data**: for every `γ`, spins `J` and SU(2)
data `G`, both the inner integrand (on `ℂ^10`, for every point of `SL(2,ℂ)^5`) and the outer one
(`integrable_lorOuter`) are integrable. -/
theorem integrable_lorInner_coh (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (G : Fin 5 → Fin 5 → SU2)
    (X : Fin 5 → SL2C) :
    Integrable (fun w : Fin 10 → ℂ => lorIntegrand (fun e => (edgeSpin J e : ℝ) / 2)
      (fun e => eprlRho γ (edgeSpin J e)) (bdry G) X w) volume :=
  integrable_lorInner _ _ (fun e => by positivity) _ (fun e => (bdry_norm G e).1)
    (fun e => (bdry_norm G e).2) X

end Lightlike.Asymptotics.Lorentzian
