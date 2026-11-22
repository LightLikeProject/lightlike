module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.AbelTransformDeriv
public import Lightlike.Lorentz.SL2RPlancherel.KernelPair

/-!
# A bounded truncation of the half Abel integral of `F'`

For `F` of class `C²` with compact support, `H = halfAbel F'` is continuous and vanishes beyond the
support of `F`.  The truncation `φ = 1_{[1, R]} · H` is bounded, measurable, vanishes on `[R, ∞)`,
and for `v > 1` satisfies `∫_a φ a / √(a - v) = -π F v` (Abel inversion, `halfAbel_halfAbel_deriv`).
Together with `integral_integral_abelSlice_pair` this expresses `π² ∫_{v>1} F(v) conj F(v)` as the
triple integral of `φ ⊗ conj φ` — step (B) of the Plancherel route for `SL(2,ℝ)`
(milestone HA3, density `ρ tanh(πρ)`).
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `halfAbel f` is continuous for `f` of class `C¹` with compact support. -/
theorem continuous_halfAbel (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Continuous (halfAbel f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_halfAbel' f hf hc x).continuousAt

/-- For `a` beyond the support of `F`, `halfAbel F' a = 0`. -/
theorem halfAbel_deriv_eq_zero {F : ℝ → ℂ} {R : ℝ} (hR : ∀ x : ℝ, R ≤ ‖x‖ → deriv F x = 0)
    {a : ℝ} (ha : R ≤ a) : halfAbel (deriv F) a = 0 := by
  unfold halfAbel
  have : ∀ w ∈ Ioi (0 : ℝ), (w ^ (-(1 / 2 : ℝ)) : ℝ) • deriv F (a + w) = 0 := by
    intro w hw
    have hw' : (0 : ℝ) < w := hw
    have : R ≤ ‖a + w‖ := by
      rw [Real.norm_eq_abs]
      exact le_trans (by linarith) (le_abs_self _)
    simp [hR _ this]
  rw [setIntegral_congr_fun measurableSet_Ioi this]
  simp

/-- `∫_a φ a / √(a - v) = halfAbel φ v`, for `φ` agreeing with `H` on `(1, ∞)` and `v > 1`. -/
theorem integral_abelSlice_eq_halfAbel {φ H : ℝ → ℂ} (h : ∀ a, 1 < a → φ a = H a) {v : ℝ}
    (hv : 1 < v) : ∫ a, abelSlice φ v a = halfAbel H v := by
  rw [halfAbel_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi v)]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
    have ha' : 1 < a := lt_trans hv ha
    unfold abelSlice
    rw [h a ha', div_eq_mul_inv]
    push_cast
    rfl
  · intro a ha
    have : a - v ≤ 0 := by
      have : a ≤ v := not_lt.1 ha
      linarith
    simp [abelSlice, Real.sqrt_eq_zero_of_nonpos this]

/-- **Truncated Abel integral of `F'`.** For `F` of class `C²` with compact support there are
`R, M` and a measurable `φ`, bounded by `M`, vanishing on `[R, ∞)`, with
`∫_a φ a / √(a - v) = -π F v` for `v > 1`. -/
theorem exists_abelSlice_trunc (F : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) :
    ∃ (R M : ℝ) (φ : ℝ → ℂ), Measurable φ ∧ (∀ a, ‖φ a‖ ≤ M) ∧ (∀ a, R ≤ a → φ a = 0) ∧
      ∀ v, 1 < v → ∫ a, abelSlice φ v a = -(π : ℂ) * F v := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv F) := by
    have h2 : ContDiff ℝ (1 + 1) F := hF
    exact ((contDiff_succ_iff_deriv (n := 1) (f := F)).1 h2).2.2
  obtain ⟨R0, hR0pos, hR0⟩ := hc.deriv.exists_pos_le_norm
  set R : ℝ := max R0 1 with hRdef
  have hR : ∀ x : ℝ, R ≤ ‖x‖ → deriv F x = 0 := fun x hx => hR0 x (le_trans (le_max_left _ _) hx)
  set H : ℝ → ℂ := halfAbel (deriv F) with hH
  have hHc : Continuous H := continuous_halfAbel (deriv F) hd1 hc.deriv
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := R)).exists_bound_of_continuousOn
    hHc.continuousOn
  set M : ℝ := max M0 0 with hMdef
  have hHzero : ∀ a, R ≤ a → H a = 0 := fun a ha => halfAbel_deriv_eq_zero hR ha
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  refine ⟨R, M, (Icc 1 R).indicator H, hHc.measurable.indicator measurableSet_Icc, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ Icc (1 : ℝ) R
    · rw [indicator_of_mem ha]
      exact le_trans (hM0 a ha) (le_max_left _ _)
    · rw [indicator_of_notMem ha]
      simp [hMdef]
  · intro a ha
    by_cases h : a ∈ Icc (1 : ℝ) R
    · rw [indicator_of_mem h]
      exact hHzero a ha
    · rw [indicator_of_notMem h]
  · intro v hv
    have hagree : ∀ a, 1 < a → (Icc 1 R).indicator H a = H a := by
      intro a ha
      by_cases h : a ∈ Icc (1 : ℝ) R
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h]
        have : R < a := by
          by_contra hh
          exact h ⟨ha.le, not_lt.1 hh⟩
        exact (hHzero a this.le).symm
    rw [integral_abelSlice_eq_halfAbel hagree hv, hH]
    exact halfAbel_halfAbel_deriv F hF1 hc v

lemma abelSlice_conj (φ : ℝ → ℂ) (v a : ℝ) :
    abelSlice (fun x => (starRingEnd ℂ) (φ x)) v a = (starRingEnd ℂ) (abelSlice φ v a) := by
  unfold abelSlice
  rw [map_mul, Complex.conj_ofReal]

/-- **Step (B) of the Plancherel route.** For `F` of class `C²` with compact support there is a
bounded measurable `φ` (the truncation of `halfAbel F'`) with
`∫_a ∫_b ∫_{v>1} (φ a/√(a-v)) (conj φ b/√(b-v)) = π² ∫_{v>1} F v · conj (F v)`. -/
theorem exists_triple_integral_eq (F : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) :
    ∃ (R M : ℝ) (φ : ℝ → ℂ), Measurable φ ∧ (∀ a, ‖φ a‖ ≤ M) ∧ (∀ a, R ≤ a → φ a = 0) ∧
      (∀ v, 1 < v → ∫ a, abelSlice φ v a = -(π : ℂ) * F v) ∧
      ∫ a, ∫ b, ∫ v in Ioi (1 : ℝ),
          abelSlice φ v a * abelSlice (fun x => (starRingEnd ℂ) (φ x)) v b =
        (π : ℂ) ^ 2 * ∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v) := by
  obtain ⟨R, M, φ, hφ, hM, hR, hint⟩ := exists_abelSlice_trunc F hF hc
  refine ⟨R, M, φ, hφ, hM, hR, hint, ?_⟩
  rw [integral_integral_abelSlice_pair (ψ := fun x => (starRingEnd ℂ) (φ x)) hφ
    (Complex.continuous_conj.measurable.comp hφ) hM
    (fun a => by simpa using hM a) hR (fun a ha => by simp [hR a ha])]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have h2 : ∫ b, abelSlice (fun x => (starRingEnd ℂ) (φ x)) v b
      = (starRingEnd ℂ) (∫ b, abelSlice φ v b) := by
    simp only [abelSlice_conj]
    exact integral_conj
  simp only [h2, hint v hv, map_mul, Complex.conj_ofReal, map_neg]
  ring

end Lightlike.Lorentz.SL2RPlancherel
