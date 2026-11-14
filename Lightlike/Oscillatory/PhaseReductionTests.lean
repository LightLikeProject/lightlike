module

public import Lightlike.Oscillatory.PhaseReduction
public import Lightlike.Oscillatory.QuadraticPhaseTests

/-!
# Trust checks for local stationary phase

For `stationary_phase_local`,
`∫ u e^{iτφ} = (2π/τ)^{n/2} invSqrtDet(-iφ''(0)) u(0) + O(τ^{-n/2-1})` for `u` supported near a
nondegenerate critical point `0` of a phase with `Im φ ≥ 0`:

* **Non-vacuity, a phase that is not quadratic** (`stationary_phase_local_testPhase`,
  `testPhase_bump`): the complex phase `φ(x) = x²/2 + x³ + i x⁴` on `ℝ¹` satisfies every
  hypothesis (`testPhase_zero`, `fderiv_testPhase_zero`, `im_testPhase_nonneg`, Hessian
  `hessMat_testPhase = 1`, computed from the definition). The theorem gives
  `∫ u e^{iτφ} = (2π/τ)^{1/2} e^{iπ/4} u(0) + O(τ^{-3/2})`, and a bump with `u(0) = 1` satisfies
  the support hypothesis, so the leading term is nonzero. The perturbation `x³ + i x⁴` does not
  change the Fresnel coefficient of the quadratic part, as the theorem predicts.
* **Wrong constant** (`testPhase_wrong_phase`): the leading coefficient is unique
  (`coeff_eq_zero_of_isBigO`), so the real Gaussian coefficient `(2π/τ)^{1/2} u(0)` of
  Laplace's method, without the Fresnel phase `e^{iπ/4}`, admits no `O(τ^{-3/2})` error for this
  phase on any neighbourhood of `0`.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset Filter
open scoped Real ContDiff Topology

namespace Lightlike.Oscillatory

/-- The polynomial `e(w) = w²/2 + w³ + i w⁴`. -/
noncomputable def testPoly (w : ℂ) : ℂ := w ^ 2 / 2 + w ^ 3 + I * w ^ 4

/-- The test phase on `ℝ¹`: `φ(x) = x²/2 + x³ + i x⁴`. -/
noncomputable def testPhase (x : Fin 1 → ℝ) : ℂ := testPoly (x 0 : ℂ)

/-- The derivative of `x ↦ e(x₀)` on `ℝ¹`, for `e : ℂ → ℂ` complex differentiable. -/
theorem hasFDerivAt_comp_coord {e : ℂ → ℂ} {e' : ℂ} {x : Fin 1 → ℝ}
    (he : HasDerivAt e e' (x 0 : ℂ)) :
    HasFDerivAt (fun y : Fin 1 → ℝ => e (y 0 : ℂ))
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) e').restrictScalars ℝ).comp
        (ofRealCLM.comp (ContinuousLinearMap.proj 0))) x := by
  have hL : HasFDerivAt (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ))
      (ofRealCLM.comp (ContinuousLinearMap.proj 0)) x :=
    ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply 0 x)
  exact (he.hasFDerivAt.restrictScalars ℝ).comp x hL

/-- The partial derivative of `x ↦ e(x₀)` on `ℝ¹` is `e'(x₀)`. -/
theorem coordDeriv_comp_coord {e : ℂ → ℂ} {e' : ℂ} {x : Fin 1 → ℝ}
    (he : HasDerivAt e e' (x 0 : ℂ)) (l : Fin 1) :
    coordDeriv (fun y : Fin 1 → ℝ => e (y 0 : ℂ)) l x = e' := by
  rw [Subsingleton.elim l 0]
  simp [coordDeriv, (hasFDerivAt_comp_coord he).fderiv]

/-- `e'(w) = w + 3 w² + 4 i w³`. -/
theorem hasDerivAt_testPoly (w : ℂ) :
    HasDerivAt testPoly (w + 3 * w ^ 2 + 4 * I * w ^ 3) w := by
  have := (((hasDerivAt_pow 2 w).div_const 2).add (hasDerivAt_pow 3 w)).add
    ((hasDerivAt_pow 4 w).const_mul I)
  exact this.congr_deriv (by norm_num; ring)

/-- `e''(w) = 1 + 6 w + 12 i w²`. -/
theorem hasDerivAt_testPoly' (w : ℂ) :
    HasDerivAt (fun w : ℂ => w + 3 * w ^ 2 + 4 * I * w ^ 3) (1 + 6 * w + 12 * I * w ^ 2) w := by
  have := (((hasDerivAt_id w).add ((hasDerivAt_pow 2 w).const_mul 3))).add
    ((hasDerivAt_pow 3 w).const_mul (4 * I))
  exact this.congr_deriv (by norm_num; ring)

/-- The test phase is smooth. -/
theorem contDiff_testPhase : ContDiff ℝ ∞ testPhase := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  exact ((hL.pow 2).div_const 2 |>.add (hL.pow 3)).add (contDiff_const.mul (hL.pow 4))

/-- The test phase vanishes at `0`. -/
theorem testPhase_zero : testPhase 0 = 0 := by
  simp [testPhase, testPoly]

/-- `0` is a critical point of the test phase. -/
theorem fderiv_testPhase_zero : fderiv ℝ testPhase 0 = 0 := by
  have h := hasFDerivAt_comp_coord (e := testPoly) (x := 0) (hasDerivAt_testPoly _)
  rw [show (fun y : Fin 1 → ℝ => testPoly (y 0 : ℂ)) = testPhase from rfl] at h
  rw [h.fderiv]
  ext
  simp

/-- `Im φ(x) = x⁴ ≥ 0` everywhere. -/
theorem im_testPhase_nonneg (x : Fin 1 → ℝ) : 0 ≤ (testPhase x).im := by
  simp only [testPhase, testPoly, ← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
    div_ofNat_im]
  positivity

/-- The Hessian of the test phase at `0` is `1`, so the critical point is nondegenerate. -/
theorem hessMat_testPhase : hessMat testPhase 0 = 1 := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv testPhase 0 y) =
      fun y => (fun w : ℂ => w + 3 * w ^ 2 + 4 * I * w ^ 3) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (hasDerivAt_testPoly _) 0
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_testPoly' _)]
  simp

/-- A smooth bump on `ℝ¹`, equal to `1` on `closedBall 0 (δ/2)` and supported in
`closedBall 0 δ`. -/
noncomputable def smallBump {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (0 : Fin 1 → ℝ) :=
  ⟨δ / 2, δ, by positivity, by linarith⟩

/-- The bump `smallBump` as a complex amplitude. -/
noncomputable def smallAmp {δ : ℝ} (hδ : 0 < δ) (x : Fin 1 → ℝ) : ℂ := (smallBump hδ x : ℂ)

/-- The amplitude `smallAmp` is smooth. -/
theorem contDiff_smallAmp {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (smallAmp hδ) :=
  ofRealCLM.contDiff.comp (smallBump hδ).contDiff

/-- The amplitude `smallAmp` is supported in `closedBall 0 δ`. -/
theorem tsupport_smallAmp {δ : ℝ} (hδ : 0 < δ) :
    tsupport (smallAmp hδ) ⊆ Metric.closedBall 0 δ := by
  have h := tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) ofReal_zero (smallBump hδ)
  rw [(smallBump hδ).tsupport_eq] at h
  exact h

/-- The amplitude `smallAmp` is `1` at the origin. -/
theorem smallAmp_zero {δ : ℝ} (hδ : 0 < δ) : smallAmp hδ 0 = 1 := by
  simp [smallAmp, (smallBump hδ).one_of_mem_closedBall
    (Metric.mem_closedBall_self (smallBump hδ).rIn_pos.le)]

/-- A term `(2π/τ)^p c` is `O(τ^{-p-1})` only if `c = 0`. -/
theorem coeff_eq_zero_of_isBigO {p : ℝ} {c : ℂ}
    (h : (fun τ : ℝ => (((2 * π / τ) ^ p : ℝ) : ℂ) * c) =O[atTop] fun τ : ℝ => τ ^ (-p - 1)) :
    c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨a, ha⟩ := eventually_atTop.mp hC
  refine asymp_coeff_unique (F := fun τ => (((2 * π / τ) ^ p : ℝ) : ℂ) * c) (p := p)
    (a := c) (b := 0)
    ⟨0, 1, one_pos, fun τ _ => by simp⟩
    ⟨C, max a 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
  have h1 := ha τ (le_trans (le_max_left _ _) hτ)
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [le_max_right a 1]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hτ0 _)] at h1
  simpa using h1

/-- Non-vacuity: the test phase `φ(x) = x²/2 + x³ + i x⁴` satisfies the hypotheses of
`stationary_phase_local` (with Hessian `1`), which gives
`∫ u e^{iτφ} = (2π/τ)^{1/2} e^{iπ/4} u(0) + O(τ^{-3/2})` near `0`: the Fresnel coefficient of the
quadratic part, unchanged by the cubic and the complex quartic terms. -/
theorem stationary_phase_local_testPhase :
    ∃ δ, 0 < δ ∧ ∀ u : (Fin 1 → ℝ) → ℂ, ContDiff ℝ ∞ u → tsupport u ⊆ Metric.closedBall 0 δ →
      (fun τ : ℝ => (∫ x, u x * cexp (I * τ * testPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * cexp (π / 4 * I) * u 0) =O[atTop]
        fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  obtain ⟨δ, hδ, -, h⟩ := stationary_phase_local contDiff_testPhase testPhase_zero
    fderiv_testPhase_zero one_pos (fun x _ => im_testPhase_nonneg x)
    (by rw [hessMat_testPhase]; simp)
  refine ⟨δ, hδ, fun u hu hus => ?_⟩
  have h1 := h u hu hus
  rw [hessMat_testPhase, invSqrtDet_neg_I_one] at h1
  simpa only [Nat.cast_one, one_mul] using h1

/-- Non-vacuity with a nonzero leading term: a bump `u` with `u(0) = 1` satisfies the support
hypothesis, and `∫ u e^{iτφ} = (2π/τ)^{1/2} e^{iπ/4} + O(τ^{-3/2})` for the test phase. -/
theorem testPhase_bump :
    ∃ δ, 0 < δ ∧ ∃ u : (Fin 1 → ℝ) → ℂ, ContDiff ℝ ∞ u ∧
      tsupport u ⊆ Metric.closedBall 0 δ ∧ u 0 = 1 ∧
      (fun τ : ℝ => (∫ x, u x * cexp (I * τ * testPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * cexp (π / 4 * I)) =O[atTop]
        fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  obtain ⟨δ, hδ, h⟩ := stationary_phase_local_testPhase
  refine ⟨δ, hδ, smallAmp hδ, contDiff_smallAmp hδ, tsupport_smallAmp hδ, smallAmp_zero hδ, ?_⟩
  simpa only [smallAmp_zero, mul_one] using h _ (contDiff_smallAmp hδ) (tsupport_smallAmp hδ)

/-- Wrong constant: for the test phase, the real Gaussian coefficient `(2π/τ)^{1/2} u(0)` of
Laplace's method, without the Fresnel phase `e^{iπ/4}`, admits no `O(τ^{-3/2})` error on any
neighbourhood of `0`. -/
theorem testPhase_wrong_phase :
    ¬ ∃ δ, 0 < δ ∧ ∀ u : (Fin 1 → ℝ) → ℂ, ContDiff ℝ ∞ u → tsupport u ⊆ Metric.closedBall 0 δ →
      (fun τ : ℝ => (∫ x, u x * cexp (I * τ * testPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * u 0) =O[atTop]
        fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  rintro ⟨δ', hδ', h'⟩
  obtain ⟨δ, hδ, h⟩ := stationary_phase_local_testPhase
  have hε : 0 < min δ δ' := lt_min hδ hδ'
  have hus := tsupport_smallAmp hε
  have h1 := h _ (contDiff_smallAmp hε)
    (hus.trans (Metric.closedBall_subset_closedBall (min_le_left _ _)))
  have h2 := h' _ (contDiff_smallAmp hε)
    (hus.trans (Metric.closedBall_subset_closedBall (min_le_right _ _)))
  have h4 : (fun τ : ℝ => (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (cexp (π / 4 * I) - 1))
      =O[atTop] fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
    refine (h2.sub h1).congr_left fun τ => ?_
    simp only [smallAmp_zero]
    ring
  have hre := congrArg Complex.re (sub_eq_zero.mp (coeff_eq_zero_of_isBigO h4))
  rw [show (π / 4 * I : ℂ) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_four, one_re] at hre
  have hs : √2 = 2 := by linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [hs] at this
  norm_num at this

end Lightlike.Oscillatory
