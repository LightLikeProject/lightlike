module

public import Lightlike.Oscillatory.StationaryPhase
public import Lightlike.Oscillatory.LocalisationTests

/-!
# Trust checks for stationary phase

* **Non-vacuity, one critical point, global** (`stationary_phase_testPhase`): the phase
  `φ(x) = x²/2 + x³ + i x⁴` on all of `ℝ¹`, with a bump of radius `1` and `U = ℝ¹`, satisfies every
  hypothesis of `stationary_phase_of_isOpen`. Its only critical point is `0`, with Hessian `1`, so
  `∫ a e^{iτφ} = (2π/τ)^{1/2} e^{iπ/4} + O(τ^{-3/2})`: the Fresnel coefficient. Unlike
  `stationary_phase_local_testPhase`, the support of the amplitude is not chosen small.
* **Non-vacuity, two critical points** (`stationary_phase_twoPhase`): the phase
  `φ(x) = x³/3 − x + i (x² − 1)²` has the critical points `x = ±1`, with `φ(±1) = ∓2/3` and
  `-i φ''(±1) = 8 ∓ 2i`. The theorem (in its `Fin n → ℝ` form) gives the sum of the two
  contributions, each with its own phase `e^{∓2iτ/3}`.
* **Non-vacuity, a critical point on the boundary of the support** (`stationary_phase_edge`): the
  phase `φ(x) = x²/2 + i x³` with the amplitude `a(x) = ψ(x) ψ(1 − x)`, `ψ = expNegInvGlue`,
  supported on `[0, 1]`. The only critical point, `0`, lies on the boundary of the support, and
  `Im φ = x³` is negative just to its left, so no open set containing the support has `Im φ ≥ 0`
  (`edgePhase_not_isOpen`) and the corollaries with Hörmander's hypothesis do not apply.
  `stationary_phase_pi` applies and gives `∫ a e^{iτφ} = O(τ^{-3/2})`, since `a(0) = 0`.
* **Wrong input, a degenerate critical point** (`stationary_phase_needs_nondegenerate`): for the
  phase `i x⁴`, every hypothesis of `stationary_phase_of_isOpen` except nondegeneracy holds (its
  Hessian at `0` is `0`, `det_hess_toEuc_quarticPhase`), and the conclusion fails for every
  leading coefficient: `∫ a e^{-τx⁴} ≥ 2 e^{-1} τ^{-1/4}` (`integral_quartic_lower`) decays more
  slowly than `τ^{-1/2}` (`quarticPhase_not_isBigO`).
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset Filter Asymptotics
open scoped Real ContDiff Topology

namespace Lightlike.Oscillatory

/-! ### Non-vacuity: the test phase on all of `ℝ¹` -/

/-- `ofEuc` undoes `toEuc`. -/
theorem ofEuc_toEuc {n : ℕ} (v : (Fin n → ℝ) → ℂ) : ofEuc (toEuc v) = v := rfl

/-- The Hessian of the test phase, transported to `EuclideanSpace`, is `1` at `0`. -/
theorem hess_toEuc_testPhase : hess (toEuc testPhase) 0 = 1 :=
  (hessMat_ofEuc (toEuc testPhase) 0).symm.trans hessMat_testPhase

/-- The only critical point of the transported test phase is `0`. -/
theorem critical_toEuc_testPhase (x : EuclideanSpace ℝ (Fin 1)) :
    ((toEuc testPhase x).im = 0 ∧ fderiv ℝ (toEuc testPhase) x = 0) ↔
      x ∈ ({0} : Finset (EuclideanSpace ℝ (Fin 1))) := by
  rw [Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    have h0 : WithLp.ofLp x = 0 := eq_zero_of_im_testPhase h
    rw [← WithLp.toLp_ofLp (x := x), h0]
    rfl
  · rintro rfl
    refine ⟨by simp [toEuc, testPhase_zero], ?_⟩
    exact (fderiv_ofEuc_eq_zero_iff (toEuc testPhase) 0).mp fderiv_testPhase_zero

/-- Non-vacuity of `stationary_phase_of_isOpen`, globally: for the test phase
`φ(x) = x²/2 + x³ + i x⁴` on all of `ℝ¹` and the bump `a` of radius `1` (equal to `1` near `0`),
`∫ a e^{iτφ} = (2π/τ)^{1/2} e^{iπ/4} + O(τ^{-3/2})`. The single critical point `0` has
Hessian `1`, and the Fresnel factor `e^{iπ/4}` is `invSqrtDet (-i · 1)`. -/
theorem stationary_phase_testPhase :
    (fun τ : ℝ => (∫ x, toEuc (smallAmp one_pos) x * cexp (I * τ * toEuc testPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * cexp (π / 4 * I)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  have ha0 : toEuc (smallAmp one_pos) 0 = 1 := smallAmp_zero one_pos
  have h := stationary_phase_of_isOpen (contDiff_toEuc contDiff_testPhase)
    (contDiff_toEuc (contDiff_smallAmp one_pos))
    (hasCompactSupport_toEuc (hasCompactSupport_smallAmp one_pos)) isOpen_univ
    (Set.subset_univ _) (fun x _ => im_testPhase_nonneg _) {0}
    (fun x _ => critical_toEuc_testPhase x)
    (fun x hx => by
      rw [Finset.mem_singleton.mp hx]
      exact subset_tsupport _ (by simp [Function.mem_support, ha0]))
    (fun x hx => by
      rw [Finset.mem_singleton.mp hx, hess_toEuc_testPhase]
      simp)
  have hφ0 : toEuc testPhase 0 = 0 := testPhase_zero
  simpa only [Finset.sum_singleton, hφ0, mul_zero, Complex.exp_zero, one_mul,
    hess_toEuc_testPhase, invSqrtDet_neg_I_one, Nat.cast_one, ha0, mul_one] using h

/-! ### Wrong input: a degenerate critical point -/

/-- The phase `φ(x) = i x⁴` on `ℝ¹`: `Im φ ≥ 0`, its only critical point is `0`, and there the
Hessian vanishes. -/
noncomputable def quarticPhase (x : Fin 1 → ℝ) : ℂ := I * (x 0 : ℂ) ^ 4

/-- `e'(w) = 4 i w³` for `e(w) = i w⁴`. -/
theorem hasDerivAt_quartic (w : ℂ) : HasDerivAt (fun w : ℂ => I * w ^ 4) (4 * I * w ^ 3) w :=
  ((hasDerivAt_pow 4 w).const_mul I).congr_deriv (by norm_num; ring)

/-- `e''(w) = 12 i w²` for `e(w) = i w⁴`. -/
theorem hasDerivAt_quartic' (w : ℂ) :
    HasDerivAt (fun w : ℂ => 4 * I * w ^ 3) (12 * I * w ^ 2) w :=
  ((hasDerivAt_pow 3 w).const_mul (4 * I)).congr_deriv (by norm_num; ring)

/-- The phase `i x⁴` is smooth. -/
theorem contDiff_quarticPhase : ContDiff ℝ ∞ quarticPhase := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  exact contDiff_const.mul (hL.pow 4)

/-- `Im (i x⁴) = x⁴`. -/
theorem im_quarticPhase (x : Fin 1 → ℝ) : (quarticPhase x).im = x 0 ^ 4 := by
  simp [quarticPhase, ← ofReal_pow]

/-- `0` is a critical point of `i x⁴`. -/
theorem fderiv_quarticPhase_zero : fderiv ℝ quarticPhase 0 = 0 := by
  have h := hasFDerivAt_comp_coord (e := fun w : ℂ => I * w ^ 4) (x := 0) (hasDerivAt_quartic _)
  rw [show (fun y : Fin 1 → ℝ => (fun w : ℂ => I * w ^ 4) (y 0 : ℂ)) = quarticPhase from rfl]
    at h
  rw [h.fderiv]
  ext
  simp

/-- The Hessian of `i x⁴` at `0` is `0`: the critical point is degenerate. -/
theorem hessMat_quarticPhase : hessMat quarticPhase 0 = 0 := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv quarticPhase 0 y) =
      fun y => (fun w : ℂ => 4 * I * w ^ 3) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (hasDerivAt_quartic _) 0
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_quartic' _)]
  simp

/-- The integrand of `∫ a e^{iτ · i x⁴}` is real: `e^{iτ · i x⁴} = e^{-τ x⁴}`. -/
theorem exp_quarticPhase (τ : ℝ) (x : Fin 1 → ℝ) :
    cexp (I * τ * quarticPhase x) = (Real.exp (-(τ * x 0 ^ 4)) : ℂ) := by
  rw [ofReal_exp]
  congr 1
  simp only [quarticPhase, ofReal_neg, ofReal_mul, ofReal_pow]
  ring_nf
  rw [I_sq]
  ring

/-- Lower bound for the degenerate phase: for `τ ≥ 16`,
`∫ a e^{-τ x⁴} ≥ 2 e^{-1} τ^{-1/4}`, where `a` is the bump of radius `1`. On
`|x| ≤ τ^{-1/4} ≤ 1/2` the bump is `1` and `e^{-τx⁴} ≥ e^{-1}`. -/
theorem integral_quartic_lower {τ : ℝ} (hτ : 16 ≤ τ) :
    2 * Real.exp (-1) * τ ^ (-(1 / 4 : ℝ)) ≤
      ∫ x : Fin 1 → ℝ, smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) := by
  have hτ0 : 0 < τ := by linarith
  set r := τ ^ (-(1 / 4 : ℝ)) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hτ0.le _
  have hr4 : τ * r ^ 4 = 1 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hτ0.le,
      show (-(1 / 4 : ℝ)) * ((4 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ hτ0.ne']
  have hr_half : r ≤ 1 / 2 := by
    have h16 : (16 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [hr, ← h16]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hτ (by norm_num)
  have hnn : ∀ x : Fin 1 → ℝ, 0 ≤ smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) :=
    fun x => mul_nonneg (smallBump one_pos).nonneg (Real.exp_pos _).le
  have hint : Integrable fun x : Fin 1 → ℝ => smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (smallBump one_pos).continuous.mul (Real.continuous_exp.comp (by fun_prop))
    · exact (smallBump one_pos).hasCompactSupport.mul_right
  have hball : ∀ x ∈ Metric.closedBall (0 : Fin 1 → ℝ) r,
      Real.exp (-1) ≤ smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) := by
    intro x hx
    have hx' : ‖x‖ ≤ r := by simpa using hx
    have h1 : smallBump one_pos x = 1 :=
      (smallBump one_pos).one_of_mem_closedBall (by
        simp only [Metric.mem_closedBall, dist_zero_right]
        show ‖x‖ ≤ 1 / 2
        linarith)
    have hx0 : |x 0| ≤ r := by
      have := (norm_le_pi_norm x 0).trans hx'
      rwa [Real.norm_eq_abs] at this
    have h4 : x 0 ^ 4 ≤ r ^ 4 := by
      rw [show x 0 ^ 4 = |x 0| ^ 4 by rw [pow_abs, abs_of_nonneg (by positivity)]]
      exact pow_le_pow_left₀ (abs_nonneg _) hx0 4
    rw [h1, one_mul]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hvol : (volume : Measure (Fin 1 → ℝ)).real (Metric.closedBall 0 r) = 2 * r := by
    rw [measureReal_def, Real.volume_pi_closedBall _ hr0, Fintype.card_fin, pow_one,
      ENNReal.toReal_ofReal (by positivity)]
  have hs := setIntegral_ge_of_const_le_real (μ := volume) Metric.isClosed_closedBall.measurableSet
    measure_closedBall_lt_top.ne hball hint.integrableOn
  rw [hvol] at hs
  calc 2 * Real.exp (-1) * r = Real.exp (-1) * (2 * r) := by ring
    _ ≤ _ := hs
    _ ≤ _ := setIntegral_le_integral hint (Eventually.of_forall hnn)

/-- For the degenerate phase `i x⁴` and the bump `a` of radius `1`, no term `(2π/τ)^{1/2} c`,
whatever the constant `c`, approximates `∫ a e^{iτφ}` up to `O(τ^{-3/2})`: the integral is
`≥ 2 e^{-1} τ^{-1/4}`, which decays more slowly than `τ^{-1/2}`. -/
theorem quarticPhase_not_isBigO (c : ℂ) :
    ¬ (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (I * τ * quarticPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * c) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  -- the leading term is `O(τ^{-1/2})`, so the integral is too
  have hlead : (fun τ : ℝ => (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * c) =O[atTop]
      fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) := by
    refine IsBigO.of_bound ((2 * π) ^ (1 / 2 : ℝ) * ‖c‖) ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity), Nat.cast_one,
      Real.div_rpow (by positivity) hτ.le, Real.rpow_neg hτ.le, div_eq_mul_inv]
    ring_nf
    rfl
  have herr : (fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1)) =O[atTop]
      fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with τ hτ
    have hτ0 : 0 < τ := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hτ0.le _), Real.norm_of_nonneg
      (Real.rpow_nonneg hτ0.le _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le hτ (by norm_num)
  have hI := (h.trans herr).add hlead
  obtain ⟨C, hC⟩ := hI.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC
  -- pick `τ` large enough that `2 e^{-1} τ^{-1/4} > C τ^{-1/2}`
  set τ := max (max T 16) ((C * Real.exp 1 + 1) ^ 4) with hτdef
  have hτ16 : 16 ≤ τ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hτ0 : 0 < τ := by linarith
  have hbound := hT τ (le_trans (le_max_left _ _) (le_max_left _ _))
  have hval : (∫ x, smallAmp one_pos x * cexp (I * τ * quarticPhase x)) =
      ((∫ x : Fin 1 → ℝ, smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [exp_quarticPhase, smallAmp, ofReal_mul]
  have hlow := integral_quartic_lower hτ16
  have hInn : 0 ≤ ∫ x : Fin 1 → ℝ, smallBump one_pos x * Real.exp (-(τ * x 0 ^ 4)) :=
    le_trans (by positivity) hlow
  rw [sub_add_cancel, hval, norm_real, Real.norm_of_nonneg hInn,
    Real.norm_of_nonneg (Real.rpow_nonneg hτ0.le _)] at hbound
  set q := τ ^ (-(1 / 4 : ℝ)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hτ0 _
  have hsplit : τ ^ (-(1 / 2 : ℝ)) = q * q := by
    rw [hq, ← Real.rpow_add hτ0]
    norm_num
  have h2 : 2 * Real.exp (-1) * q ≤ C * q * q := by
    rw [mul_assoc C, ← hsplit]
    linarith
  have key : 2 * Real.exp (-1) ≤ C * q := le_of_mul_le_mul_right h2 hq0
  have he0 := Real.exp_pos (-1)
  rcases le_or_gt C 0 with hC | hC
  · nlinarith
  · have hτq : C * Real.exp 1 + 1 ≤ τ ^ (1 / 4 : ℝ) := by
      have hb : 0 ≤ C * Real.exp 1 + 1 := by positivity
      calc C * Real.exp 1 + 1 = ((C * Real.exp 1 + 1) ^ 4) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
            norm_num
        _ ≤ τ ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by norm_num)
    have hp0 : 0 < τ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hτ0 _
    have hqp : q * τ ^ (1 / 4 : ℝ) = 1 := by
      rw [hq, Real.rpow_neg hτ0.le, inv_mul_cancel₀ hp0.ne']
    have he : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 : 2 * Real.exp (-1) * τ ^ (1 / 4 : ℝ) ≤ C := by
      have := mul_le_mul_of_nonneg_right key hp0.le
      rwa [mul_assoc C, hqp, mul_one] at this
    have h4 : Real.exp (-1) * (C * Real.exp 1 + 1) = C + Real.exp (-1) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (Real.exp (-1)) C, mul_assoc, he, mul_one]
    have h5 := mul_le_mul_of_nonneg_left hτq he0.le
    linarith

/-- The transported phase `i x⁴` has `0` as its only critical point. -/
theorem critical_toEuc_quarticPhase (x : EuclideanSpace ℝ (Fin 1)) :
    ((toEuc quarticPhase x).im = 0 ∧ fderiv ℝ (toEuc quarticPhase) x = 0) ↔
      x ∈ ({0} : Finset (EuclideanSpace ℝ (Fin 1))) := by
  rw [Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    have h0 : WithLp.ofLp x = 0 := by
      funext i
      rw [Subsingleton.elim i 0]
      exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp ((im_quarticPhase _).symm.trans h)
    rw [← WithLp.toLp_ofLp (x := x), h0, WithLp.toLp_zero]
  · rintro rfl
    refine ⟨by simp [toEuc, quarticPhase], ?_⟩
    exact (fderiv_ofEuc_eq_zero_iff (toEuc quarticPhase) 0).mp fderiv_quarticPhase_zero

/-- The Hessian of the transported phase `i x⁴` at `0` is `0`. -/
theorem hess_toEuc_quarticPhase : hess (toEuc quarticPhase) 0 = 0 :=
  (hessMat_ofEuc (toEuc quarticPhase) 0).symm.trans hessMat_quarticPhase

/-- The nondegeneracy hypothesis of `stationary_phase_of_isOpen` fails for `i x⁴` at `0`. -/
theorem det_hess_toEuc_quarticPhase : (-I • hess (toEuc quarticPhase) 0).det = 0 := by
  rw [hess_toEuc_quarticPhase]
  simp

/-- Wrong input: the nondegeneracy hypothesis of `stationary_phase_of_isOpen` cannot be dropped.
For the phase `i x⁴` on `ℝ¹` and the bump of radius `1`, every other hypothesis holds (with
`U = ℝ¹` and `K = {0}`) but the conclusion fails: the integral decays like `τ^{-1/4}`
(`quarticPhase_not_isBigO`). -/
theorem stationary_phase_needs_nondegenerate :
    ¬ ∀ (φ a : EuclideanSpace ℝ (Fin 1) → ℂ), ContDiff ℝ ∞ φ → ContDiff ℝ ∞ a →
      HasCompactSupport a → (∀ x, 0 ≤ (φ x).im) → ∀ K : Finset (EuclideanSpace ℝ (Fin 1)),
      (∀ x ∈ tsupport a, ((φ x).im = 0 ∧ fderiv ℝ φ x = 0) ↔ x ∈ K) →
      (∀ x ∈ K, x ∈ tsupport a) →
      (fun lam : ℝ => (∫ x, a x * cexp (I * lam * φ x)) -
          ∑ x₀ ∈ K, cexp (I * lam * φ x₀) * ((2 * π / lam) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) *
            invSqrtDet (-I • hess φ x₀) * a x₀)
        =O[atTop] fun lam : ℝ => lam ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  have ha0 : toEuc (smallAmp one_pos) 0 = 1 := smallAmp_zero one_pos
  have h1 := h (toEuc quarticPhase) (toEuc (smallAmp one_pos))
    (contDiff_toEuc contDiff_quarticPhase) (contDiff_toEuc (contDiff_smallAmp one_pos))
    (hasCompactSupport_toEuc (hasCompactSupport_smallAmp one_pos))
    (fun x => le_trans (by positivity) (im_quarticPhase (WithLp.ofLp x)).ge) {0}
    (fun x _ => critical_toEuc_quarticPhase x)
    (fun x hx => by
      rw [Finset.mem_singleton.mp hx]
      exact subset_tsupport _ (by simp [Function.mem_support, ha0]))
  have hφ0 : toEuc quarticPhase 0 = 0 := by simp [toEuc, quarticPhase]
  simp only [Finset.sum_singleton, hφ0, mul_zero, Complex.exp_zero, one_mul, ha0,
    mul_one] at h1
  refine quarticPhase_not_isBigO (invSqrtDet (-I • hess (toEuc quarticPhase) 0)) ?_
  refine h1.congr_left fun τ => ?_
  rw [integral_ofEuc]
  rfl

/-! ### Non-vacuity with two critical points -/

/-- `P(w) = w³/3 − w + i (w⁴ − 2w² + 1)`; on the real line `Im P = (x² − 1)²`. -/
noncomputable def twoPoly (w : ℂ) : ℂ := w ^ 3 / 3 - w + I * (w ^ 4 - 2 * w ^ 2 + 1)

/-- The phase `φ(x) = P(x)` on `ℝ¹`, with critical points `±1`. -/
noncomputable def twoPhase (x : Fin 1 → ℝ) : ℂ := twoPoly (x 0 : ℂ)

/-- `P'(w) = w² − 1 + i (4w³ − 4w) = (w² − 1)(1 + 4iw)`. -/
theorem hasDerivAt_twoPoly (w : ℂ) :
    HasDerivAt twoPoly (w ^ 2 - 1 + I * (4 * w ^ 3 - 4 * w)) w := by
  have := (((hasDerivAt_pow 3 w).div_const 3).sub (hasDerivAt_id' w)).add
    ((((hasDerivAt_pow 4 w).sub ((hasDerivAt_pow 2 w).const_mul 2)).add_const 1).const_mul I)
  exact this.congr_deriv (by norm_num; ring)

/-- `P''(w) = 2w + i (12w² − 4)`. -/
theorem hasDerivAt_twoPoly' (w : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ 2 - 1 + I * (4 * w ^ 3 - 4 * w))
      (2 * w + I * (12 * w ^ 2 - 4)) w := by
  have := ((hasDerivAt_pow 2 w).sub_const 1).add
    ((((hasDerivAt_pow 3 w).const_mul 4).sub ((hasDerivAt_id' w).const_mul 4)).const_mul I)
  exact this.congr_deriv (by norm_num; ring)

/-- The two-point phase is smooth. -/
theorem contDiff_twoPhase : ContDiff ℝ ∞ twoPhase := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  exact ((hL.pow 3).div_const 3 |>.sub hL).add
    (contDiff_const.mul (((hL.pow 4).sub (contDiff_const.mul (hL.pow 2))).add contDiff_const))

/-- `Im φ(x) = (x² − 1)²`. -/
theorem im_twoPhase (x : Fin 1 → ℝ) : (twoPhase x).im = (x 0 ^ 2 - 1) ^ 2 := by
  rw [show twoPhase x = ((x 0 ^ 3 / 3 - x 0 : ℝ) : ℂ) + I * (((x 0 ^ 2 - 1) ^ 2 : ℝ) : ℂ) by
    simp only [twoPhase, twoPoly]
    push_cast
    ring]
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]

/-- The partial derivative at a point with `x² = 1` vanishes. -/
theorem fderiv_twoPhase_eq_zero {x : Fin 1 → ℝ} (hx : x 0 ^ 2 = 1) : fderiv ℝ twoPhase x = 0 := by
  have hc : ((x 0 : ℂ)) ^ 2 = 1 := by exact_mod_cast hx
  have he : (x 0 : ℂ) ^ 2 - 1 + I * (4 * (x 0 : ℂ) ^ 3 - 4 * (x 0 : ℂ)) = 0 := by
    linear_combination (1 + 4 * I * (x 0 : ℂ)) * hc
  have h := hasFDerivAt_comp_coord (e := twoPoly) (x := x) (hasDerivAt_twoPoly _)
  rw [show (fun y : Fin 1 → ℝ => twoPoly (y 0 : ℂ)) = twoPhase from rfl, he] at h
  rw [h.fderiv]
  ext
  simp

/-- The Hessian of the two-point phase: the `1 × 1` matrix `P''(x)`. -/
theorem hessMat_twoPhase (x : Fin 1 → ℝ) (i j : Fin 1) :
    hessMat twoPhase x i j = 2 * (x 0 : ℂ) + I * (12 * (x 0 : ℂ) ^ 2 - 4) := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv twoPhase 0 y) =
      fun y => (fun w : ℂ => w ^ 2 - 1 + I * (4 * w ^ 3 - 4 * w)) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (hasDerivAt_twoPoly _) 0
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_twoPoly' _)]

/-- At a point with `x = s`, `-i · Hess φ` is the diagonal matrix `-i P''(s)`. -/
theorem neg_I_hessMat_twoPhase {x : Fin 1 → ℝ} {s : ℝ} (hx : x 0 = s) :
    -I • hessMat twoPhase x = diagonal fun _ => -I * (2 * s + I * (12 * s ^ 2 - 4)) := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [hessMat_twoPhase, hx]

/-- The bump `smallAmp` equals `1` on `closedBall 0 (δ/2)`. -/
theorem smallAmp_eq_one {δ : ℝ} (hδ : 0 < δ) {x : Fin 1 → ℝ} (hx : ‖x‖ ≤ δ / 2) :
    smallAmp hδ x = 1 := by
  have hm : x ∈ Metric.closedBall (0 : Fin 1 → ℝ) (smallBump hδ).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hx
  simp [smallAmp, (smallBump hδ).one_of_mem_closedBall hm]

/-- The point `x = 1` of `ℝ¹`. -/
noncomputable def ptOne : Fin 1 → ℝ := fun _ => 1

/-- The point `x = -1` of `ℝ¹`. -/
noncomputable def ptNegOne : Fin 1 → ℝ := fun _ => -1

/-- Non-vacuity of the sum over critical points: for `φ(x) = x³/3 − x + i (x² − 1)²` on `ℝ¹`,
whose critical points are `x = ±1` with `φ(±1) = ∓2/3` and `-i P''(±1) = 8 ∓ 2i`, and the bump of
radius `2` (equal to `1` on `[-1, 1]`),
`∫ a e^{iτφ} = (2π/τ)^{1/2} (e^{-2iτ/3} (8 − 2i)^{-1/2} + e^{2iτ/3} (8 + 2i)^{-1/2}) + O(τ^{-3/2})`.
Both critical points contribute, each with its own phase `e^{iτφ(x₀)}`. -/
theorem stationary_phase_twoPhase :
    (fun τ : ℝ => (∫ x, smallAmp two_pos x * cexp (I * τ * twoPhase x)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) *
          (cexp (-(2 / 3 * I * τ)) * (8 - 2 * I) ^ (-(1 / 2 : ℂ)) +
            cexp (2 / 3 * I * τ) * (8 + 2 * I) ^ (-(1 / 2 : ℂ)))) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  have hn1 : ‖ptOne‖ ≤ 2 / 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => by
    simp [ptOne]
  have hn2 : ‖ptNegOne‖ ≤ 2 / 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => by
    simp [ptNegOne]
  have ha1 := smallAmp_eq_one two_pos hn1
  have ha2 := smallAmp_eq_one two_pos hn2
  have hpm : ptOne ≠ ptNegOne := fun h => by
    have := congrFun h 0
    simp [ptOne, ptNegOne] at this
    linarith
  have hφ1 : twoPhase ptOne = -(2 / 3) := by
    simp only [twoPhase, twoPoly, ptOne]
    push_cast
    ring
  have hφ2 : twoPhase ptNegOne = 2 / 3 := by
    simp only [twoPhase, twoPoly, ptNegOne]
    push_cast
    ring
  have hd1 : -I • hessMat twoPhase ptOne = diagonal fun _ => 8 - 2 * I := by
    rw [neg_I_hessMat_twoPhase (s := 1) rfl]
    congr 1
    funext
    push_cast
    linear_combination (-8) * I_sq
  have hd2 : -I • hessMat twoPhase ptNegOne = diagonal fun _ => 8 + 2 * I := by
    rw [neg_I_hessMat_twoPhase (s := -1) rfl]
    congr 1
    funext
    push_cast
    linear_combination (-8) * I_sq
  have hK : ∀ x ∈ tsupport (smallAmp two_pos),
      ((twoPhase x).im = 0 ∧ fderiv ℝ twoPhase x = 0) ↔ x ∈ ({ptOne, ptNegOne} : Finset _) := by
    intro x _
    rw [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      rw [im_twoPhase] at h
      have hx2 : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith [sq_nonneg (x 0 ^ 2 - 1)]
      rcases mul_eq_zero.mp hx2 with h1 | h1
      · left
        funext i
        rw [Subsingleton.elim i 0]
        simp only [ptOne]
        linarith
      · right
        funext i
        rw [Subsingleton.elim i 0]
        simp only [ptNegOne]
        linarith
    · rintro (rfl | rfl)
      · exact ⟨by rw [hφ1]; simp, fderiv_twoPhase_eq_zero (by simp [ptOne])⟩
      · exact ⟨by rw [hφ2]; simp, fderiv_twoPhase_eq_zero (by simp [ptNegOne])⟩
  have h := stationary_phase_pi_of_isOpen contDiff_twoPhase (contDiff_smallAmp two_pos)
    (hasCompactSupport_smallAmp two_pos) isOpen_univ (Set.subset_univ _)
    (fun x _ => by rw [im_twoPhase]; positivity) {ptOne, ptNegOne} hK
    (fun x hx => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact subset_tsupport _ (by simp [Function.mem_support, ha1])
      · exact subset_tsupport _ (by simp [Function.mem_support, ha2]))
    (fun x hx => by
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hd1, det_diagonal, Fin.prod_univ_one]
        intro h0
        simpa using congrArg Complex.re h0
      · rw [hd2, det_diagonal, Fin.prod_univ_one]
        intro h0
        simpa using congrArg Complex.re h0)
  simp only [Finset.sum_pair hpm, hφ1, hφ2, hd1, hd2, invSqrtDet_diagonal, Fin.prod_univ_one,
    ha1, ha2, mul_one] at h
  refine h.congr_left fun τ => ?_
  rw [show I * (τ : ℂ) * -(2 / 3) = -(2 / 3 * I * τ) by ring,
    show I * (τ : ℂ) * (2 / 3) = 2 / 3 * I * τ by ring]
  ring

/-! ### Non-vacuity: a critical point on the boundary of the support -/

/-- `P(w) = w²/2 + i w³`; on the real line `Im P = x³`, negative for `x < 0`. -/
noncomputable def edgePoly (w : ℂ) : ℂ := w ^ 2 / 2 + I * w ^ 3

/-- The phase `φ(x) = x²/2 + i x³` on `ℝ¹`. -/
noncomputable def edgePhase (x : Fin 1 → ℝ) : ℂ := edgePoly (x 0 : ℂ)

/-- The amplitude `a(x) = ψ(x) ψ(1 − x)` with `ψ = expNegInvGlue`: smooth, supported on `[0, 1]`,
and flat at both ends. -/
noncomputable def edgeAmp (x : Fin 1 → ℝ) : ℂ :=
  ((expNegInvGlue (x 0) * expNegInvGlue (1 - x 0) : ℝ) : ℂ)

/-- `P'(w) = w + 3i w²`. -/
theorem hasDerivAt_edgePoly (w : ℂ) : HasDerivAt edgePoly (w + 3 * I * w ^ 2) w := by
  have := ((hasDerivAt_pow 2 w).div_const 2).add ((hasDerivAt_pow 3 w).const_mul I)
  exact this.congr_deriv (by norm_num; ring)

/-- `P''(w) = 1 + 6i w`. -/
theorem hasDerivAt_edgePoly' (w : ℂ) :
    HasDerivAt (fun w : ℂ => w + 3 * I * w ^ 2) (1 + 6 * I * w) w := by
  have := (hasDerivAt_id' w).add ((hasDerivAt_pow 2 w).const_mul (3 * I))
  exact this.congr_deriv (by norm_num; ring)

/-- The edge phase is smooth. -/
theorem contDiff_edgePhase : ContDiff ℝ ∞ edgePhase := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  exact ((hL.pow 2).div_const 2).add (contDiff_const.mul (hL.pow 3))

/-- `Im φ(x) = x³`. -/
theorem im_edgePhase (x : Fin 1 → ℝ) : (edgePhase x).im = x 0 ^ 3 := by
  rw [show edgePhase x = ((x 0 ^ 2 / 2 : ℝ) : ℂ) + I * ((x 0 ^ 3 : ℝ) : ℂ) by
    simp only [edgePhase, edgePoly]
    push_cast
    ring]
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]

/-- `0` is a critical point of the edge phase. -/
theorem fderiv_edgePhase_zero : fderiv ℝ edgePhase 0 = 0 := by
  have h := hasFDerivAt_comp_coord (e := edgePoly) (x := (0 : Fin 1 → ℝ))
    (hasDerivAt_edgePoly _)
  rw [show (fun y : Fin 1 → ℝ => edgePoly (y 0 : ℂ)) = edgePhase from rfl] at h
  rw [h.fderiv]
  ext
  simp

/-- The Hessian of the edge phase at `0` is `1`. -/
theorem hessMat_edgePhase : hessMat edgePhase 0 = 1 := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv edgePhase 0 y) =
      fun y => (fun w : ℂ => w + 3 * I * w ^ 2) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (hasDerivAt_edgePoly _) 0
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_edgePoly' _)]
  simp

/-- The edge amplitude is smooth. -/
theorem contDiff_edgeAmp : ContDiff ℝ ∞ edgeAmp := by
  have hc : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => y 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
  have hg : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff (n := ⊤)
  exact ofRealCLM.contDiff.comp ((hg.comp hc).mul (hg.comp (contDiff_const.sub hc)))

/-- The edge amplitude vanishes for `x < 0` and for `x > 1`. -/
theorem edgeAmp_eq_zero {x : Fin 1 → ℝ} (hx : x 0 ≤ 0 ∨ 1 ≤ x 0) : edgeAmp x = 0 := by
  rcases hx with hx | hx
  · simp [edgeAmp, expNegInvGlue.zero_of_nonpos hx]
  · simp [edgeAmp, expNegInvGlue.zero_of_nonpos (show 1 - x 0 ≤ 0 by linarith)]

/-- The edge amplitude has compact support. -/
theorem hasCompactSupport_edgeAmp : HasCompactSupport edgeAmp := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 1 → ℝ) 1) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one] at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  replace hi := not_le.mp hi
  rw [Subsingleton.elim i 0, Real.norm_eq_abs] at hi
  refine edgeAmp_eq_zero ?_
  rcases le_or_gt (x 0) 0 with h | h
  · exact Or.inl h
  · rw [abs_of_pos h] at hi
    exact Or.inr hi.le

/-- The support of the edge amplitude lies in `x ≥ 0`. -/
theorem tsupport_edgeAmp_subset : tsupport edgeAmp ⊆ {x | 0 ≤ x 0} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const (continuous_apply 0))
  by_contra h
  exact hx (edgeAmp_eq_zero (Or.inl (not_le.mp h).le))

/-- `0` lies in the support of the edge amplitude, on its boundary. -/
theorem zero_mem_tsupport_edgeAmp : (0 : Fin 1 → ℝ) ∈ tsupport edgeAmp := by
  rw [tsupport, Metric.mem_closure_iff]
  intro ε hε
  set t := min (ε / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  refine ⟨fun _ => t, ?_, ?_⟩
  · rw [Function.mem_support, edgeAmp, ofReal_ne_zero]
    exact (mul_pos (expNegInvGlue.pos_of_pos ht0)
      (expNegInvGlue.pos_of_pos (by linarith))).ne'
  · rw [dist_zero_left, pi_norm_const, Real.norm_eq_abs, abs_of_pos ht0]
    exact (min_le_left _ _).trans_lt (by linarith)

/-- The edge amplitude vanishes at the critical point `0`. -/
theorem edgeAmp_zero : edgeAmp 0 = 0 := edgeAmp_eq_zero (Or.inl le_rfl)

/-- Hörmander's hypothesis fails for the edge example: no open set containing the support of the
amplitude has `Im φ ≥ 0`, since `Im φ(x) = x³ < 0` for `x < 0` arbitrarily close to `0`. So
`stationary_phase_pi_of_isOpen` does not apply, while `stationary_phase_pi` does
(`stationary_phase_edge`). -/
theorem edgePhase_not_isOpen : ¬ ∃ U : Set (Fin 1 → ℝ), IsOpen U ∧ tsupport edgeAmp ⊆ U ∧
    ∀ x ∈ U, 0 ≤ (edgePhase x).im := by
  rintro ⟨U, hU, haU, hIm⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU 0 (haU zero_mem_tsupport_edgeAmp)
  have hx : (fun _ => -(ε / 2) : Fin 1 → ℝ) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    linarith
  have := hIm _ (hεU hx)
  rw [im_edgePhase] at this
  have h3 : 0 < (ε / 2) ^ 3 := by positivity
  nlinarith

/-- Non-vacuity of the boundary case: for `φ(x) = x²/2 + i x³` and `a(x) = ψ(x) ψ(1 − x)`,
supported on `[0, 1]`, the only critical point `0` is on the boundary of the support, where
`a` is flat, and `Im φ ≥ 0` holds on the support but on no open set around it
(`edgePhase_not_isOpen`). `stationary_phase_pi` gives `∫ a e^{iτφ} = O(τ^{-3/2})`: the leading
term `(2π/τ)^{1/2} e^{iπ/4} a(0)` is `0`. -/
theorem stationary_phase_edge :
    (fun τ : ℝ => ∫ x, edgeAmp x * cexp (I * τ * edgePhase x)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  have hK : ∀ x ∈ tsupport edgeAmp,
      ((edgePhase x).im = 0 ∧ fderiv ℝ edgePhase x = 0) ↔ x ∈ ({0} : Finset _) := by
    intro x _
    rw [Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩
      rw [im_edgePhase, pow_eq_zero_iff three_ne_zero] at h
      funext i
      rw [Subsingleton.elim i 0, h]
      rfl
    · rintro rfl
      exact ⟨by rw [im_edgePhase]; simp, fderiv_edgePhase_zero⟩
  have h := stationary_phase_pi contDiff_edgePhase contDiff_edgeAmp hasCompactSupport_edgeAmp
    (fun x hx => by
      rw [im_edgePhase]
      exact pow_nonneg (tsupport_edgeAmp_subset hx) 3)
    {0} hK (fun x hx => by rw [Finset.mem_singleton.mp hx]; exact zero_mem_tsupport_edgeAmp)
    (fun x hx => by
      rw [Finset.mem_singleton.mp hx, hessMat_edgePhase, smul_one_eq_diagonal, det_diagonal,
        Fin.prod_univ_one]
      exact neg_ne_zero.mpr I_ne_zero)
  simp only [Finset.sum_singleton, edgeAmp_zero, mul_zero, sub_zero] at h
  exact h

end Lightlike.Oscillatory
