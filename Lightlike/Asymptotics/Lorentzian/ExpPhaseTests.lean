import Lightlike.Asymptotics.Lorentzian.ExpPhase
import Lightlike.Oscillatory.PhaseReductionTests
import Lightlike.Oscillatory.GaussianTests

/-!
# Trust checks for the `e^{τ S}` stationary phase

* **Non-vacuity** (`expPhase_gauss`): the Gaussian action `S(x) = -x²/2` on `ℝ¹` with a bump
  amplitude satisfies every hypothesis of `expPhase_asymptotics`: smooth, `Re S ≤ 0`, the critical
  set is `{0}`, and `-∂²S = 1` is invertible. The conclusion is
  `∫ a e^{τS} = (2π/τ)^{1/2} + O(τ^{-3/2})`.
* **Wrong sign** (`expPhase_gauss_wrong_sign`): with the Hessian entering as `+∂²S` instead of
  `-∂²S` the leading coefficient would be `invSqrtDet (-1) ≠ 1`, and the same asymptotic
  statement is false for it (`invSqrtDet_neg_one_ne_one`).
* **Wrong constant** (`expPhase_gauss_wrong_constant`): any other leading coefficient `c ≠ 1`
  makes the statement false, so the constant of the theorem is determined.
-/

open Complex Filter Asymptotics Lightlike.Oscillatory
open scoped Real ContDiff Topology

namespace Lightlike.Asymptotics.Lorentzian

/-- `e(w) = -w²/2` has derivative `-w`. -/
theorem hasDerivAt_gaussPoly (w : ℂ) : HasDerivAt (fun w : ℂ => -(w ^ 2) / 2) (-w) w := by
  have := ((hasDerivAt_pow 2 w).neg.div_const 2)
  exact this.congr_deriv (by norm_num; ring)

/-- `e'(w) = -w` has derivative `-1`. -/
theorem hasDerivAt_gaussPoly' (w : ℂ) : HasDerivAt (fun w : ℂ => -w) (-1) w :=
  (hasDerivAt_id w).neg

/-- The Gaussian action is smooth. -/
theorem contDiff_gaussAction : ContDiff ℝ ∞ gaussAction := by
  have hL : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => ((y 0 : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff
  exact ((hL.pow 2).neg).div_const 2

/-- `0` is a critical point of the Gaussian action. -/
theorem fderiv_gaussAction_zero : fderiv ℝ gaussAction 0 = 0 := by
  have h := hasFDerivAt_comp_coord (e := fun w : ℂ => -(w ^ 2) / 2) (x := 0)
    (hasDerivAt_gaussPoly _)
  rw [show (fun y : Fin 1 → ℝ => (fun w : ℂ => -(w ^ 2) / 2) (y 0 : ℂ)) = gaussAction from rfl]
    at h
  rw [h.fderiv]
  ext
  simp

/-- The Hessian of the Gaussian action is `-1`. -/
theorem hessMat_gaussAction (x : Fin 1 → ℝ) : hessMat gaussAction x = -1 := by
  have h1 : (fun y : Fin 1 → ℝ => coordDeriv gaussAction 0 y) =
      fun y => (fun w : ℂ => -w) (y 0 : ℂ) :=
    funext fun y => coordDeriv_comp_coord (e := fun w : ℂ => -(w ^ 2) / 2)
      (hasDerivAt_gaussPoly _) 0
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [hessMat, h1]
  rw [coordDeriv_comp_coord (hasDerivAt_gaussPoly' _)]
  simp

/-- **Non-vacuity.** For the Gaussian action and the bump of radius `1`, all hypotheses of
`expPhase_asymptotics` hold, and `∫ a e^{τS} = (2π/τ)^{1/2} + O(τ^{-3/2})`. -/
theorem expPhase_gauss :
    (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (τ * gaussAction x)) -
      ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  have h := expPhase_asymptotics (S := gaussAction) (a := smallAmp one_pos) (K := {0})
    contDiff_gaussAction (contDiff_smallAmp one_pos)
    (by
      have := (smallBump one_pos).hasCompactSupport
      exact (this.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero))
    (fun x _ => gaussAction_re_nonpos x)
    (fun x hx => by
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨h1, -⟩
        funext i
        rw [Subsingleton.elim i 0]
        exact gaussAction_re_eq_zero h1
      · rintro rfl
        exact ⟨by simp [gaussAction], fderiv_gaussAction_zero⟩)
    (fun x hx => by
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact subset_tsupport _ (show smallAmp one_pos 0 ≠ 0 by
        rw [smallAmp_zero]; exact one_ne_zero))
    (fun x hx => by
      simp only [Finset.mem_singleton] at hx
      subst hx
      rw [hessMat_gaussAction]
      simp)
  simpa [hessMat_gaussAction, smallAmp_zero, invSqrtDet_one, gaussAction] using h

/-- **Wrong constant.** Any leading coefficient `c ≠ 1` makes the statement of `expPhase_gauss`
false: the constant `invSqrtDet (-hessMat S 0) = 1` of the theorem is determined by the
asymptotics. -/
theorem expPhase_gauss_wrong_constant {c : ℂ} (hc : c ≠ 1) :
    ¬ (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (τ * gaussAction x)) -
      ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * c) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  have h2 := (expPhase_gauss.sub h)
  have h3 : (fun τ : ℝ => (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * (c - 1)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
    refine h2.congr_left fun τ => ?_
    ring
  exact hc (sub_eq_zero.mp (coeff_eq_zero_of_isBigO h3))

/-- `invSqrtDet (-1) ≠ 1` on `ℝ¹`: the inverse square root of `-1` is `∓ i`. -/
theorem invSqrtDet_neg_one_ne_one : invSqrtDet (-1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 1 := by
  intro h
  have hd : (-1 : Matrix (Fin 1) (Fin 1) ℂ) = Matrix.diagonal (fun _ => (-1 : ℂ)) := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp
  rw [hd, invSqrtDet_diagonal] at h
  simp only [Finset.univ_unique, Finset.prod_singleton] at h
  have h2 := congrArg (· ^ 2) h
  simp only [one_pow] at h2
  rw [← cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(1 / 2) = -1 by norm_num, cpow_neg_one] at h2
  norm_num at h2

/-- **Wrong sign.** With the Hessian entering as `+∂²S` instead of `-∂²S`, the coefficient would
be `invSqrtDet (-1)`, and the asymptotic statement of the Gaussian instance is false. -/
theorem expPhase_gauss_wrong_sign :
    ¬ (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (τ * gaussAction x)) -
      ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * invSqrtDet (hessMat gaussAction 0)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  rw [hessMat_gaussAction]
  exact expPhase_gauss_wrong_constant invSqrtDet_neg_one_ne_one

/-! ### Swapped constants -/

/-- If `sin (nθ) → 0` along the integers then `sin θ = 0`: consecutive terms give
`|sin θ| ≤ |sin ((n+1)θ)| + |sin (nθ)|`. -/
theorem sin_eq_zero_of_tendsto {θ : ℝ}
    (h : Tendsto (fun n : ℕ => Real.sin (n * θ)) atTop (nhds 0)) : Real.sin θ = 0 := by
  have h1 : Tendsto (fun n : ℕ => Real.sin (((n + 1 : ℕ) : ℝ) * θ)) atTop (nhds 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| + |Real.sin (n * θ)|)
      atTop (nhds 0) := by
    simpa using h1.abs.add h.abs
  have hb : ∀ n : ℕ, |Real.sin θ| ≤ |Real.sin (((n + 1 : ℕ) : ℝ) * θ)| + |Real.sin (n * θ)| :=
    fun n => by
    have : Real.sin θ = Real.sin (((n + 1 : ℕ) : ℝ) * θ) * Real.cos (n * θ) -
        Real.cos (((n + 1 : ℕ) : ℝ) * θ) * Real.sin (n * θ) := by
      rw [← Real.sin_sub]; congr 1; push_cast; ring_nf
    rw [this]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    · rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  have := ge_of_tendsto' h2 hb
  exact abs_nonpos_iff.mp this

/-- **Swapped constants.** For `sin θ ≠ 0` and `A₁ ≠ A₂`, the two-exponential formula
`λ^p (A₁ e^{iλθ} + A₂ e^{-iλθ})` and the one with `A₁` and `A₂` interchanged cannot both
approximate the same sequence to order `λ^{p-1}`. -/
theorem swap_constants_fails {F : ℕ → ℂ} {A₁ A₂ : ℂ} {θ p : ℝ} (hs : Real.sin θ ≠ 0)
    (hA : A₁ ≠ A₂)
    (h1 : (fun lam : ℕ => F lam - (((lam : ℝ) ^ p : ℝ) : ℂ) *
        (A₁ * cexp (I * (lam : ℝ) * θ) + A₂ * cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (p - 1))) :
    ¬ (fun lam : ℕ => F lam - (((lam : ℝ) ^ p : ℝ) : ℂ) *
        (A₂ * cexp (I * (lam : ℝ) * θ) + A₁ * cexp (-(I * (lam : ℝ) * θ))))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (p - 1)) := by
  intro h2
  obtain ⟨C, hC⟩ := (h1.sub h2).bound
  have hd : ∀ lam : ℕ, (F lam - (((lam : ℝ) ^ p : ℝ) : ℂ) *
        (A₁ * cexp (I * (lam : ℝ) * θ) + A₂ * cexp (-(I * (lam : ℝ) * θ)))) -
      (F lam - (((lam : ℝ) ^ p : ℝ) : ℂ) *
        (A₂ * cexp (I * (lam : ℝ) * θ) + A₁ * cexp (-(I * (lam : ℝ) * θ)))) =
      (((lam : ℝ) ^ p : ℝ) : ℂ) * ((A₂ - A₁) * (2 * I * (Real.sin (lam * θ) : ℂ))) := by
    intro lam
    have e1 : cexp (I * (lam : ℝ) * θ) = Real.cos (lam * θ) + Real.sin (lam * θ) * I := by
      rw [show I * (lam : ℝ) * θ = ((lam * θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have e2 : cexp (-(I * (lam : ℝ) * θ)) = Real.cos (lam * θ) - Real.sin (lam * θ) * I := by
      rw [show -(I * (lam : ℝ) * θ) = ((-(lam * θ) : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
        Real.sin_neg]
      push_cast; ring
    rw [e1, e2]; ring
  have hbound : ∀ᶠ lam : ℕ in atTop, |Real.sin (lam * θ)| ≤
      (C / (2 * ‖A₂ - A₁‖)) * ((lam : ℝ))⁻¹ := by
    filter_upwards [hC, eventually_gt_atTop 0] with lam hl hlam
    have hl0 : (0 : ℝ) < lam := by exact_mod_cast hlam
    rw [hd] at hl
    have hpos : (0 : ℝ) < (lam : ℝ) ^ p := Real.rpow_pos_of_pos hl0 _
    have hAn : 0 < ‖A₂ - A₁‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hA.symm)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _)] at hl
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      Complex.norm_ofNat, mul_one] at hl
    rw [Real.rpow_sub hl0, Real.rpow_one] at hl
    have : (lam : ℝ) ^ p * (‖A₂ - A₁‖ * (2 * |Real.sin (lam * θ)|)) ≤
        C * ((lam : ℝ) ^ p / lam) := by simpa [abs_of_pos hpos, mul_assoc] using hl
    have h3 : ‖A₂ - A₁‖ * (2 * |Real.sin (lam * θ)|) ≤ C * (lam : ℝ)⁻¹ := by
      rw [← mul_le_mul_iff_of_pos_left hpos]
      calc _ = (lam : ℝ) ^ p * (‖A₂ - A₁‖ * (2 * |Real.sin (lam * θ)|)) := by ring
        _ ≤ C * ((lam : ℝ) ^ p / lam) := this
        _ = _ := by rw [div_eq_mul_inv]; ring
    have h4 : |Real.sin (lam * θ)| * (2 * ‖A₂ - A₁‖) ≤ C * (lam : ℝ)⁻¹ := by nlinarith [h3]
    have h5 : 0 < 2 * ‖A₂ - A₁‖ := by positivity
    calc |Real.sin (lam * θ)| = |Real.sin (lam * θ)| * (2 * ‖A₂ - A₁‖) / (2 * ‖A₂ - A₁‖) := by
          field_simp
      _ ≤ C * (lam : ℝ)⁻¹ / (2 * ‖A₂ - A₁‖) := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun lam : ℕ => (C / (2 * ‖A₂ - A₁‖)) * ((lam : ℝ))⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (C / (2 * ‖A₂ - A₁‖))
  have hz : Tendsto (fun lam : ℕ => Real.sin (lam * θ)) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hbound] with lam hl
    simpa using hl
  exact hs (sin_eq_zero_of_tendsto hz)

/-! ### Dropping `Re S ≤ 0` -/

/-- The growing action `S(x) = +x²/2` on `ℝ¹`, the Gaussian with the wrong sign. -/
noncomputable def growAction : (Fin 1 → ℝ) → ℂ := fun x => ((x 0 : ℂ) ^ 2) / 2

/-- Real part of the integrand for the growing action: `b(x) e^{τ x²/2}`. -/
theorem re_grow_integrand (τ : ℝ) (x : Fin 1 → ℝ) :
    (smallAmp one_pos x * cexp (τ * growAction x)).re =
      smallBump one_pos x * Real.exp (τ * (x 0) ^ 2 / 2) := by
  have : (τ : ℂ) * growAction x = ((τ * (x 0) ^ 2 / 2 : ℝ) : ℂ) := by
    simp [growAction]; ring
  rw [this, ← Complex.ofReal_exp,
    show smallAmp one_pos x * ((Real.exp (τ * (x 0) ^ 2 / 2) : ℝ) : ℂ) =
      ((smallBump one_pos x * Real.exp (τ * (x 0) ^ 2 / 2) : ℝ) : ℂ) by simp [smallAmp]]
  exact Complex.ofReal_re _

/-- **Dropped hypothesis `Re S ≤ 0`.** For the growing action `S = +x²/2`, with the same bump
amplitude, no constant `c` makes `∫ a e^{τS} - (2π/τ)^{1/2} c` of order `τ^{-3/2}`: the
integral is at least `∫ a > 0` for `τ ≥ 0`, while the correction term tends to `0`. So the
conclusion of `expPhase_asymptotics` fails without the sign hypothesis. -/
theorem expPhase_grow_fails (c : ℂ) :
    ¬ (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (τ * growAction x)) -
      (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * c) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  have hz : Tendsto (fun τ : ℝ => (∫ x, smallAmp one_pos x * cexp (τ * growAction x)) -
      (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * c) atTop (nhds 0) := by
    refine h.trans_tendsto ?_
    have e : (-(((1 : ℕ) : ℝ) / 2) - 1) = -(3 / 2 : ℝ) := by norm_num
    rw [e]; exact tendsto_rpow_neg_atTop (by norm_num)
  have hr : Tendsto (fun τ : ℝ => (((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * c)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun τ : ℝ => 2 * π / τ) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun τ : ℝ => (2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2)) atTop (nhds 0) := by
      have h3 := (Real.continuousAt_rpow_const 0 (((1 : ℕ) : ℝ) / 2)
        (Or.inr (by norm_num))).tendsto.comp h1
      rwa [Real.zero_rpow (by norm_num)] at h3
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp h2).mul_const c
  have hI := hz.add hr
  simp only [sub_add_cancel, add_zero] at hI
  have hint : ∀ τ : ℝ, MeasureTheory.Integrable
      (fun x : Fin 1 → ℝ => smallAmp one_pos x * cexp (τ * growAction x)) := fun τ => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (contDiff_smallAmp one_pos).continuous.mul (by unfold growAction; fun_prop)
    · exact ((smallBump one_pos).hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ))
        ofReal_zero).mul_right
  have hlow : ∀ τ : ℝ, 0 ≤ τ → ∫ x, smallBump one_pos x ≤
      ‖∫ x, smallAmp one_pos x * cexp (τ * growAction x)‖ := fun τ hτ => by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ (hint τ)]
    simp only [Complex.reCLM_apply, re_grow_integrand]
    refine le_trans ?_ (le_abs_self _)
    refine MeasureTheory.integral_mono (smallBump one_pos).integrable ?_ fun x => ?_
    · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (smallBump one_pos).continuous.mul (by fun_prop)
      · exact (smallBump one_pos).hasCompactSupport.mul_right
    · have : 1 ≤ Real.exp (τ * (x 0) ^ 2 / 2) :=
        Real.one_le_exp (by positivity)
      have hb := (smallBump one_pos).nonneg (x := x)
      nlinarith
  have hpos : 0 < ∫ x, smallBump one_pos x := (smallBump one_pos).integral_pos
  have hn : Tendsto (fun τ : ℝ => ‖∫ x, smallAmp one_pos x * cexp (τ * growAction x)‖)
      atTop (nhds 0) := by simpa using hI.norm
  have := ge_of_tendsto hn (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ using hlow τ hτ)
  linarith

/-! ### `det H` against `det (-H)` -/

/-- On `ℝ¹` the determinants differ: the Hessian of the Gaussian action is `-1`, so
`det H = -1` and `det (-H) = 1`. An odd dimension tells the two readings of the source's
`√(det H)` apart. -/
theorem det_gauss_hessian :
    (hessMat gaussAction 0).det = -1 ∧ (-hessMat gaussAction 0).det = 1 := by
  rw [hessMat_gaussAction]
  simp

/-- For an even dimension the radicands agree: `det (-M) = det M`. This is the case of the
vertex (`n = 44`). -/
theorem det_neg_of_even {n : ℕ} (hn : Even n) (M : Matrix (Fin n) (Fin n) ℂ) :
    (-M).det = M.det := by
  rw [Matrix.det_neg, Fintype.card_fin, hn.neg_one_pow, one_mul]

/-- Even dimension does **not** make the inverse square root insensitive to the sign of the
Hessian: for `H = -1` on `ℂ²` the radicands `det H = det (-H) = 1` agree, yet
`invSqrtDet (-H) = 1` and `invSqrtDet H = -1`. The branch of the root, which the source does not
state, is therefore a hypothesis of the formula, also for `n = 44`. -/
theorem invSqrtDet_neg_one_two :
    invSqrtDet (-(-1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 ∧
      invSqrtDet (-1 : Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  refine ⟨by rw [neg_neg]; exact invSqrtDet_one, ?_⟩
  have hd : (-1 : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal (fun _ => (-1 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hd, invSqrtDet_diagonal]
  simp only [Fin.prod_univ_two]
  have h2 : ((-1 : ℂ) ^ (-(1 / 2 : ℂ))) ^ 2 = -1 := by
    rw [← cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(1 / 2) = -1 by norm_num, cpow_neg_one]
    norm_num
  rw [← sq]; exact h2

end Lightlike.Asymptotics.Lorentzian
