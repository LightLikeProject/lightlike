module

public import Lightlike.Oscillatory.QuadraticPhase
public import Lightlike.Oscillatory.GaussianTests

/-!
# Trust checks for the quadratic-phase lemma

For `quadratic_phase`,
`∫ u e^{iτ⟨A x, x⟩/2} = (2π/τ)^{n/2} invSqrtDet(-iA) u(0) + O(τ^{-n/2-1})`:

* **Known value, the Maslov phase** (`invSqrtDet_neg_I_real_diagonal`): for a real nondegenerate
  diagonal `A = diag(d)`, `invSqrtDet(-iA) = ∏ |dᵢ|^{-1/2} e^{iπ sgn(dᵢ)/4}`, the classical
  `|det A|^{-1/2} e^{iπ sgn A/4}`. Special cases: `invSqrtDet(-i · 1) = e^{iπn/4}`
  (`invSqrtDet_neg_I_one`) and signature zero, `invSqrtDet(-i diag(1, -1)) = 1`
  (`invSqrtDet_neg_I_signature_zero`).
* **Non-vacuity, the Fresnel integral** (`fresnel_bump`): a smooth bump `u` on `ℝⁿ` with
  `u(0) = 1` (`bumpAmp`) and `A = 1` satisfy the hypotheses, and the lemma gives
  `∫ u e^{iτ|x|²/2} = (2π/τ)^{n/2} e^{iπn/4} + O(τ^{-n/2-1})`.
* **Wrong constant** (`fresnel_bump_wrong_phase`, `fresnel_bump_wrong_branch`): the leading
  coefficient is unique (`asymp_coeff_unique`), so on `ℝ¹` neither the real Gaussian coefficient
  `(2π/τ)^{1/2}`, without the Fresnel phase, nor the other square root
  `-(2π/τ)^{1/2} e^{iπ/4}` admits an `O(τ^{-3/2})` error.
* **Wrong input** (`quadratic_phase_needs_det`): for `A = 0` the integral is `∫ u`, which does
  not decay, while the formula's leading term is `0` (Lean's junk value `0^{-1/2} = 0`). The
  hypothesis `det A ≠ 0` cannot be dropped.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset Filter
open scoped Real ContDiff Topology

namespace Lightlike.Oscillatory

/-- `(-i)^{-1/2} = e^{iπ/4}` with the principal branch. -/
theorem cpow_neg_I_neg_half : (-I) ^ (-(1 / 2 : ℂ)) = cexp (π / 4 * I) := by
  rw [cpow_def_of_ne_zero (neg_ne_zero.mpr I_ne_zero), log_neg_I]
  congr 1
  ring

/-- `i^{-1/2} = e^{-iπ/4}` with the principal branch. -/
theorem cpow_I_neg_half : I ^ (-(1 / 2 : ℂ)) = cexp (-(π / 4 * I)) := by
  rw [cpow_def_of_ne_zero I_ne_zero, log_I]
  congr 1
  ring

/-- Known value, the Maslov phase: for real `dᵢ ≠ 0`,
`invSqrtDet(-i diag(d)) = ∏ᵢ |dᵢ|^{-1/2} e^{iπ sgn(dᵢ)/4}`, that is
`|det A|^{-1/2} e^{iπ sgn A/4}` (Hörmander, *ALPDO I*, (3.4.6) and §7.7). -/
theorem invSqrtDet_neg_I_real_diagonal {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    invSqrtDet (-I • diagonal fun i => (d i : ℂ)) =
      ∏ i, ((|d i| ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp ((if 0 < d i then 1 else -1) * (π / 4 * I)) := by
  rw [← diagonal_smul, invSqrtDet_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have hab : 0 < |d i| := abs_pos.mpr (hd i)
  have hexp : (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) := by push_cast; ring
  rcases lt_or_gt_of_ne (hd i) with h | h
  · have hm : -I * (d i : ℂ) = ((|d i| : ℝ) : ℂ) * I := by
      rw [abs_of_neg h]; push_cast; ring
    rw [hm, cpow_ofReal_mul hab I_ne_zero, cpow_I_neg_half, hexp, ← ofReal_cpow hab.le]
    simp only [show ¬ (0 < d i) from not_lt.mpr h.le, ↓reduceIte, neg_one_mul]
  · have hm : -I * (d i : ℂ) = ((|d i| : ℝ) : ℂ) * (-I) := by
      rw [abs_of_pos h]; ring
    rw [hm, cpow_ofReal_mul hab (neg_ne_zero.mpr I_ne_zero), cpow_neg_I_neg_half, hexp,
      ← ofReal_cpow hab.le]
    simp only [h, ↓reduceIte, one_mul]

/-- Known value: `invSqrtDet(-i · 1) = e^{iπn/4}`, the Fresnel phase of `e^{iτ|x|²/2}`. -/
theorem invSqrtDet_neg_I_one {n : ℕ} :
    invSqrtDet (-I • (1 : Matrix (Fin n) (Fin n) ℂ)) = cexp (n * (π / 4 * I)) := by
  rw [smul_one_eq_diagonal, invSqrtDet_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, cpow_neg_I_neg_half, ← Complex.exp_nat_mul]

/-- Known value: signature zero gives no phase, `invSqrtDet(-i diag(1, -1)) = 1`. -/
theorem invSqrtDet_neg_I_signature_zero :
    invSqrtDet (-I • diagonal ![(1 : ℂ), -1]) = 1 := by
  rw [← diagonal_smul, invSqrtDet_diagonal, Fin.prod_univ_two]
  simp only [Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul, mul_one,
    mul_neg, neg_neg]
  rw [cpow_neg_I_neg_half, cpow_I_neg_half, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The standard smooth bump on `ℝⁿ`: equal to `1` on the unit ball, supported in the ball of
radius `2`. -/
noncomputable def stdBump (n : ℕ) : ContDiffBump (0 : Fin n → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The standard bump as a complex amplitude. -/
noncomputable def bumpAmp (n : ℕ) (x : Fin n → ℝ) : ℂ := (stdBump n x : ℂ)

/-- The amplitude `bumpAmp` is smooth. -/
theorem contDiff_bumpAmp (n : ℕ) : ContDiff ℝ ∞ (bumpAmp n) :=
  ofRealCLM.contDiff.comp (stdBump n).contDiff

/-- The amplitude `bumpAmp` has compact support. -/
theorem hasCompactSupport_bumpAmp (n : ℕ) : HasCompactSupport (bumpAmp n) :=
  (stdBump n).hasCompactSupport.comp_left ofReal_zero

/-- The amplitude `bumpAmp` is `1` at the origin. -/
theorem bumpAmp_zero (n : ℕ) : bumpAmp n 0 = 1 := by
  simp [bumpAmp, (stdBump n).one_of_mem_closedBall
    (Metric.mem_closedBall_self (stdBump n).rIn_pos.le)]

/-- The identity satisfies the hypothesis `Im ⟨A x, x⟩ ≥ 0`: its form is real. -/
theorem im_qform_one_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ (qform (1 : Matrix (Fin n) (Fin n) ℂ) x).im := by
  rw [qform_one]
  simp only [← ofReal_pow, ← ofReal_sum, ofReal_im, le_refl]

/-- Non-vacuity, the Fresnel integral: for the bump `u` with `u(0) = 1`,
`∫ u e^{iτ|x|²/2} dx = (2π/τ)^{n/2} e^{iπn/4} + O(τ^{-n/2-1})`. -/
theorem fresnel_bump (n : ℕ) :
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, bumpAmp n x * cexp (I * τ * (∑ i, (x i : ℂ) ^ 2) / 2)) -
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * cexp (n * (π / 4 * I))‖ ≤
        C * τ ^ (-((n : ℝ) / 2) - 1) := by
  obtain ⟨C, τ₀, hτ₀, h⟩ := quadratic_phase isSymm_one im_qform_one_nonneg (by simp)
    (contDiff_bumpAmp n) (hasCompactSupport_bumpAmp n)
  refine ⟨C, τ₀, hτ₀, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  simp only [invSqrtDet_neg_I_one, bumpAmp_zero, mul_one, qform_one] at h1
  exact h1

/-- The leading coefficient of an expansion `F(τ) = (2π/τ)^p a + O(τ^{-p-1})` is unique. -/
theorem asymp_coeff_unique {F : ℝ → ℂ} {p : ℝ} {a b : ℂ}
    (ha : ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖F τ - ((2 * π / τ) ^ p : ℝ) * a‖ ≤ C * τ ^ (-p - 1))
    (hb : ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖F τ - ((2 * π / τ) ^ p : ℝ) * b‖ ≤ C * τ ^ (-p - 1)) :
    a = b := by
  obtain ⟨C, τ₀, hτ₀, hC⟩ := ha
  obtain ⟨C', τ₁, -, hC'⟩ := hb
  have hP : 0 < (2 * π) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have key : ∀ τ ≥ max τ₀ τ₁, (2 * π) ^ p * ‖a - b‖ ≤ (C + C') * τ⁻¹ := by
    intro τ hτ
    have hτ0 : 0 < τ := lt_of_lt_of_le hτ₀ (le_trans (le_max_left _ _) hτ)
    have h1 := hC τ (le_trans (le_max_left _ _) hτ)
    have h2 := hC' τ (le_trans (le_max_right _ _) hτ)
    have htri : ‖(((2 * π / τ) ^ p : ℝ) : ℂ) * (a - b)‖ ≤
        C * τ ^ (-p - 1) + C' * τ ^ (-p - 1) := by
      calc _ = ‖(F τ - ((2 * π / τ) ^ p : ℝ) * b) - (F τ - ((2 * π / τ) ^ p : ℝ) * a)‖ := by
            congr 1; ring1
        _ ≤ _ := (norm_sub_le _ _).trans (by linarith)
    have hT : 0 < τ ^ p := Real.rpow_pos_of_pos hτ0 p
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.div_rpow (by positivity) hτ0.le, Real.rpow_sub_one hτ0.ne', Real.rpow_neg hτ0.le,
      show (2 * π) ^ p / τ ^ p * ‖a - b‖ = (2 * π) ^ p * ‖a - b‖ / τ ^ p by ring,
      show C * ((τ ^ p)⁻¹ / τ) + C' * ((τ ^ p)⁻¹ / τ) = (C + C') * τ⁻¹ / τ ^ p by ring] at htri
    exact (div_le_div_iff_of_pos_right hT).mp htri
  have ht : Tendsto (fun τ : ℝ => (C + C') * τ⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (C + C')
  have hle := ge_of_tendsto ht ((eventually_ge_atTop (max τ₀ τ₁)).mono key)
  have hn : ‖a - b‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_right hle hP) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- For the bump, the Fresnel coefficient `e^{iπn/4}` is the only coefficient `c` with
`∫ u e^{iτ|x|²/2} = (2π/τ)^{n/2} c + O(τ^{-n/2-1})`. -/
theorem fresnel_bump_coeff_unique (n : ℕ) {c : ℂ}
    (h : ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, bumpAmp n x * cexp (I * τ * (∑ i, (x i : ℂ) ^ 2) / 2)) -
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * c‖ ≤ C * τ ^ (-((n : ℝ) / 2) - 1)) :
    c = cexp (n * (π / 4 * I)) :=
  asymp_coeff_unique h (fresnel_bump n)

/-- Wrong constant: on `ℝ¹`, the coefficient of a real Gaussian, `(2π/τ)^{1/2}` without the
Fresnel phase `e^{iπ/4}`, admits no `O(τ^{-3/2})` error. -/
theorem fresnel_bump_wrong_phase :
    ¬ ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, bumpAmp 1 x * cexp (I * τ * (∑ i, (x i : ℂ) ^ 2) / 2)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * 1‖ ≤ C * τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  have h1 := (fresnel_bump_coeff_unique 1 h).symm
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  have him := congrArg Complex.im hk
  simp only [Nat.cast_one, one_mul, mul_im, div_ofNat_re, div_ofNat_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, mul_one, zero_div, add_zero, intCast_re, intCast_im, zero_mul,
    re_ofNat, im_ofNat, sub_zero, mul_re] at him
  have h8 : π * 1 = π * (8 * k) := by linarith
  have h8' : ((1 : ℤ) : ℝ) = ((8 * k : ℤ) : ℝ) := by
    push_cast; exact mul_left_cancel₀ Real.pi_ne_zero h8
  have := Int.cast_injective h8'
  omega

/-- Wrong constant: on `ℝ¹`, the other square root, `-(2π/τ)^{1/2} e^{iπ/4}`, admits no
`O(τ^{-3/2})` error. -/
theorem fresnel_bump_wrong_branch :
    ¬ ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, bumpAmp 1 x * cexp (I * τ * (∑ i, (x i : ℂ) ^ 2) / 2)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) * -cexp (π / 4 * I)‖ ≤
        C * τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  intro h
  have h1 := fresnel_bump_coeff_unique 1 h
  rw [Nat.cast_one, one_mul, neg_eq_iff_add_eq_zero, ← two_mul] at h1
  exact Complex.exp_ne_zero _ ((mul_eq_zero.mp h1).resolve_left two_ne_zero)

/-- Wrong input: `det A ≠ 0` cannot be dropped. For `A = 0` on `ℝ¹` the integral is `∫ u > 0`
for every `τ`, while the formula's leading term `(2π/τ)^{1/2} invSqrtDet(0) u(0)` is `0`, so
the claimed `O(τ^{-3/2})` error fails. -/
theorem quadratic_phase_needs_det :
    ¬ ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ ≥ τ₀,
      ‖(∫ x, bumpAmp 1 x * cexp (I * τ * qform (0 : Matrix (Fin 1) (Fin 1) ℂ) x / 2)) -
        ((2 * π / τ) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • (0 : Matrix (Fin 1) (Fin 1) ℂ)) * bumpAmp 1 0‖ ≤
        C * τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
  rintro ⟨C, τ₀, -, h⟩
  have hq : ∀ x, qform (0 : Matrix (Fin 1) (Fin 1) ℂ) x = 0 := fun x => by simp [qform]
  have hdet0 : invSqrtDet (-I • (0 : Matrix (Fin 1) (Fin 1) ℂ)) = 0 := by
    rw [smul_zero, ← diagonal_zero, invSqrtDet_diagonal]
    simp
  have hint : ∫ x, bumpAmp 1 x = ((∫ x, stdBump 1 x : ℝ) : ℂ) := integral_ofReal
  have hpos : 0 < ∫ x, stdBump 1 x := (stdBump 1).integral_pos
  simp only [hq, mul_zero, zero_div, Complex.exp_zero, mul_one, hdet0, zero_mul, sub_zero,
    hint, Complex.norm_real, Real.norm_of_nonneg hpos.le] at h
  have ht : Tendsto (fun τ : ℝ => C * τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < ((1 : ℕ) : ℝ) / 2 + 1)).const_mul C
    rw [mul_zero] at this
    refine this.congr fun τ => ?_
    rw [neg_add']
  obtain ⟨τ, hτ, hlt⟩ := ((eventually_ge_atTop τ₀).and (ht.eventually (gt_mem_nhds hpos))).exists
  linarith [h τ hτ]

end Lightlike.Oscillatory
