module

public import Lightlike.Oscillatory.Localisation
public import Lightlike.Oscillatory.PhaseReductionTests

/-!
# Trust checks for non-stationary phase and localisation

* **Non-vacuity, `dF ≠ 0`** (`nonstationary_phase_linPhase`): the linear phase `F(x) = x` on `ℝ¹`
  with a bump amplitude satisfies every hypothesis of `nonstationary_phase`, so the Fourier
  transform of the bump is `O(τ^{-k})` for every `k`.
* **Non-vacuity, `Im F > 0`** (`noncritical_const_I`): the constant phase `F = i` has `dF = 0`
  everywhere, so only the exponential-decay branch of `exists_bound_noncritical` applies.
* **Non-vacuity, localisation** (`localise_testPhase`): the phase `x²/2 + x³ + i x⁴` has exactly one
  critical point, `0` (`im_testPhase`), so `integral_localise` applies with `K = {0}`.
* **Wrong input, a critical point** (`nonstationary_phase_needs_noncritical`): for the phase
  `x²/2 + x³ + i x⁴`, whose critical point `0` violates `dF ≠ 0`, the conclusion of
  `nonstationary_phase` fails already for `k = 2`. A bound `O(τ^{-2})` would make the leading term
  `(2π/τ)^{1/2} e^{iπ/4}` of `testPhase_bump` an `O(τ^{-3/2})`, forcing `e^{iπ/4} = 0`.
* **Wrong input, a constant real phase** (`noncritical_needs_hypothesis`): for `F = 0` (so
  `Im F = 0` and `dF = 0`) the integral is the constant `∫ u ≠ 0`, which is not even `O(τ^{-1})`.
  This check does not depend on the stationary-phase results.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset Filter
open scoped Real ContDiff Topology

namespace Lightlike.Oscillatory

/-- The amplitude `smallAmp` has compact support. -/
theorem hasCompactSupport_smallAmp {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (smallAmp hδ) :=
  (isCompact_closedBall 0 δ).of_isClosed_subset (isClosed_tsupport _) (tsupport_smallAmp hδ)

/-- The linear phase `F(x) = x` on `ℝ¹`. -/
noncomputable def linPhase (x : Fin 1 → ℝ) : ℂ := (x 0 : ℂ)

/-- The linear phase is smooth. -/
theorem contDiff_linPhase : ContDiff ℝ ∞ linPhase :=
  (ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).contDiff

/-- The linear phase has no critical point. -/
theorem fderiv_linPhase_ne_zero (x : Fin 1 → ℝ) : fderiv ℝ linPhase x ≠ 0 := by
  have h := (ofRealCLM.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)).hasFDerivAt (x := x)
  rw [show linPhase = ⇑(ofRealCLM.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0)) from rfl, h.fderiv]
  intro h0
  have := congrArg (fun L : (Fin 1 → ℝ) →L[ℝ] ℂ => L (Pi.single 0 1)) h0
  simp at this

/-- Non-vacuity of `nonstationary_phase`: the Fourier transform `∫ u(x) e^{iτx} dx` of a bump
is `O(τ^{-k})` for every `k`. -/
theorem nonstationary_phase_linPhase (k : ℕ) : ∃ C, ∀ τ : ℝ, 1 ≤ τ →
    ‖∫ x, smallAmp one_pos x * cexp (I * τ * linPhase x)‖ ≤ C * (τ ^ k)⁻¹ :=
  nonstationary_phase contDiff_linPhase (contDiff_smallAmp one_pos)
    (hasCompactSupport_smallAmp one_pos) (fun x _ => by simp [linPhase])
    (fun x _ => fderiv_linPhase_ne_zero x) k

/-- Non-vacuity of the exponential-decay branch: for the constant phase `F = i`, which is critical
everywhere, `∫ u e^{iτF} = e^{-τ} ∫ u` is `O(τ^{-k})` for every `k`. -/
theorem noncritical_const_I (k : ℕ) : ∃ C, ∀ τ : ℝ, 1 ≤ τ →
    ‖∫ x, smallAmp one_pos x * cexp (I * τ * (fun _ : Fin 1 → ℝ => I) x)‖ ≤ C * (τ ^ k)⁻¹ :=
  exists_bound_noncritical contDiff_const (contDiff_smallAmp one_pos)
    (hasCompactSupport_smallAmp one_pos) (fun x _ => by simp)
    (fun x _ => Or.inl (by simp)) k

/-- `Im φ(x) = x⁴` for the test phase `φ(x) = x²/2 + x³ + i x⁴`. -/
theorem im_testPhase (x : Fin 1 → ℝ) : (testPhase x).im = x 0 ^ 4 := by
  simp only [testPhase, testPoly, ← ofReal_pow, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
    div_ofNat_im]
  ring

/-- The only critical point of the test phase (`Im φ = 0`, `dφ = 0`) is `0`. -/
theorem eq_zero_of_im_testPhase {x : Fin 1 → ℝ} (h : (testPhase x).im = 0) : x = 0 := by
  rw [im_testPhase] at h
  funext i
  rw [Subsingleton.elim i 0]
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h

/-- Non-vacuity of `integral_localise`: for the test phase `x²/2 + x³ + i x⁴` and a bump `a`, the
integral localises at the single critical point `0`, with a cutoff supported in `ball 0 (1/2)`. -/
theorem localise_testPhase :
    ∃ χ : (Fin 1 → ℝ) → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ Metric.ball 0 (1 / 2) ∧ χ 0 = 1 ∧
      ∀ k : ℕ, ∃ C, ∀ τ : ℝ, 1 ≤ τ →
        ‖(∫ x, smallAmp one_pos x * cexp (I * τ * testPhase x)) -
          ∫ x, ((χ x : ℂ) * smallAmp one_pos x) * cexp (I * τ * testPhase x)‖ ≤
          C * (τ ^ k)⁻¹ := by
  have h0 : (0 : Fin 1 → ℝ) ∈ tsupport (smallAmp one_pos) :=
    subset_tsupport _ (by simp [Function.mem_support, smallAmp_zero])
  obtain ⟨χ, hχc, hχs, hχ1, hχb⟩ := integral_localise contDiff_testPhase
    (contDiff_smallAmp one_pos) (hasCompactSupport_smallAmp one_pos)
    (fun x _ => im_testPhase_nonneg x) {0}
    (fun x _ h _ => by simp [eq_zero_of_im_testPhase h]) (fun x hx => by simp_all)
    (fun _ => 1 / 2) (fun _ _ => by norm_num)
  refine ⟨χ 0, hχc 0 (by simp), hχs 0 (by simp), hχ1 0 (by simp), fun k => ?_⟩
  simpa only [Finset.sum_singleton] using hχb k

/-- Wrong input: the hypothesis `dF ≠ 0` of `nonstationary_phase` cannot be dropped. For the test
phase `x²/2 + x³ + i x⁴` (critical at `0`) some bump amplitude has `∫ u e^{iτφ} ≠ O(τ^{-2})`. -/
theorem nonstationary_phase_needs_noncritical :
    ¬ ∀ u : (Fin 1 → ℝ) → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      ∃ C, ∀ τ : ℝ, 1 ≤ τ → ‖∫ x, u x * cexp (I * τ * testPhase x)‖ ≤ C * (τ ^ 2)⁻¹ := by
  intro h
  obtain ⟨δ, hδ, u, huc, hus, -, hasym⟩ := testPhase_bump
  obtain ⟨C, hC⟩ := h u huc
    ((isCompact_closedBall 0 δ).of_isClosed_subset (isClosed_tsupport _) hus)
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 1 le_rfl)
  have hI : (fun τ : ℝ => ∫ x, u x * cexp (I * τ * testPhase x)) =O[atTop]
      fun τ : ℝ => τ ^ (-(((1 : ℕ) : ℝ) / 2) - 1) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with τ hτ
    have hτ0 : 0 < τ := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hτ0.le _)]
    refine (hC τ hτ).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [← Real.rpow_natCast, ← Real.rpow_neg hτ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hτ (by norm_num)
  have hlead := coeff_eq_zero_of_isBigO ((hI.sub hasym).congr_left fun τ => by ring)
  exact Complex.exp_ne_zero _ hlead

/-- Wrong input: for the constant real phase `F = 0` (`Im F = 0` and `dF = 0` everywhere) the
integral `∫ u e^{iτF} = ∫ u` of a bump is a nonzero constant, so it is not `O(τ^{-1})`. -/
theorem noncritical_needs_hypothesis :
    ¬ ∃ C, ∀ τ : ℝ, 1 ≤ τ →
      ‖∫ x, smallAmp one_pos x * cexp (I * τ * (fun _ : Fin 1 → ℝ => (0 : ℂ)) x)‖ ≤
        C * (τ ^ 1)⁻¹ := by
  rintro ⟨C, hC⟩
  have hint : ∀ τ : ℝ,
      ∫ x, smallAmp one_pos x * cexp (I * τ * (fun _ : Fin 1 → ℝ => (0 : ℂ)) x) =
        ((∫ x, smallBump one_pos x : ℝ) : ℂ) := by
    intro τ
    simp only [mul_zero, Complex.exp_zero, mul_one, smallAmp]
    exact integral_complex_ofReal
  have hpos : 0 < ∫ x, smallBump one_pos x := (smallBump one_pos).integral_pos
  set c := ∫ x, smallBump one_pos x
  have hτ : 1 ≤ max 1 ((C + 1) / c) := le_max_left _ _
  have h := hC _ hτ
  rw [hint, norm_real, Real.norm_of_nonneg hpos.le, pow_one] at h
  have hτ0 : 0 < max 1 ((C + 1) / c) := by linarith
  rw [le_mul_inv_iff₀ hτ0] at h
  have : (C + 1) / c * c ≤ max 1 ((C + 1) / c) * c :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le
  rw [div_mul_cancel₀ _ hpos.ne'] at this
  nlinarith

end Lightlike.Oscillatory
