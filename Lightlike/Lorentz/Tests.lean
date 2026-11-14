module

public import Lightlike.Lorentz.SU2Decomposition
public import Lightlike.Lorentz.Continuity
public import Lightlike.Lorentz.SmoothVectors
public import Physlib.Relativity.SL2C.Cover

/-!
# Trust checks for milestone HA1

1. **Casimir values against an independent computation.** On every real-linear function
   `L : ℂ² → ℂ` the Casimirs can be computed directly from the definition (all second derivatives
   vanish): `C₁ L = (3/2) L` and `C₂ L (ζ) = -(3/4) L(iζ)` (`casimir1_linear`,
   `casimir2_linear`). The coordinate `ζ₀` is homogeneous of degree `(1, 0)`, i.e. the
   parameters `(k, ρ) = (1/2, -3i/2)` of the defining representation `(½, 0)` (Rühl's
   `(k, ρ) = (j₁ - j₂, ±i(j₁ + j₂ + 1))`), and `ζ̄₀` is homogeneous with `(k, ρ) = (-1/2, -3i/2)`,
   the representation `(0, ½)` (`isHomog_coord`, `isHomog_conj_coord`). The general theorems
   `casimir1_eq`, `casimir2_eq` give `k² - ρ² - 1 = 3/2` and `kρ = ∓3i/4`, which agrees with the
   direct computation (`casimir_coord_check`, `casimir_conj_coord_check`). The trivial
   representation (constant functions, `(k, ρ) = (0, -i)`) has both Casimirs `0`
   (`casimir_const_check`).
2. **Wrong inputs.** The second Casimir separates the two chiralities (`casimir2_chirality`); the
   principal-series parameter `ρ = 0` is the wrong degree for `ζ₀` (`not_isHomog_coord`).
3. **A parameter outside the principal series breaks unitarity.** For `g = diag(a, a⁻¹)` the
   formula of the principal series scales the `L²` norm by `|a|^{4 Im ρ}` (`lintegral_act_diag`),
   so for `Im ρ ≠ 0` there is an `L²` function whose norm changes (`not_unitary_of_im_ne_zero`),
   while for real `ρ` the factor is `1`.
4. **Spin content.** For `k = 1` the lowest spin is `1`: spins `0` and `½` do not occur
   (`no_spin_zero_k1`, `no_spin_half_k1`). For `k = ½` spin `0` does not occur but spin `½` does
   (`no_spin_zero_khalf`, `lowest_spin_khalf`).
5. **Haar measure.** `SL(2,ℂ)` has infinite Haar volume (`SL2C.haar_univ`), and its left Haar
   measure is right-invariant (`SL2C.haar_isMulRightInvariant`).
6. **Compatibility with Physlib.** The group used here is literally
   Physlib's `SL(2,ℂ)` (`sl2c_eq_physlib`), so Physlib's double cover of the restricted Lorentz
   group, stated in Physlib's signature `(+,-,-,-)`, applies to it unchanged
   (`toRestrictedLorentzGroup_surjective`). L1 never needs the Lorentz group itself.

References: W. Rühl, *The Lorentz Group and Harmonic Analysis* (Benjamin, 1970), for the
parameters `(k, ρ)` of the finite-dimensional representations; J. W. Barrett et al., Class.
Quantum Grav. 27 (2010) 165009, for the Casimir values.
-/

@[expose] public section

open Matrix Complex MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Lightlike.Lorentz.Tests

open Lightlike.Lorentz Lightlike.SU2

/-! ## 1. Casimirs on linear functions, computed directly -/

lemma lie_clm (L : C2 →L[ℝ] ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) (ζ : C2) :
    lie X L ζ = L (Xᵀ *ᵥ ζ) := by
  simp [lie, L.fderiv]

lemma lie_lie_clm (L : C2 →L[ℝ] ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) (ζ : C2) :
    lie X (lie Y L) ζ = L (Yᵀ *ᵥ (Xᵀ *ᵥ ζ)) := by
  have : lie Y L = ⇑(L.comp (mulVecCLM Y)) := by
    funext ζ'; rw [lie_clm]; rfl
  rw [this, lie_clm]; rfl

/-- **Direct computation**: `C₁ L = (3/2) L` for every real-linear `L`. -/
theorem casimir1_linear (L : C2 →L[ℝ] ℂ) (ζ : C2) : casimir1 L ζ = 3 / 2 * L ζ := by
  simp only [casimir1, lie_lie_clm, boostGen_sq, rotGen_sq, map_smul, Fin.sum_univ_three,
    Complex.real_smul]
  push_cast; ring

/-- **Direct computation**: `C₂ L (ζ) = -(3/4) L(iζ)` for every real-linear `L`. -/
theorem casimir2_linear (L : C2 →L[ℝ] ℂ) (ζ : C2) :
    casimir2 L ζ = -(3 / 4) * L (I • ζ) := by
  simp only [casimir2, lie_lie_clm, boostGen_rotGen, map_smul, Fin.sum_univ_three,
    Complex.real_smul]
  push_cast; ring

/-- The coordinate `ζ ↦ ζ₀`, a real-linear map. -/
noncomputable def coord : C2 →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) 0

/-- The conjugate coordinate `ζ ↦ ζ̄₀`. -/
noncomputable def conjCoord : C2 →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp coord

@[simp] lemma coord_apply (ζ : C2) : coord ζ = ζ 0 := rfl
@[simp] lemma conjCoord_apply (ζ : C2) : conjCoord ζ = conj (ζ 0) := rfl

lemma mult_coord (w : ℂ) (hw : w ≠ 0) : mult 1 (-3 * I / 2) w = w := by
  have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have : 2 * I * (-3 * I / 2) - 2 = 1 := by ring_nf; rw [I_sq]; ring
  rw [mult, this, Complex.cpow_one, zpow_one]; field_simp

/-- `ζ₀` is homogeneous of degree `(1, 0)`: `(k, ρ) = (1/2, -3i/2)`, the representation `(½, 0)`. -/
theorem isHomog_coord : IsHomog 1 (-3 * I / 2) coord := by
  intro w ζ hw _
  show coord (w • ζ) = mult 1 (-3 * I / 2) w * coord ζ
  rw [mult_coord w hw]; simp

/-- `ζ̄₀` is homogeneous of degree `(0, 1)`: `(k, ρ) = (-1/2, -3i/2)`, the representation
`(0, ½)`. -/
theorem isHomog_conj_coord : IsHomog (-1) (-3 * I / 2) conjCoord := by
  intro w ζ hw _
  have h := mult_coord w hw
  have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have hn : w / ((‖w‖ : ℝ) : ℂ) ≠ 0 := div_ne_zero hw hw'
  -- `m_{-1}(w) = m_1(w) (w/|w|)^{-2} = w (w̄/w) = w̄`
  have hphase : (w / ((‖w‖ : ℝ) : ℂ))⁻¹ = conj (w / ((‖w‖ : ℝ) : ℂ)) := by
    have h1 : ‖w / ((‖w‖ : ℝ) : ℂ)‖ = 1 := norm_phase hw
    rw [inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hm : mult (-1) (-3 * I / 2) w = conj w := by
    have e : mult (-1) (-3 * I / 2) w = mult 1 (-3 * I / 2) w * (w / ((‖w‖ : ℝ) : ℂ))⁻¹ ^ 2 := by
      simp only [mult]; rw [_root_.zpow_neg_one, zpow_one, inv_pow]; field_simp
    rw [e, h, hphase, map_div₀, Complex.conj_ofReal]
    have hc : (conj w) ≠ 0 := by simpa using hw
    field_simp
    rw [show ((‖w‖ : ℝ) : ℂ) ^ 2 = w * conj w by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring]
  show conjCoord (w • ζ) = mult (-1) (-3 * I / 2) w * conjCoord ζ
  rw [hm]; simp

/-- **Check (defining representation `(½, 0)`)**: the general Casimir theorems reproduce the direct
computation, `C₁ = 3/2`, `C₂ = -3i/4`. -/
theorem casimir_coord_check (ζ : C2) (hζ : ζ ≠ 0) :
    casimir1 coord ζ = 3 / 2 * ζ 0 ∧ casimir2 coord ζ = -(3 * I / 4) * ζ 0 ∧
    casimir1 coord ζ = (((1 : ℤ) / 2 : ℂ) ^ 2 - (-3 * I / 2) ^ 2 - 1) * coord ζ ∧
    casimir2 coord ζ = (((1 : ℤ) / 2 : ℂ) * (-3 * I / 2)) * coord ζ := by
  have hc : ContDiffAt ℝ 2 coord ζ := coord.contDiff.contDiffAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [casimir1_linear, coord_apply]
  · rw [casimir2_linear]; simp; ring
  · exact casimir1_eq isHomog_coord hζ hc
  · exact casimir2_eq isHomog_coord hζ hc

/-- **Check (representation `(0, ½)`)**: `C₁ = 3/2`, `C₂ = +3i/4`. -/
theorem casimir_conj_coord_check (ζ : C2) (hζ : ζ ≠ 0) :
    casimir1 conjCoord ζ = 3 / 2 * conj (ζ 0) ∧ casimir2 conjCoord ζ = (3 * I / 4) * conj (ζ 0) ∧
    casimir1 conjCoord ζ = (((-1 : ℤ) / 2 : ℂ) ^ 2 - (-3 * I / 2) ^ 2 - 1) * conjCoord ζ ∧
    casimir2 conjCoord ζ = (((-1 : ℤ) / 2 : ℂ) * (-3 * I / 2)) * conjCoord ζ := by
  have hc : ContDiffAt ℝ 2 conjCoord ζ := conjCoord.contDiff.contDiffAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [casimir1_linear, conjCoord_apply]
  · rw [casimir2_linear]; simp; ring
  · exact casimir1_eq isHomog_conj_coord hζ hc
  · exact casimir2_eq isHomog_conj_coord hζ hc

/-- The numbers agree: `k² - ρ² - 1 = 3/2` and `kρ = -3i/4` at `(k, ρ) = (1/2, -3i/2)`. -/
example : ((1 : ℂ) / 2) ^ 2 - (-3 * I / 2) ^ 2 - 1 = 3 / 2 := by ring_nf; rw [I_sq]; ring
example : ((1 : ℂ) / 2) * (-3 * I / 2) = -(3 * I / 4) := by ring

/-- **Check (trivial representation)**: the constant `1` is homogeneous with `(k, ρ) = (0, -i)`,
and both Casimirs vanish on it, as the formulas `k² - ρ² - 1 = 0` and `kρ = 0` predict. -/
theorem casimir_const_check (ζ : C2) (hζ : ζ ≠ 0) :
    IsHomog 0 (-I) (fun _ => 1) ∧ casimir1 (fun _ => (1 : ℂ)) ζ = 0 ∧
    casimir2 (fun _ => (1 : ℂ)) ζ = 0 := by
  have hh : IsHomog 0 (-I) (fun _ => 1) := by
    intro w ζ hw _
    have : 2 * I * -I - 2 = 0 := by ring_nf; rw [I_sq]; ring
    show (1 : ℂ) = mult 0 (-I) w * 1
    rw [mult, this]; simp
  have hc : ContDiffAt ℝ 2 (fun _ : C2 => (1 : ℂ)) ζ := contDiffAt_const
  refine ⟨hh, ?_, ?_⟩
  · rw [casimir1_eq hh hζ hc]; ring_nf; rw [I_sq]; ring
  · rw [casimir2_eq hh hζ hc]; ring

/-! ## 2. Wrong inputs -/

/-- **The second Casimir separates `(½, 0)` from `(0, ½)`.** -/
theorem casimir2_chirality (ζ : C2) (h0 : ζ 0 = 1) :
    casimir2 coord ζ ≠ casimir2 conjCoord ζ := by
  rw [casimir2_linear, casimir2_linear]
  simp [h0]
  intro h
  have := congrArg Complex.im h
  simp at this
  norm_num at this

/-- **The principal-series parameter `ρ = 0` is the wrong degree for `ζ₀`**:
`ζ₀` is not homogeneous of degree `(-1+k, -1-k)`, `k = 1/2`. -/
theorem not_isHomog_coord : ¬ IsHomog 1 0 coord := by
  intro h
  have hζ : (![1, 0] : C2) ≠ 0 := by intro h'; have := congrFun h' 0; simp at this
  have := h 2 ![1, 0] two_ne_zero hζ
  simp only [coord_apply, Pi.smul_apply, smul_eq_mul, mult] at this
  norm_num at this
  have h2 : ((2 : ℂ)) ^ (-2 : ℂ) = 1 / 4 := by
    rw [show (-2 : ℂ) = ((-2 : ℤ) : ℂ) by norm_num, Complex.cpow_intCast]; norm_num
  rw [h2] at this
  norm_num at this

/-! ## 3. Outside the principal series, unitarity fails -/

lemma den_diag (a : ℂ) (ha : a ≠ 0) (z : ℂ) : den (SL2C.diagSL a ha) z = a⁻¹ := by
  simp [den, SL2C.diagSL, SL2C.mk]

/-- **Scaling of the `L²` norm by `g = diag(a, a⁻¹)`**: `∫ |π(g) f|² = |a|^{4 Im ρ} ∫ |f|²`, for
every complex `ρ`. -/
theorem lintegral_act_diag (n : ℤ) (ρ : ℂ) (a : ℂ) (ha : a ≠ 0) (f : ℂ → ℂ) :
    ∫⁻ z, ‖act n ρ (SL2C.diagSL a ha) f z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (‖a‖ ^ (4 * ρ.im)) * ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set g := SL2C.diagSL a ha
  rw [lintegral_mob g (fun w => ‖f w‖ₑ ^ (2 : ℝ)), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  have hd : den g z = a⁻¹ := den_diag a ha z
  show ‖mult n ρ (den g z) * f (mob g z)‖ₑ ^ (2 : ℝ) = _
  rw [hd, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← mul_assoc]
  congr 1
  rw [← ofReal_norm, norm_mult_complex n ρ (inv_ne_zero ha),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) zero_le_two, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [norm_inv, ← Real.rpow_mul (by positivity), Real.inv_rpow hapos.le, ← Real.rpow_neg hapos.le,
    inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_add hapos]
  congr 1; push_cast; ring

/-- For real `ρ` the scaling factor is `1`, consistent with unitarity. -/
example (ρ : ℝ) (a : ℂ) : ‖a‖ ^ (4 * (ρ : ℂ).im) = 1 := by simp

/-- **A parameter outside the principal series breaks unitarity**: if `Im ρ ≠ 0`, the same formula
changes the `L²` norm of the indicator of the unit disc. -/
theorem not_unitary_of_im_ne_zero (n : ℤ) (ρ : ℂ) (hρ : ρ.im ≠ 0) :
    ∃ (g : SL2C) (f : ℂ → ℂ), MemLp f 2 volume ∧
      ∫⁻ z, ‖act n ρ g f z‖ₑ ^ (2 : ℝ) ≠ ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) := by
  have hball : MeasurableSet (Metric.ball (0 : ℂ) 1) := measurableSet_ball
  set f : ℂ → ℂ := (Metric.ball (0 : ℂ) 1).indicator (fun _ => (1 : ℂ))
  have hf : MemLp f 2 volume :=
    memLp_indicator_const 2 hball.nullMeasurableSet (1 : ℂ) (Or.inr measure_ball_lt_top.ne)
  have hI : ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) = volume (Metric.ball (0 : ℂ) 1) := by
    rw [← lintegral_indicator_one hball]
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ Metric.ball (0 : ℂ) 1 <;> simp [f, hw]
  refine ⟨SL2C.diagSL 2 two_ne_zero, f, hf, ?_⟩
  rw [lintegral_act_diag, hI]
  have hpos : volume (Metric.ball (0 : ℂ) 1) ≠ 0 := (Metric.measure_ball_pos volume 0 one_pos).ne'
  have htop : volume (Metric.ball (0 : ℂ) 1) ≠ ⊤ := measure_ball_lt_top.ne
  intro h
  have h1 : ENNReal.ofReal (‖(2 : ℂ)‖ ^ (4 * ρ.im)) = 1 := by
    have := (ENNReal.mul_eq_right hpos htop).mp h
    exact this
  rw [ENNReal.ofReal_eq_one] at h1
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at h1
  rcases lt_or_gt_of_ne hρ with hlt | hgt
  · have : (2 : ℝ) ^ (4 * ρ.im) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    linarith
  · have : 1 < (2 : ℝ) ^ (4 * ρ.im) := Real.one_lt_rpow one_lt_two (by linarith)
    linarith

/-! ## 4. Spin content -/

/-- `k = 1`: spin `0` does not occur. -/
theorem no_spin_zero_k1 (ρ : ℝ) {S : (Fin (0 + 1) → ℂ) →ₗ[ℂ] L2C}
    (hS : IsPSIntertwiner 2 ρ S) : S = 0 :=
  intertwiner_eq_zero 2 ρ (fun ℓ => by omega) hS

/-- `k = 1`: spin `½` does not occur. -/
theorem no_spin_half_k1 (ρ : ℝ) {S : (Fin (1 + 1) → ℂ) →ₗ[ℂ] L2C}
    (hS : IsPSIntertwiner 2 ρ S) : S = 0 :=
  intertwiner_eq_zero 2 ρ (fun ℓ => by omega) hS

/-- `k = 1`: the lowest spin is `1` (`2j = 2`). -/
example : dsp 2 0 = 2 := by rw [dsp_eq]; rfl

/-- `k = ½`: spin `0` does not occur. -/
theorem no_spin_zero_khalf (ρ : ℝ) {S : (Fin (0 + 1) → ℂ) →ₗ[ℂ] L2C}
    (hS : IsPSIntertwiner 1 ρ S) : S = 0 :=
  intertwiner_eq_zero 1 ρ (fun ℓ => by omega) hS

/-- `k = ½`: the lowest spin is `½`, and it occurs (its embedding is an isometry). -/
theorem lowest_spin_khalf (ρ : ℝ) : dsp 1 0 = 1 ∧ ∀ x, ‖suV 1 ρ 0 x‖ = ‖x‖ :=
  ⟨by rw [dsp_eq]; rfl, fun x => (suV 1 ρ 0).norm_map x⟩

/-! ## 5. Non-vacuity of the representation -/

/-- The Haar measure of `SL(2,ℂ)` is infinite, as for every noncompact group. -/
example : SL2C.haar Set.univ = ⊤ := SL2C.haar_univ

/-! ## Non-vacuity of the generator formula -/

/-- The boost curve `t ↦ diag(e^{t/2}, e^{-t/2})` in `SL(2,ℂ)`. -/
noncomputable def boostCurve (t : ℝ) : SL2C :=
  SL2C.mk (cexp ((t : ℂ) / 2)) 0 0 (cexp (-((t : ℂ) / 2))) (by
    rw [← Complex.exp_add]; simp)

/-- **The hypotheses of `hasDerivAt_actH` are met**: the boost curve starts at `1` with velocity
`K₃ = σ₃ / 2`, so `dπ(K₃) F` is the derivative of `t ↦ F(γ(t)ᵀ ζ)` for every differentiable `F`. -/
theorem hasDerivAt_boostCurve {F : C2 → ℂ} {ζ : C2} (hF : DifferentiableAt ℝ F ζ) :
    HasDerivAt (fun t => actH (boostCurve t) F ζ) (lie (boostGen 2) F ζ) 0 := by
  refine hasDerivAt_actH boostCurve (boostGen 2) ?_ ?_ hF
  · ext i j; fin_cases i <;> fin_cases j <;> simp [boostCurve, SL2C.mk]
  · have h1 : HasDerivAt (fun t : ℝ => cexp ((t : ℂ) / 2)) 2⁻¹ 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.div_const (2 : ℂ)).cexp
      simpa using this
    have h2 : HasDerivAt (fun t : ℝ => cexp (-((t : ℂ) / 2))) (-2⁻¹) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.div_const (2 : ℂ)).neg.cexp
      simpa using this
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [boostCurve, SL2C.mk, boostGen, pauli, hasDerivAt_const, h1, h2]

/-! ## 6. Compatibility with Physlib -/

open MatrixGroups in
/-- **The group used here is Physlib's `SL(2,ℂ)`** (both are Mathlib's
`Matrix.SpecialLinearGroup (Fin 2) ℂ`). -/
theorem sl2c_eq_physlib : SL2C = SL(2, ℂ) := rfl

/-- **Physlib's double cover applies unchanged**: `SL(2,ℂ) → SO⁺(1,3)` is onto (Physlib, signature
`(+,-,-,-)`). -/
theorem toRestrictedLorentzGroup_surjective :
    Function.Surjective (Lorentz.SL2C.toRestrictedLorentzGroup : SL2C →* _) :=
  Lorentz.SL2C.toRestrictedLorentzGroup_surjective

end Lightlike.Lorentz.Tests
