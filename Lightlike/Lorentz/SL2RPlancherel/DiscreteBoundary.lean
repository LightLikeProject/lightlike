import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.DiscreteOrth

/-!
# The boundary form of `φ_i` against the principal-series coefficients

For the discrete direction `φ_i` (`l - s ≤ i < l`) and a matrix coefficient `Φ = Φ^ν_{m,n}`, the
Casimir boundary form `B = sinh (φ_i conj Φ' - φ_i' conj Φ)` tends to `0` at `0⁺`
(`tendsto_casBdry_phiN_zero`: `φ_i` extends continuously and `sinh φ_i' → 0`) and at `∞`
(`tendsto_casBdry_phiN_atTop`: `sinh φ_i` is bounded and `|Φ|, |Φ'| ≤ C e^{-ξ/4}`).
Hence the Casimir integral `∫_{(0,∞)} (L φ_i conj Φ - φ_i conj (L Φ)) sinh` vanishes whenever its
integrand is integrable (`integral_casimir_phiN_mcoefP_eq_zero`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The derivative `Φ'_{m,n} = ((w - n)/2) Φ_{m,n+1} + ((w + n)/2) Φ_{m,n-1}`. -/
def mcoefD (ν : ℝ) (m n : ℤ) (ξ : ℝ) : ℂ :=
  (wP ν - n) / 2 * mcoefP ν m (n + 1) ξ + (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ

lemma continuous_mcoefD (ν : ℝ) (m n : ℤ) : Continuous (mcoefD ν m n) :=
  (continuous_const.mul (continuous_mcoefP ν m (n + 1))).add
    (continuous_const.mul (continuous_mcoefP ν m (n - 1)))

lemma norm_mcoefD_le (ν : ℝ) (m n : ℤ) (ξ : ℝ) :
    ‖mcoefD ν m n ξ‖ ≤ (‖(wP ν - n) / 2‖ + ‖(wP ν + n) / 2‖) * hcXi ξ := by
  unfold mcoefD
  calc _ ≤ ‖(wP ν - n) / 2 * mcoefP ν m (n + 1) ξ‖ + ‖(wP ν + n) / 2 * mcoefP ν m (n - 1) ξ‖ :=
        norm_add_le _ _
    _ ≤ ‖(wP ν - n) / 2‖ * hcXi ξ + ‖(wP ν + n) / 2‖ * hcXi ξ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_mcoefP_le _ _ _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_mcoefP_le _ _ _ _) (norm_nonneg _))
    _ = _ := by ring

/-- The boundary form in terms of the continuous extension of `φ_i`. -/
def phiBdry (s l i : ℕ) (ν : ℝ) (m n : ℤ) (ξ : ℝ) : ℂ :=
  ((Real.sinh ξ * phiHalf s l i ξ : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefD ν m n ξ) -
    ((phiHalf s l i ξ * (((i : ℝ) - l) * Real.cosh ξ + (i + s)) : ℝ) : ℂ) *
      (starRingEnd ℂ) (mcoefP ν m n ξ)

lemma casBdry_phiN_eq (s l i : ℕ) (hli : l ≤ i + s) (ν : ℝ) (m n : ℤ) {ξ : ℝ} (hξ : 0 < ξ) :
    casBdry (fun t => ((phiN s l i t : ℝ) : ℂ)) (mcoefP ν m n) ξ = phiBdry s l i ν m n ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold casBdry phiBdry
  beta_reduce
  rw [(hasDerivAt_mcoefP ν m n ξ).deriv, ((hasDerivAt_phiN s l i hξ).ofReal_comp).deriv,
    phiN_eq_phiHalf s l i hli hξ]
  simp only [mcoefD, phiLog, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_natCast]
  field_simp

lemma zero_pow_mul_natCast (k : ℕ) : (0 : ℝ) ^ k * k = 0 := by
  cases k with
  | zero => simp
  | succ k => simp

/-- **The boundary form vanishes at `0⁺`.** -/
theorem tendsto_casBdry_phiN_zero (s l i : ℕ) (hli : l ≤ i + s) (ν : ℝ) (m n : ℤ) :
    Tendsto (casBdry (fun t => ((phiN s l i t : ℝ) : ℂ)) (mcoefP ν m n)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (phiBdry s l i ν m n) := by
    unfold phiBdry
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sinh.mul (continuous_phiHalf s l i))).mul
      (Complex.continuous_conj.comp (continuous_mcoefD ν m n))).sub
      ((Complex.continuous_ofReal.comp ((continuous_phiHalf s l i).mul
        ((continuous_const.mul Real.continuous_cosh).add continuous_const))).mul
        (Complex.continuous_conj.comp (continuous_mcoefP ν m n)))
  have h0 : phiBdry s l i ν m n 0 = 0 := by
    have hk : ((i : ℝ) - l) * Real.cosh 0 + (i + s) = ((2 * (i + s) - (l + s) : ℕ) : ℝ) := by
      rw [Real.cosh_zero, Nat.cast_sub (by omega)]; push_cast; ring
    have hz : phiHalf s l i 0 * (((i : ℝ) - l) * Real.cosh 0 + (i + s)) = 0 := by
      rw [hk, phiHalf]
      simp only [zero_div, Real.sinh_zero, Real.cosh_zero, one_pow, div_one]
      rw [mul_assoc, zero_pow_mul_natCast, mul_zero]
    rw [phiBdry, hz, Real.sinh_zero, zero_mul]
    simp
  have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [h0] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ξ hξ
  exact (casBdry_phiN_eq s l i hli ν m n hξ).symm

lemma one_le_sinh {ξ : ℝ} (hξ : 1 ≤ ξ) : 1 ≤ Real.sinh ξ := by
  have h1 : 1 ≤ Real.sinh 1 := by
    rw [Real.sinh_eq, Real.exp_neg]
    have he := Real.exp_one_gt_d9
    have hinv : (Real.exp 1)⁻¹ < 1 / 2 := by
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    linarith
  exact h1.trans (Real.sinh_le_sinh.2 hξ)

lemma cosh_le_two_mul_sinh {ξ : ℝ} (hξ : 1 ≤ ξ) : Real.cosh ξ ≤ 2 * Real.sinh ξ := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have h1 := Real.add_one_le_exp (2 * ξ)
  have h2 : Real.exp (2 * ξ) = Real.exp ξ * Real.exp ξ := by rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos ξ
  have hneg : Real.exp (-ξ) = (Real.exp ξ)⁻¹ := Real.exp_neg ξ
  rw [hneg]
  have : 3 ≤ Real.exp ξ * Real.exp ξ := by linarith
  have hinv : 3 * (Real.exp ξ)⁻¹ ≤ Real.exp ξ := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hpos]; linarith
  linarith

/-- **The boundary form vanishes at `∞`.** -/
theorem tendsto_casBdry_phiN_atTop (s l i : ℕ) (hli : l ≤ i + s) (hil : i < l) (ν : ℝ)
    (m n : ℤ) :
    Tendsto (casBdry (fun t => ((phiN s l i t : ℝ) : ℂ)) (mcoefP ν m n)) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_phiN_mul_sinh s l i hli hil
  set A := ‖(wP ν - n) / 2‖ + ‖(wP ν + n) / 2‖ with hA
  set D := 2 * |(i : ℝ) - l| + (i + s) with hD
  set M := K * (A + D) * hcConst with hM
  refine squeeze_zero_norm' (a := fun ξ => M * Real.exp (-ξ / 4)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ξ hξ
    have hξ0 : (0 : ℝ) < ξ := by linarith
    have hs := Real.sinh_pos_iff.2 hξ0
    have hsh1 : 1 ≤ Real.sinh ξ := one_le_sinh hξ
    have hφ0 := phiN_nonneg s l i hξ0
    have hXi := hcXi_le hξ0.le
    have hXi0 : 0 ≤ hcXi ξ := (norm_nonneg _).trans (norm_mcoefP_le ν ξ m n)
    have hg : |((i : ℝ) - l) * Real.cosh ξ + (i + s)| / Real.sinh ξ ≤ D := by
      rw [div_le_iff₀ hs]
      have hc := cosh_le_two_mul_sinh hξ
      calc |((i : ℝ) - l) * Real.cosh ξ + (i + s)| ≤ |(i : ℝ) - l| * Real.cosh ξ + (i + s) := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_pos (Real.cosh_pos ξ),
              abs_of_nonneg (show (0 : ℝ) ≤ (i : ℝ) + s by positivity)]
        _ ≤ |(i : ℝ) - l| * (2 * Real.sinh ξ) + (i + s) * Real.sinh ξ :=
            add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
              (le_mul_of_one_le_right (by positivity) hsh1)
        _ = D * Real.sinh ξ := by rw [hD]; ring
    unfold casBdry
    rw [(hasDerivAt_mcoefP ν m n ξ).deriv, ((hasDerivAt_phiN s l i hξ0).ofReal_comp).deriv]
    have hDer := norm_mcoefD_le ν m n ξ
    simp only [mcoefD] at hDer
    calc ‖((Real.sinh ξ : ℝ) : ℂ) * (((phiN s l i ξ : ℝ) : ℂ) *
            (starRingEnd ℂ) ((wP ν - n) / 2 * mcoefP ν m (n + 1) ξ +
              (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ) -
          ((phiN s l i ξ * phiLog s l i ξ : ℝ) : ℂ) * (starRingEnd ℂ) (mcoefP ν m n ξ))‖
        ≤ phiN s l i ξ * Real.sinh ξ * (A * hcXi ξ) +
          phiN s l i ξ * Real.sinh ξ * (D * hcXi ξ) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
          refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hs.le).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hφ0, abs_mul,
            abs_of_nonneg hφ0, phiLog, abs_div, abs_of_pos hs]
          have e1 : Real.sinh ξ * (phiN s l i ξ * ‖(wP ν - n) / 2 * mcoefP ν m (n + 1) ξ +
              (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ‖ + phiN s l i ξ *
                (|((i : ℝ) - l) * Real.cosh ξ + (i + s)| / Real.sinh ξ) * ‖mcoefP ν m n ξ‖) =
              phiN s l i ξ * Real.sinh ξ * ‖(wP ν - n) / 2 * mcoefP ν m (n + 1) ξ +
                (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ‖ + phiN s l i ξ * Real.sinh ξ *
                  ((|((i : ℝ) - l) * Real.cosh ξ + (i + s)| / Real.sinh ξ) * ‖mcoefP ν m n ξ‖) := by
            ring
          rw [e1]
          have hps : 0 ≤ phiN s l i ξ * Real.sinh ξ := mul_nonneg hφ0 hs.le
          exact add_le_add (mul_le_mul_of_nonneg_left hDer hps)
            (mul_le_mul_of_nonneg_left (mul_le_mul hg (norm_mcoefP_le ν ξ m n) (norm_nonneg _)
              (by rw [hD]; positivity)) hps)
      _ = phiN s l i ξ * Real.sinh ξ * ((A + D) * hcXi ξ) := by ring
      _ ≤ K * ((A + D) * (hcConst * Real.exp (-ξ / 4))) :=
          mul_le_mul (hK ξ hξ0) (mul_le_mul_of_nonneg_left hXi (by rw [hA, hD]; positivity))
            (by positivity) hK0
      _ = M * Real.exp (-ξ / 4) := by rw [hM]; ring
  · have : Tendsto (fun ξ : ℝ => Real.exp (-ξ / 4)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have : Tendsto (fun ξ : ℝ => -ξ / 4) atTop atBot := by
        simpa [neg_div] using (tendsto_neg_atTop_atBot.atBot_div_const (by norm_num : (0 : ℝ) < 4))
      exact this
    simpa using this.const_mul M

lemma contDiffOn_phiN (s l i : ℕ) :
    ContDiffOn ℝ 2 (fun t => ((phiN s l i t : ℝ) : ℂ)) (Ioi 0) := by
  have h : ContDiffOn ℝ 2 (phiN s l i) (Ioi 0) := by
    unfold phiN
    exact ((Real.contDiff_cosh.sub contDiff_const).pow _).contDiffOn.div
      (Real.contDiff_sinh.pow _).contDiffOn fun t ht => pow_ne_zero _ (Real.sinh_pos_iff.2 ht).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h

/-- **The Casimir integral of `φ_i` against a matrix coefficient vanishes**, for an integrable
symmetric integrand. -/
theorem integral_casimir_phiN_mcoefP_eq_zero (s l i : ℕ) (hli : l ≤ i + s) (hil : i < l) (ν : ℝ)
    (m n : ℤ) (r : ℝ)
    (hf : IntegrableOn (fun x => (radialCasimir l r (fun t => ((phiN s l i t : ℝ) : ℂ)) x *
      (starRingEnd ℂ) (mcoefP ν m n x) - ((phiN s l i x : ℝ) : ℂ) *
        (starRingEnd ℂ) (radialCasimir l r (mcoefP ν m n) x)) * (Real.sinh x : ℂ)) (Ioi 0)) :
    ∫ x in Ioi 0, (radialCasimir l r (fun t => ((phiN s l i t : ℝ) : ℂ)) x *
      (starRingEnd ℂ) (mcoefP ν m n x) - ((phiN s l i x : ℝ) : ℂ) *
        (starRingEnd ℂ) (radialCasimir l r (mcoefP ν m n) x)) * (Real.sinh x : ℂ) = 0 := by
  set F : ℝ → ℂ := fun t => ((phiN s l i t : ℝ) : ℂ) with hF
  have hFc := contDiffOn_phiN s l i
  have hGc : ContDiffOn ℝ 2 (mcoefP ν m n) (Ioi 0) :=
    ((contDiff_mcoefP ν m n).of_le (by norm_cast)).contDiffOn
  have hint_b : ∀ b : ℝ, 0 < b → ∫ x in (0 : ℝ)..b, (radialCasimir l r F x *
      (starRingEnd ℂ) (mcoefP ν m n x) - F x *
        (starRingEnd ℂ) (radialCasimir l r (mcoefP ν m n) x)) * (Real.sinh x : ℂ) =
      casBdry F (mcoefP ν m n) b := by
    intro b hb
    rw [intervalIntegral.integral_of_le hb.le]
    have hl := tendsto_intervalIntegral_zero_right hb (hf.mono_set Ioc_subset_Ioi_self)
    have heq : ∀ᶠ a in 𝓝[>] (0 : ℝ), casBdry F (mcoefP ν m n) b - casBdry F (mcoefP ν m n) a =
        ∫ x in a..b, (radialCasimir l r F x * (starRingEnd ℂ) (mcoefP ν m n x) - F x *
          (starRingEnd ℂ) (radialCasimir l r (mcoefP ν m n) x)) * (Real.sinh x : ℂ) := by
      filter_upwards [Ioo_mem_nhdsGT hb] with a ha
      exact (integral_radialCasimir_symm _ _ ha.1 ha.2.le hFc hGc).symm
    have hl2 := (tendsto_const_nhds (x := casBdry F (mcoefP ν m n) b)).sub
      (tendsto_casBdry_phiN_zero s l i hli ν m n)
    rw [sub_zero] at hl2
    exact tendsto_nhds_unique hl (hl2.congr' heq)
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id
  have hlim2 := (tendsto_casBdry_phiN_atTop s l i hli hil ν m n).congr'
    (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb using (hint_b b hb).symm)
  exact tendsto_nhds_unique hlim hlim2

end Lightlike.Lorentz.SL2RPlancherel
