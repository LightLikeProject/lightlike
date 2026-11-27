import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical
import Lightlike.Lorentz.SL2RPlancherel.LadderClosed
import Lightlike.Lorentz.SL2RPlancherel.LadderLocal
import Lightlike.Lorentz.SL2RPlancherel.LadderRecursion
import Lightlike.Lorentz.SL2RPlancherel.KTypeLR

/-!
# Pairing the ladder chains with the principal-series matrix coefficients

The reflection `x ↦ -x` sends `e_k` to `e_{-k}`, so `Φ^ν_{-m,-n} = Φ^ν_{m,n}` (`mcoefP_neg_neg`).
Conjugating `a(ξ)` by the rotation `k_{π/2}` gives `a(-ξ)`, so
`Φ^ν_{m,n}(-ξ) = (-1)^{m-n} Φ^ν_{m,n}(ξ)` (`mcoefP_neg_arg`); with unitarity,
`Φ^ν_{m,n}(ξ) = conj Φ^ν_{n,m}(-ξ)` (`mcoefP_swap`) and
`Φ^ν_{m,n} = (-1)^{n-m} conj Φ^ν_{n,m}` (`mcoefP_eq_conj`); conjugation flips `ν`,
`conj Φ^ν_{m,n} = Φ^{-ν}_{-m,-n}` (`conj_mcoefP`).
The ladders are adjoint on `(0, ∞)` for `sinh ξ dξ` (`integral_Ioi_ladUp_mul_conj`), and the
matrix coefficients satisfy `ladDown_{n,-m} Φ_{m,n} = -(w + n) Φ_{m,n-1}`, so pairing a ladder chain
with `Φ` lowers both down to the spherical base: for smooth compactly supported `G`,
`∫_{ξ>0} profile_k G conj Φ^ν_{0,k} sinh = ∏_{j<k} conj(-(w + j + 1)) · (1/2) Ĝ(ν/2)`
(`integral_profile_mul_conj_mcoefP`) and
`∫_{ξ>0} Hc_{r,l} G conj Φ^ν_{-r,l} sinh
= ∏_{j<l} conj(-(w_ν + j + 1)) · (-1)^r ∏_{j<r} conj(-(w_{-ν} + j + 1)) · (1/2) Ĝ(ν/2)`
(`integral_Hc_mul_conj_mcoefP`), `Ĝ = sphTransformH G`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (pairing the ladder chains with the matrix
coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `e_k(-x) = e_{-k}(x)`. -/
lemma kVecP_neg (ν : ℝ) (k : ℤ) (x : ℝ) : kVecP ν k (-x) = kVecP ν (-k) x := by
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  have h3 : -(x : ℂ) + I ≠ 0 := by
    rw [show -(x : ℂ) + I = -((x : ℂ) - I) by ring]; exact neg_ne_zero.2 hm
  simp only [kVecP, neg_sq, Complex.ofReal_neg, zpow_neg, ← inv_zpow, inv_div]
  congr 2
  rw [div_eq_div_iff h3 hm]
  ring

/-- **The reflection symmetry**: `Φ^ν_{-m,-n} = Φ^ν_{m,n}`. -/
theorem mcoefP_neg_neg (ν ξ : ℝ) (m n : ℤ) : mcoefP ν (-m) (-n) ξ = mcoefP ν m n ξ := by
  rw [mcoefP_eq_integral, mcoefP_eq_integral, ← integral_neg_eq_self]
  congr 1
  funext x
  simp only [kVecP_neg, mul_neg, neg_neg]

/-- `k_{π/2} a(ξ) k_{-π/2} = a(-ξ)`. -/
lemma rot_mul_aR_mul_rot (ξ : ℝ) : rot (Real.pi / 2) * aR ξ * rot (-(Real.pi / 2)) = aR (-ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aR, diagSL, Matrix.mul_apply, Fin.sum_univ_two, neg_div, Real.exp_neg]

/-- **The Weyl symmetry**: `Φ^ν_{m,n}(-ξ) = (-1)^{m-n} Φ^ν_{m,n}(ξ)`. -/
theorem mcoefP_neg_arg (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n (-ξ) = (-1 : ℂ) ^ (m - n) * mcoefP ν m n ξ := by
  have h := inner_kVecL2_kak ν (Real.pi / 2) ξ (-(Real.pi / 2)) m n
  rw [rot_mul_aR_mul_rot] at h
  have h' : mcoefP ν m n (-ξ) = _ := h
  rw [h']
  congr 1
  have e : -(2 * ((m : ℂ) * ((Real.pi / 2 : ℝ) : ℂ) + (n : ℂ) * ((-(Real.pi / 2) : ℝ) : ℂ)) * I) =
      ((m - n : ℤ) : ℂ) * (-(Real.pi * I)) := by
    push_cast; ring
  rw [e, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]

/-- **Unitarity**: `Φ^ν_{m,n}(ξ) = conj Φ^ν_{n,m}(-ξ)`. -/
theorem mcoefP_swap (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n ξ = (starRingEnd ℂ) (mcoefP ν n m (-ξ)) := by
  rw [show mcoefP ν n m (-ξ) =
      inner ℂ (kVecL2 ν n) (principalSeries 0 ν (aR (-ξ)) (kVecL2 ν m)) from rfl,
    inner_conj_symm, inner_aR_neg_kVecL2]

/-- `Φ^ν_{m,n} = (-1)^{n-m} conj Φ^ν_{n,m}`. -/
theorem mcoefP_eq_conj (ν ξ : ℝ) (m n : ℤ) :
    mcoefP ν m n ξ = (-1 : ℂ) ^ (n - m) * (starRingEnd ℂ) (mcoefP ν n m ξ) := by
  rw [mcoefP_swap, mcoefP_neg_arg, map_mul, map_zpow₀, map_neg, map_one]

/-- `∫_a^b f → ∫_{(0,b]} f` as `a → 0⁺`, for `f` integrable on `(0, b]`. -/
lemma tendsto_intervalIntegral_zero_right {f : ℝ → ℂ} {b : ℝ} (hb : 0 < b)
    (hf : IntegrableOn f (Ioc 0 b)) :
    Tendsto (fun a => ∫ x in a..b, f x) (𝓝[>] 0) (𝓝 (∫ x in Ioc 0 b, f x)) := by
  have hg : Integrable ((Ioc 0 b).indicator f) := hf.integrable_indicator measurableSet_Ioc
  have hcont : Continuous fun a => ∫ x in (0 : ℝ)..a, (Ioc 0 b).indicator f x :=
    intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable) 0
  have hv : (∫ x in (0 : ℝ)..b, (Ioc 0 b).indicator f x) = ∫ x in Ioc 0 b, f x := by
    rw [intervalIntegral.integral_of_le hb.le, setIntegral_indicator measurableSet_Ioc, inter_self]
  have key : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∫ x in a..b, f x =
      (∫ x in Ioc 0 b, f x) - ∫ x in (0 : ℝ)..a, (Ioc 0 b).indicator f x := by
    filter_upwards [Ioo_mem_nhdsGT hb] with a ha
    rw [← hv, intervalIntegral.integral_interval_sub_left hg.intervalIntegrable
      hg.intervalIntegrable]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le ha.2.le] at hx
    exact (indicator_of_mem (show x ∈ Ioc 0 b from ⟨ha.1.trans_le hx.1, hx.2⟩) f).symm
  have hlim : Tendsto (fun a => (∫ x in Ioc 0 b, f x) -
      ∫ x in (0 : ℝ)..a, (Ioc 0 b).indicator f x) (𝓝[>] 0)
      (𝓝 ((∫ x in Ioc 0 b, f x) - 0)) := by
    refine tendsto_const_nhds.sub ?_
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  rw [sub_zero] at hlim
  exact hlim.congr' (key.mono fun a h => h.symm)

/-- **The ladders are adjoint on `(0, ∞)`** for `sinh ξ dξ`, when `F` vanishes beyond `R` and the
boundary term `F conj(G) sinh` tends to `0` at `0`. -/
theorem integral_Ioi_ladUp_mul_conj (l r : ℝ) {F G : ℝ → ℂ} {R : ℝ}
    (hF : ContDiffOn ℝ 1 F (Ioi 0)) (hG : ContDiffOn ℝ 1 G (Ioi 0))
    (hR : ∀ ξ, R < ξ → F ξ = 0)
    (h0 : Tendsto (fun a => F a * (starRingEnd ℂ) (G a) * (Real.sinh a : ℂ)) (𝓝[>] 0) (𝓝 0))
    (h1 : IntegrableOn (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ))
      (Ioi 0))
    (h2 : IntegrableOn
      (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) (Ioi 0)) :
    ∫ ξ in Ioi 0, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in Ioi 0, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  set b := max R 0 + 1 with hbdef
  have hb : 0 < b := by positivity
  have hRb : R < b := by have := le_max_left R 0; linarith
  have hFb : F b = 0 := hR b hRb
  have hvanF : ∀ ξ, b < ξ → F ξ = 0 := fun ξ h => hR ξ (hRb.trans h)
  have hvanD : ∀ ξ, b < ξ → deriv F ξ = 0 := fun ξ h => by
    have : F =ᶠ[𝓝 ξ] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds (hRb.trans h)] with y hy using hR y hy
    rw [this.deriv_eq, deriv_const]
  have hI1 : ∫ ξ in Ioi 0, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in Ioc 0 b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun ξ hξ => ?_
    have hξb : b < ξ := by
      by_contra h; push Not at h; exact hξ.2 ⟨hξ.1, h⟩
    simp [ladUp, hvanF ξ hξb, hvanD ξ hξb]
  have hI2 : ∫ ξ in Ioi 0, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in Ioc 0 b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun ξ hξ => ?_
    have hξb : b < ξ := by
      by_contra h; push Not at h; exact hξ.2 ⟨hξ.1, h⟩
    simp [hvanF ξ hξb]
  have hl1 := tendsto_intervalIntegral_zero_right hb (h1.mono_set Ioc_subset_Ioi_self)
  have hl2 := tendsto_intervalIntegral_zero_right hb (h2.mono_set Ioc_subset_Ioi_self)
  have heq : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      (0 - F a * (starRingEnd ℂ) (G a) * (Real.sinh a : ℂ)) +
        ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT hb] with a ha
    rw [ladder_adjoint_boundary l r ha.1 ha.2.le hF hG, hFb]
    ring
  have hl3 := ((tendsto_const_nhds (x := (0 : ℂ))).sub h0).add hl2
  have := tendsto_nhds_unique hl1 (hl3.congr' heq)
  rw [hI1, hI2, this]
  ring

lemma continuous_mcoefP (ν : ℝ) (m n : ℤ) : Continuous (mcoefP ν m n) :=
  continuous_iff_continuousAt.2 fun ξ => (hasDerivAt_mcoefP ν m n ξ).continuousAt

lemma contDiff_one_mcoefP (ν : ℝ) (m n : ℤ) : ContDiff ℝ 1 (mcoefP ν m n) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun ξ => (hasDerivAt_mcoefP ν m n ξ).differentiableAt, ?_⟩
  have : deriv (mcoefP ν m n) = fun ξ => (wP ν - n) / 2 * mcoefP ν m (n + 1) ξ +
      (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ := funext fun ξ => (hasDerivAt_mcoefP ν m n ξ).deriv
  rw [this]
  exact (continuous_const.mul (continuous_mcoefP ν m (n + 1))).add
    (continuous_const.mul (continuous_mcoefP ν m (n - 1)))

/-- `Φ^ν_{0,0}` is real. -/
lemma conj_mcoefP_zero_zero (ν ξ : ℝ) : (starRingEnd ℂ) (mcoefP ν 0 0 ξ) = mcoefP ν 0 0 ξ := by
  have h := mcoefP_eq_conj ν ξ 0 0
  simp only [sub_self, zpow_zero, one_mul] at h
  exact h.symm

lemma hasCompactSupport_profile (k : ℕ) {G : ℝ → ℂ} (hc : HasCompactSupport G) :
    HasCompactSupport (profile k G) :=
  (hasCompactSupport_comp_cosh (hasCompactSupport_iteratedDeriv hc k)).mul_left

/-- An integrand `F conj(Φ) sinh` with `F` continuous and compactly supported is integrable. -/
lemma integrableOn_mul_conj_sinh {F Φ : ℝ → ℂ} (hF : Continuous F) (hc : HasCompactSupport F)
    (hΦ : Continuous Φ) :
    IntegrableOn (fun ξ => F ξ * (starRingEnd ℂ) (Φ ξ) * (Real.sinh ξ : ℂ)) (Ioi 0) := by
  refine Integrable.integrableOn ?_
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hF.mul (Complex.continuous_conj.comp hΦ)).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)
  · exact (hc.mul_right).mul_right

lemma tendsto_mul_conj_sinh {F Φ : ℝ → ℂ} (hF : Continuous F) (hΦ : Continuous Φ) :
    Tendsto (fun a => F a * (starRingEnd ℂ) (Φ a) * (Real.sinh a : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun a => F a * (starRingEnd ℂ) (Φ a) * (Real.sinh a : ℂ) :=
    (hF.mul (Complex.continuous_conj.comp hΦ)).mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh)
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-- **The profile chain against the matrix coefficients**:
`∫_{ξ>0} profile_k G(ξ) conj Φ^ν_{0,k}(ξ) sinh ξ dξ = ∏_{j<k} conj(-(w + j + 1)) · (1/2) Ĝ(ν/2)`. -/
theorem integral_profile_mul_conj_mcoefP (ν : ℝ) (k : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    ∫ ξ in Ioi 0, profile k G ξ * (starRingEnd ℂ) (mcoefP ν 0 k ξ) * (Real.sinh ξ : ℂ) =
      (∏ j ∈ Finset.range k, (starRingEnd ℂ) (-(wP ν + ((j : ℂ) + 1)))) *
        ((1 / 2) * sphTransformH G (ν / 2)) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero]
    rw [← integral_sinh_mul_mcoefP_zero_zero ν hG.continuous hc]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [profile, pow_zero, Complex.ofReal_one, one_mul, iteratedDeriv_zero,
      conj_mcoefP_zero_zero]
    ring
  | succ k ih =>
    have hPk := contDiff_profile k hG
    obtain ⟨R, -, hR'⟩ := exists_eq_zero_of_hasCompactSupport (hasCompactSupport_profile k hc)
    have hR : ∀ ξ, R < ξ → profile k G ξ = 0 := fun ξ h => hR' ξ h.le
    have hdown : ∀ ξ ∈ Ioi (0 : ℝ), ladDown ((k : ℝ) + 1) 0 (mcoefP ν 0 ((k : ℤ) + 1)) ξ =
        -(wP ν + ((k : ℂ) + 1)) * mcoefP ν 0 k ξ := by
      intro ξ hξ
      have h := ladDown_mcoefP ν 0 ((k : ℤ) + 1) (ne_of_gt hξ)
      push_cast at h
      simpa using h
    have h1 : IntegrableOn (fun ξ => ladUp (k : ℝ) 0 (profile k G) ξ *
        (starRingEnd ℂ) (mcoefP ν 0 ((k : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_mul_conj_sinh (contDiff_profile (k + 1) hG).continuous
        (hasCompactSupport_profile (k + 1) hc) (continuous_mcoefP ν 0 ((k : ℤ) + 1))).congr_fun
        (fun ξ hξ => by simp only [ladUp_profile k hG hξ]) measurableSet_Ioi
    have h2 : IntegrableOn (fun ξ => profile k G ξ *
        (starRingEnd ℂ) (ladDown ((k : ℝ) + 1) 0 (mcoefP ν 0 ((k : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_mul_conj_sinh hPk.continuous (hasCompactSupport_profile k hc)
        (show Continuous fun ξ => -(wP ν + ((k : ℂ) + 1)) * mcoefP ν 0 k ξ from
          continuous_const.mul (continuous_mcoefP ν 0 k))).congr_fun
        (fun ξ hξ => by simp only [hdown ξ hξ]) measurableSet_Ioi
    have hadj := integral_Ioi_ladUp_mul_conj (k : ℝ) 0 (hPk.of_le (by norm_cast)).contDiffOn
      (contDiff_one_mcoefP ν 0 ((k : ℤ) + 1)).contDiffOn hR
      (tendsto_mul_conj_sinh hPk.continuous (continuous_mcoefP ν 0 ((k : ℤ) + 1))) h1 h2
    have e1 : ∫ ξ in Ioi 0, profile (k + 1) G ξ *
        (starRingEnd ℂ) (mcoefP ν 0 ((k + 1 : ℕ) : ℤ) ξ) * (Real.sinh ξ : ℂ) =
        ∫ ξ in Ioi 0, ladUp (k : ℝ) 0 (profile k G) ξ *
          (starRingEnd ℂ) (mcoefP ν 0 ((k : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => by
        simp only [ladUp_profile k hG hξ, Nat.cast_succ]
    have e2 : ∫ ξ in Ioi 0, profile k G ξ *
        (starRingEnd ℂ) (ladDown ((k : ℝ) + 1) 0 (mcoefP ν 0 ((k : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ) =
        (starRingEnd ℂ) (-(wP ν + ((k : ℂ) + 1))) *
          ∫ ξ in Ioi 0, profile k G ξ * (starRingEnd ℂ) (mcoefP ν 0 k ξ) * (Real.sinh ξ : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
      simp only [hdown ξ hξ, map_mul]
      ring
    rw [e1, hadj, e2, ih, Finset.prod_range_succ]
    ring

lemma conj_wP_eq (ν : ℝ) : (starRingEnd ℂ) (wP ν) = wP (-ν) := by
  simp only [wP, map_div₀, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_one,
    map_ofNat, Complex.ofReal_neg]
  ring

/-- `conj e^ν_k = e^{-ν}_{-k}`. -/
lemma conj_kVecP (ν : ℝ) (k : ℤ) (x : ℝ) :
    (starRingEnd ℂ) (kVecP ν k x) = kVecP (-ν) (-k) x := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  simp only [kVecP]
  rw [ofReal_cpow_eq_exp h1, ofReal_cpow_eq_exp h1]
  simp only [map_mul, ← Complex.exp_conj, map_zpow₀, map_div₀, map_sub, map_add, map_one,
    map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  · congr 1; ring
  · rw [zpow_neg, ← inv_zpow, inv_div]; congr 1; ring

/-- `conj Φ^ν_{m,n} = Φ^{-ν}_{-m,-n}`. -/
theorem conj_mcoefP (ν ξ : ℝ) (m n : ℤ) :
    (starRingEnd ℂ) (mcoefP ν m n ξ) = mcoefP (-ν) (-m) (-n) ξ := by
  rw [mcoefP_eq_integral, mcoefP_eq_integral, ← integral_conj]
  congr 1
  funext x
  simp only [map_mul, conj_kVecP, neg_neg, ← Complex.exp_conj, map_neg,
    Complex.conj_ofReal, conj_wP_eq]

/-- The spherical transform is even. -/
lemma sphTransformH_neg (F : ℝ → ℂ) (ρ : ℝ) : sphTransformH F (-ρ) = sphTransformH F ρ := by
  rw [sphTransformH_eq_integral_abel, sphTransformH_eq_integral_abel, ← integral_neg_eq_self]
  congr 1
  funext t
  simp only [abelTransform, Real.cosh_neg]
  congr 2
  push_cast
  ring

lemma integrableOn_Ioi_of_eq_zero {f : ℝ → ℂ} (hf : Continuous f) {B : ℝ}
    (hB : ∀ ξ, B ≤ ξ → f ξ = 0) : IntegrableOn f (Ioi 0) := by
  have h : Integrable ((Icc 0 B).indicator f) :=
    (hf.continuousOn.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine h.integrableOn.congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
  by_cases h' : ξ ≤ B
  · exact indicator_of_mem (show ξ ∈ Icc 0 B from ⟨le_of_lt hξ, h'⟩) f
  · rw [indicator_of_notMem (fun h'' => h' h''.2), hB ξ (le_of_lt (not_le.1 h'))]

lemma Hc_zero (r : ℕ) (G : ℝ → ℂ) (ξ : ℝ) : Hc r G 0 ξ = profile r G ξ := by
  simp [Hc, profile, uRec]

/-- **The ladder chain `Hc` against the matrix coefficients**:
`∫_{ξ>0} Hc_{r,l} G(ξ) conj Φ^ν_{-r,l}(ξ) sinh ξ dξ
= ∏_{j<l} conj(-(w_ν + j + 1)) · (-1)^r ∏_{j<r} conj(-(w_{-ν} + j + 1)) · (1/2) Ĝ(ν/2)`. -/
theorem integral_Hc_mul_conj_mcoefP (ν : ℝ) (r l : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) :
    ∫ ξ in Ioi 0, Hc r G l ξ * (starRingEnd ℂ) (mcoefP ν (-r) l ξ) * (Real.sinh ξ : ℂ) =
      (∏ j ∈ Finset.range l, (starRingEnd ℂ) (-(wP ν + ((j : ℂ) + 1)))) *
        ((-1 : ℂ) ^ r * ((∏ j ∈ Finset.range r, (starRingEnd ℂ) (-(wP (-ν) + ((j : ℂ) + 1)))) *
          ((1 / 2) * sphTransformH G (ν / 2)))) := by
  obtain ⟨B, -, hB⟩ := Hc_eq_zero r hc
  induction l with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, one_mul, Nat.cast_zero]
    have hsign : (-1 : ℂ) ^ ((0 : ℤ) - r) = (-1) ^ r := by
      rw [zero_sub, zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
    have hconj : ∀ ξ, (starRingEnd ℂ) (mcoefP ν (-r) 0 ξ) =
        (-1 : ℂ) ^ r * (starRingEnd ℂ) (mcoefP (-ν) 0 r ξ) := fun ξ => by
      rw [conj_mcoefP, neg_neg, neg_zero, mcoefP_eq_conj, hsign]
    have h3 := integral_profile_mul_conj_mcoefP (-ν) r hG hc
    rw [neg_div, sphTransformH_neg] at h3
    rw [← h3, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    simp only [Hc_zero, hconj]
    ring
  | succ l ih =>
    have hdown : ∀ ξ ∈ Ioi (0 : ℝ), ladDown ((l : ℝ) + 1) (r : ℝ) (mcoefP ν (-r) ((l : ℤ) + 1)) ξ =
        -(wP ν + ((l : ℂ) + 1)) * mcoefP ν (-r) l ξ := by
      intro ξ hξ
      have h := ladDown_mcoefP ν (-r) ((l : ℤ) + 1) (ne_of_gt hξ)
      push_cast at h
      simpa using h
    have h1 : IntegrableOn (fun ξ => ladUp (l : ℝ) (r : ℝ) (Hc r G l) ξ *
        (starRingEnd ℂ) (mcoefP ν (-r) ((l : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_Ioi_of_eq_zero (B := B) (((continuous_Hc r hG (l + 1)).mul
        (Complex.continuous_conj.comp (continuous_mcoefP ν (-r) ((l : ℤ) + 1)))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh))
        (fun ξ hξ => by simp [hB (l + 1) ξ hξ])).congr_fun
        (fun ξ hξ => by simp only [ladUp_Hc r hG l hξ, Pi.mul_apply, Function.comp_apply])
        measurableSet_Ioi
    have h2 : IntegrableOn (fun ξ => Hc r G l ξ *
        (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (r : ℝ) (mcoefP ν (-r) ((l : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ)) (Ioi 0) :=
      (integrableOn_Ioi_of_eq_zero (B := B) (((continuous_Hc r hG l).mul
        (Complex.continuous_conj.comp (show Continuous fun ξ =>
          -(wP ν + ((l : ℂ) + 1)) * mcoefP ν (-r) l ξ from
          continuous_const.mul (continuous_mcoefP ν (-r) l)))).mul
        (Complex.continuous_ofReal.comp Real.continuous_sinh))
        (fun ξ hξ => by simp [hB l ξ hξ])).congr_fun
        (fun ξ hξ => by simp only [hdown ξ hξ, Pi.mul_apply, Function.comp_apply])
        measurableSet_Ioi
    have hadj := integral_Ioi_ladUp_mul_conj (l : ℝ) (r : ℝ)
      ((contDiffOn_Hc r hG l).of_le (by norm_cast))
      (contDiff_one_mcoefP ν (-r) ((l : ℤ) + 1)).contDiffOn (fun ξ h => hB l ξ h.le)
      (tendsto_mul_conj_sinh (continuous_Hc r hG l) (continuous_mcoefP ν (-r) ((l : ℤ) + 1)))
      h1 h2
    have e1 : ∫ ξ in Ioi 0, Hc r G (l + 1) ξ *
        (starRingEnd ℂ) (mcoefP ν (-r) ((l + 1 : ℕ) : ℤ) ξ) * (Real.sinh ξ : ℂ) =
        ∫ ξ in Ioi 0, ladUp (l : ℝ) (r : ℝ) (Hc r G l) ξ *
          (starRingEnd ℂ) (mcoefP ν (-r) ((l : ℤ) + 1) ξ) * (Real.sinh ξ : ℂ) :=
      setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => by
        simp only [ladUp_Hc r hG l hξ, Nat.cast_succ]
    have e2 : ∫ ξ in Ioi 0, Hc r G l ξ *
        (starRingEnd ℂ) (ladDown ((l : ℝ) + 1) (r : ℝ) (mcoefP ν (-r) ((l : ℤ) + 1)) ξ) *
          (Real.sinh ξ : ℂ) =
        (starRingEnd ℂ) (-(wP ν + ((l : ℂ) + 1))) *
          ∫ ξ in Ioi 0, Hc r G l ξ * (starRingEnd ℂ) (mcoefP ν (-r) l ξ) * (Real.sinh ξ : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
      simp only [hdown ξ hξ, map_mul]
      ring
    rw [e1, hadj, e2, ih, Finset.prod_range_succ]
    ring

end Lightlike.Lorentz.SL2RPlancherel
