import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalSpherical
import Lightlike.Lorentz.SL2RPlancherel.LadderClosed
import Lightlike.Lorentz.SL2RPlancherel.LadderLocal

/-!
# Symmetries of the principal-series matrix coefficients

The reflection `x ↦ -x` sends `e_k` to `e_{-k}`, so `Φ^ν_{-m,-n} = Φ^ν_{m,n}` (`mcoefP_neg_neg`).
Conjugating `a(ξ)` by the rotation `k_{π/2}` gives `a(-ξ)`, so
`Φ^ν_{m,n}(-ξ) = (-1)^{m-n} Φ^ν_{m,n}(ξ)` (`mcoefP_neg_arg`); with unitarity,
`Φ^ν_{m,n}(ξ) = conj Φ^ν_{n,m}(-ξ)` (`mcoefP_swap`) and
`Φ^ν_{m,n} = (-1)^{n-m} conj Φ^ν_{n,m}` (`mcoefP_eq_conj`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (pairing the ladder chains with the matrix
coefficients), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology Lightlike.Lorentz.SL2R

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

end Lightlike.Lorentz.SL2RPlancherel
