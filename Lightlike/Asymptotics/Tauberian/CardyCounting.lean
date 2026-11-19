import Lightlike.Asymptotics.Tauberian.CompareAsymp
import Lightlike.Asymptotics.Tauberian.Rho0Local
import Lightlike.Asymptotics.Tauberian.Rho0Cdf
import Lightlike.Asymptotics.Tauberian.Difference
import Lightlike.Asymptotics.Tauberian.LaplaceEff
import Lightlike.Asymptotics.Tauberian.Negligible
import Lightlike.Asymptotics.Tauberian.Remainder
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Cardy asymptotics of the counting function (MZ (1.8))

`cardy_counting`: under MZ's hypotheses (`SpectralHyp`) and complex modular invariance (MZ (2.2)),
`|σ(-∞, x] - I₀(2√(a x))| ≤ K x^{-3/4} e^{2√(a x)}`, `a = 4π² v`, `I₀(s) = (1/π)∫₀^π e^{s cos θ} dθ`
(the comparison with the crossing kernel of MZ (2.6), Section 5). With the effective asymptotics of `I₀`
this gives MZ (1.8) (`cardy_relative`, `cardy_mz`).
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- The Laplace transform of `ρ₀` on the real axis: `∫ e^{-βx} dρ₀ = e^{a/β}`. -/
lemma integral_exp_rho0 {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    Integrable (fun x : ℝ => Real.exp (-β * x)) (rho0 a) ∧
      ∫ x, Real.exp (-β * x) ∂(rho0 a) = Real.exp (a / β) := by
  have h := integral_rho0 (a := a) (β := β) (M := 1) ha hβ
    (F := fun x : ℝ => Real.exp (-β * x)) (by fun_prop) (fun x hx => by
      rw [abs_of_pos (Real.exp_pos _), one_mul])
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_zero, Real.exp_zero]
  rw [integral_crossing_exp ha hβ]; ring

/-- **The Fourier difference term is negligible**: for `θ < 1` and `c ≥ 0`, eventually
`e^{Y} · c e^{θ Y} / √(a/Δ) ≤ Δ^{-3/4} e^{2Y}` with `Y = √(aΔ)`. -/
lemma eventually_diff_negligible {a θ c : ℝ} (ha : 0 < a) (hθ : θ < 1) (hc : 0 ≤ c) :
    ∀ᶠ Δ : ℝ in atTop, Real.exp (√(a * Δ)) * (c * Real.exp (θ * √(a * Δ)) / √(a / Δ)) ≤
      Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * Δ)) := by
  set θ' : ℝ := max θ 0 with hθ'
  have hθ'1 : θ' < 1 := max_lt hθ one_pos
  set ε : ℝ := (1 - θ') / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have h1 := eventually_le_rpow_neg_mul_exp ha hε0
  have h2 := (tendsto_rpow_mul_exp_neg_sqrt ha hε0).eventually
    (gt_mem_nhds (show (0 : ℝ) < √a / (c + 1) by positivity))
  filter_upwards [h1, h2, eventually_gt_atTop (1 : ℝ)] with Δ hΔ1 hΔ2 hΔ0
  have hΔpos : 0 < Δ := by linarith
  set Y : ℝ := √(a * Δ) with hY
  have hY0 : 0 < Y := Real.sqrt_pos.2 (by positivity)
  have hβ : 0 < √(a / Δ) := Real.sqrt_pos.2 (by positivity)
  have hβΔ : √(a / Δ) * Δ = Y := (sqrt_div_mul a Δ ha hΔpos).1
  -- `1/β = √(Δ/a) ≤ Δ^{3/4} / √a`
  have hinv : 1 / √(a / Δ) ≤ Δ ^ (3 / 4 : ℝ) / √a := by
    have h3 : 1 / √(a / Δ) = √Δ / √a := by
      rw [Real.sqrt_div ha.le, one_div, inv_div]
    rw [h3]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hΔ0.le (by norm_num)
  have hexp : Real.exp (√(a * Δ)) * (c * Real.exp (θ * √(a * Δ)) / √(a / Δ)) =
      Real.exp (Y + θ * Y) * (c * (1 / √(a / Δ))) := by
    rw [Real.exp_add]; ring
  rw [hexp]
  have hθY : θ * Y ≤ θ' * Y := mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le
  have hA : Real.exp (Y + θ * Y) ≤ Real.exp (Y + θ' * Y) := Real.exp_le_exp.2 (by linarith)
  -- `c / β ≤ e^{ε Y}`
  have hB : c * (1 / √(a / Δ)) ≤ Real.exp (ε * Y) := by
    have hpos : 0 < Δ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hΔpos _
    have h4 : Δ ^ (3 / 4 : ℝ) * Real.exp (-(ε * Y)) < √a / (c + 1) := hΔ2
    have h5 : Δ ^ (3 / 4 : ℝ) < √a / (c + 1) * Real.exp (ε * Y) := by
      have := mul_lt_mul_of_pos_right h4 (Real.exp_pos (ε * Y))
      rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at this
    have hs : 0 < √a := Real.sqrt_pos.2 ha
    calc c * (1 / √(a / Δ)) ≤ c * (Δ ^ (3 / 4 : ℝ) / √a) := mul_le_mul_of_nonneg_left hinv hc
      _ ≤ (c + 1) * (Δ ^ (3 / 4 : ℝ) / √a) := by
          have : 0 ≤ Δ ^ (3 / 4 : ℝ) / √a := by positivity
          nlinarith
      _ ≤ (c + 1) * (√a / (c + 1) * Real.exp (ε * Y) / √a) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h5.le hs.le) (by positivity)
      _ = Real.exp (ε * Y) := by field_simp
  have hC : Real.exp (Y + θ' * Y) * Real.exp (ε * Y) = Real.exp ((2 - ε) * Y) := by
    rw [← Real.exp_add]; congr 1; rw [hε]; ring
  calc Real.exp (Y + θ * Y) * (c * (1 / √(a / Δ))) ≤ Real.exp (Y + θ' * Y) * Real.exp (ε * Y) :=
        mul_le_mul hA hB (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((2 - ε) * Y) := hC
    _ ≤ _ := hΔ1

namespace SpectralHyp

variable {σ : Measure ℝ} {v g C β₀ : ℝ}

/-- `Z(β) ≤ (1 + C) e^{a/β}` for `0 < β < β₀`. -/
lemma Z_le (H : SpectralHyp σ v g C β₀) {β : ℝ} (hβ : 0 < β) (hββ₀ : β < β₀) :
    ∫ x, Real.exp (-β * x) ∂σ ≤ (1 + C) * Real.exp (4 * Real.pi ^ 2 * v / β) := by
  have h := H.hasym β hβ hββ₀
  have hC := H.C_nonneg
  have h1 := (abs_le.1 h).2
  have hg : Real.exp ((4 * Real.pi ^ 2 * v - g) / β) ≤ Real.exp (4 * Real.pi ^ 2 * v / β) :=
    Real.exp_le_exp.2 (by
      apply div_le_div_of_nonneg_right _ hβ.le
      linarith [H.hg])
  nlinarith [mul_le_mul_of_nonneg_left hg hC]

end SpectralHyp

/-- **The counting function against the crossing kernel** (the step of MZ Section 5, (5.8)–(5.19), towards (5.1) = (1.8)):
in the shifted variable `x = Δ - c/12` (`v = c/12`, `a = 4π² v`), the counting functions of `σ` and of the crossing kernel
`ρ₀` of MZ (2.6) differ by `O(x^{-3/4} e^{2√(a x)})`; here `ρ₀(-∞, x] = I₀(2√(a x))` (`rho0_real_Iic`),
`I₀(s) = (1/π) ∫₀^π e^{s cos θ} dθ`. -/
theorem cardy_counting {σ : Measure ℝ} {v g C β₀ : ℝ} (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z)) :
    ∃ K Δ₁ : ℝ, 0 ≤ K ∧ ∀ Δ : ℝ, Δ₁ ≤ Δ →
      |σ.real (Iic Δ) - (1 / π) * ∫ θ in (0 : ℝ)..π,
          Real.exp (2 * √(4 * π ^ 2 * v * Δ) * Real.cos θ)| ≤
        K * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(4 * π ^ 2 * v * Δ)) := by
  have hv := H.hv
  have hπ : 0 < π := Real.pi_pos
  set a : ℝ := 4 * π ^ 2 * v with ha_def
  have ha : 0 < a := by positivity
  haveI : IsFiniteMeasureOnCompacts σ := isFiniteMeasureOnCompacts_of_exp σ one_pos (H.hint 1 one_pos)
  haveI : IsFiniteMeasureOnCompacts (rho0 a) :=
    isFiniteMeasureOnCompacts_of_exp (rho0 a) one_pos (integral_exp_rho0 ha one_pos).1
  -- the local bound for `σ`
  obtain ⟨Kσ, X₀, hKσ, hWσ⟩ := local_bound H hmodC (b := 1) (δ := 1 / 2) one_pos (by norm_num)
    (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
  -- comparison for `σ`
  have hC0 := H.C_nonneg
  obtain ⟨K₁, Δ₁, hK₁, h1⟩ := comparison_asymp σ (b := 1) (a := a) (K := Kσ) (X₀ := X₀) (Z := 1 + C)
    (β₁ := β₀) one_pos ha hKσ (by linarith) H.hβ₀ H.hint (fun c hc => hWσ c hc)
    (fun β hβ hββ₀ => H.Z_le hβ hββ₀)
  -- comparison for `ρ₀`
  obtain ⟨K₂, Δ₂, hK₂, h2⟩ := comparison_asymp (rho0 a) (b := 1) (a := a) (K := rho0K a) (X₀ := 1) (Z := 1)
    (β₁ := 1) one_pos ha (rho0K_nonneg ha) zero_le_one one_pos (fun β hβ => (integral_exp_rho0 ha hβ).1)
    (fun c hc => by
      have := rho0_local ha hc
      calc _ ≤ _ := this
        _ = _ := by ring)
    (fun β hβ _ => by rw [(integral_exp_rho0 ha hβ).2]; simp)
  -- the Fourier kernel and the difference of the Laplace transforms
  obtain ⟨gk, hgi, hg0, hgs, hg⟩ := exists_fourier_kernel (b := 1) one_pos
  have hq : ((1 : ℝ) ^ 2 + 4 ^ 2) / (4 * π ^ 2) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith [Real.pi_gt_three]
  obtain ⟨θ, K₃, hθ, hK₃, hD⟩ := delta_bound H hmodC (Λ := 4) (β₁ := 1) (by norm_num) hq one_pos
  have hev := eventually_diff_negligible ha hθ (c := 16 * K₃) (by positivity)
  obtain ⟨Δ₅, hΔ₅⟩ := eventually_atTop.1 hev
  have hN := kapN_pos (one_pos : (0 : ℝ) < 1)
  refine ⟨K₁ + K₂ + 1 / kapN 1, max (max (max Δ₁ Δ₂) (max Δ₅ 4)) a, by positivity, fun Δ hΔ => ?_⟩
  have hΔ1 : Δ₁ ≤ Δ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hΔ
  have hΔ2 : Δ₂ ≤ Δ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hΔ
  have hΔ5 : Δ₅ ≤ Δ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hΔ
  have hΔ4 : 4 ≤ Δ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hΔ
  have hΔa : a ≤ Δ := le_trans (le_max_right _ _) hΔ
  have hΔ0 : 0 < Δ := by linarith
  set β : ℝ := √(a / Δ) with hβ
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  set Y : ℝ := √(a * Δ) with hY
  have haβ : a / β = Y := (sqrt_div_mul a Δ ha hΔ0).2
  have hβ1 : β ≤ 1 := by
    have : a / Δ ≤ 1 := by rw [div_le_one hΔ0]; exact hΔa
    calc β = √(a / Δ) := hβ
      _ ≤ √1 := Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  have hρ : (rho0 a).real (Iic Δ) = (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (2 * Y * Real.cos θ) :=
    rho0_real_Iic ha hΔ0.le
  -- the middle term
  have hmid : |(∫ x, psiS 1 β (Δ - x) ∂σ) - ∫ x, psiS 1 β (Δ - x) ∂(rho0 a)| ≤
      1 / kapN 1 * (Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y)) := by
    have hMnn : 0 ≤ K₃ * Real.exp (θ * Y) := by positivity
    have := smoothed_difference σ (rho0 a) (b := 1) (β := β) (Δ := Δ) (M := K₃ * Real.exp (θ * Y)) one_pos hβ0
      (H.hint β hβ0) (integral_exp_rho0 ha hβ0).1 hgi hg0 hgs hg hMnn (fun t ht => by
        have := hD β t hβ0 hβ1 (by simpa using ht)
        have e : θ * (4 * π ^ 2 * v) / β = θ * Y := by rw [← haβ, ha_def]; ring
        rw [e] at this
        exact this)
    refine this.trans ?_
    have h5 := hΔ₅ Δ hΔ5
    have hβΔ : β * Δ = Y := (sqrt_div_mul a Δ ha hΔ0).1
    rw [hβΔ]
    calc Real.exp Y * (16 * 1 ^ 4 * (K₃ * Real.exp (θ * Y)) / β) / kapN 1
        = 1 / kapN 1 * (Real.exp Y * (16 * K₃ * Real.exp (θ * Y) / β)) := by ring
      _ ≤ 1 / kapN 1 * (Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
  have e1 := h1 Δ hΔ1
  have e2 := h2 Δ hΔ2
  rw [← hρ]
  calc |σ.real (Iic Δ) - (rho0 a).real (Iic Δ)|
      ≤ |σ.real (Iic Δ) - ∫ x, psiS 1 β (Δ - x) ∂σ| +
        |(∫ x, psiS 1 β (Δ - x) ∂σ) - ∫ x, psiS 1 β (Δ - x) ∂(rho0 a)| +
        |(∫ x, psiS 1 β (Δ - x) ∂(rho0 a)) - (rho0 a).real (Iic Δ)| := by
        have := abs_add_three (σ.real (Iic Δ) - ∫ x, psiS 1 β (Δ - x) ∂σ)
          ((∫ x, psiS 1 β (Δ - x) ∂σ) - ∫ x, psiS 1 β (Δ - x) ∂(rho0 a))
          ((∫ x, psiS 1 β (Δ - x) ∂(rho0 a)) - (rho0 a).real (Iic Δ))
        convert this using 2; ring_nf
    _ ≤ K₁ * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) +
        1 / kapN 1 * (Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y)) +
        K₂ * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
        refine add_le_add (add_le_add e1 hmid) ?_
        rw [abs_sub_comm]; exact e2
    _ = _ := by ring

end Lightlike.Tauberian
