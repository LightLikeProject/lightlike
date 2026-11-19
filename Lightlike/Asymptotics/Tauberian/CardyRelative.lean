import Lightlike.Asymptotics.Tauberian.CardyCounting

/-!
# The relative form of the Cardy asymptotics (MZ (1.8))

`cardy_relative`: in the shifted variable `x` of `σ`, with `a = 4π² v` and `Y = √(a x)`,
`|σ(-∞, x] · √(4π Y) e^{-2Y} - 1| ≤ K x^{-1/2}` for large `x`.

`cardy_mz`: the same in MZ's variable `Δ = x + c/12` (`v = c/12`): for `F(Δ) = σ(-∞, Δ - v]`,
`F(Δ) = (1/2π) (3/(cΔ))^{1/4} e^{2π√(cΔ/3)} (1 + O(Δ^{-1/2}))`, MZ (1.8).
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- **MZ (1.8) in the shifted variable**: `σ(-∞, x] = e^{2√(a x)} / √(4π √(a x)) · (1 + O(x^{-1/2}))` with
`x = Δ - c/12`; `cardy_mz` restates it in MZ's variable `Δ`. -/
theorem cardy_relative {σ : Measure ℝ} {v g C β₀ : ℝ} (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z)) :
    ∃ K Δ₁ : ℝ, 0 ≤ K ∧ ∀ Δ : ℝ, Δ₁ ≤ Δ →
      |σ.real (Iic Δ) * (√(4 * π * √(4 * π ^ 2 * v * Δ)) * Real.exp (-(2 * √(4 * π ^ 2 * v * Δ)))) - 1| ≤
        K * Δ ^ (-(1 / 2 : ℝ)) := by
  have hv := H.hv
  have hπ : 0 < π := Real.pi_pos
  set a : ℝ := 4 * π ^ 2 * v with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨K₀, Δ₀, hK₀, h0⟩ := cardy_counting H hmodC
  obtain ⟨C, hC, hI⟩ := besselI0_eff
  refine ⟨K₀ * √(4 * π * √a) + C / (2 * √a), max (max Δ₀ 1) (1 / a), by positivity, fun Δ hΔ => ?_⟩
  have hΔ0' : Δ₀ ≤ Δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΔ
  have hΔ1 : 1 ≤ Δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΔ
  have hΔa : 1 / a ≤ Δ := le_trans (le_max_right _ _) hΔ
  have hΔ0 : 0 < Δ := by linarith
  set u : ℝ := √Δ with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hΔ0
  have hu2 : u ^ 2 = Δ := Real.sq_sqrt hΔ0.le
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  set Y : ℝ := √(a * Δ) with hY
  have hYu : Y = √a * u := Real.sqrt_mul ha.le Δ
  have hY0 : 0 < Y := by rw [hYu]; positivity
  have hY1 : 1 / 2 ≤ Y := by
    have : 1 ≤ a * Δ := by
      have := mul_le_mul_of_nonneg_left hΔa ha.le
      rwa [mul_one_div_cancel ha.ne'] at this
    have h1 : √1 ≤ √(a * Δ) := Real.sqrt_le_sqrt this
    rw [Real.sqrt_one] at h1; linarith
  set F : ℝ := σ.real (Iic Δ) with hF
  set I : ℝ := (1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (2 * Y * Real.cos θ) with hIdef
  have hmain := h0 Δ hΔ0'
  have hbes := hI (2 * Y) (by linarith)
  set W : ℝ := √(4 * π * Y) with hW
  have hW0 : 0 < W := Real.sqrt_pos.2 (by positivity)
  have hW2 : √(2 * π * (2 * Y)) = W := by rw [hW]; congr 1; ring
  rw [hW2] at hbes
  have hIeq : Real.exp (-(2 * Y)) * ((1 / π) * ∫ θ in (0 : ℝ)..π, Real.exp (2 * Y * Real.cos θ)) =
      Real.exp (-(2 * Y)) * I := rfl
  have hE : 0 < Real.exp (-(2 * Y)) := Real.exp_pos _
  -- `W E |F - I| ≤ W Δ^{-3/4}`
  have step1 : W * Real.exp (-(2 * Y)) * |F - I| ≤ K₀ * (W * Δ ^ (-(3 / 4 : ℝ))) := by
    have h1 : |F - I| ≤ K₀ * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := hmain
    calc W * Real.exp (-(2 * Y)) * |F - I| ≤ W * Real.exp (-(2 * Y)) * (K₀ * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K₀ * (W * Δ ^ (-(3 / 4 : ℝ))) * (Real.exp (-(2 * Y)) * Real.exp (2 * Y)) := by ring
      _ = K₀ * (W * Δ ^ (-(3 / 4 : ℝ))) := by rw [← Real.exp_add]; simp
  have hWΔ : W * Δ ^ (-(3 / 4 : ℝ)) = √(4 * π * √a) / u := by
    have hn : Δ ^ (-(3 / 4 : ℝ)) = 1 / (u * √u) := by
      rw [Real.rpow_neg hΔ0.le, rpow_three_quarter hΔ0, one_div]
    have hW' : W = √(4 * π * √a) * √u := by
      rw [hW, hYu, show 4 * π * (√a * u) = 4 * π * √a * u by ring, Real.sqrt_mul (by positivity)]
    have hsu : 0 < √u := Real.sqrt_pos.2 hu0
    rw [hn, hW']; field_simp
  have hΔhalf : Δ ^ (-(1 / 2 : ℝ)) = 1 / u := by
    rw [Real.rpow_neg hΔ0.le, hu, Real.sqrt_eq_rpow]
    exact (one_div _).symm
  have hdecomp : F * (W * Real.exp (-(2 * Y))) - 1 =
      W * Real.exp (-(2 * Y)) * (F - I) + (W * (Real.exp (-(2 * Y)) * I) - 1) := by ring
  have hC' : |W * (Real.exp (-(2 * Y)) * I) - 1| ≤ C / (2 * Y) := hbes
  rw [hdecomp, hΔhalf]
  calc |W * Real.exp (-(2 * Y)) * (F - I) + (W * (Real.exp (-(2 * Y)) * I) - 1)|
      ≤ |W * Real.exp (-(2 * Y)) * (F - I)| + |W * (Real.exp (-(2 * Y)) * I) - 1| := abs_add_le _ _
    _ ≤ K₀ * (√(4 * π * √a) / u) + C / (2 * (√a * u)) := by
        refine add_le_add ?_ (by rw [← hYu]; exact hC')
        rw [abs_mul, abs_of_pos (by positivity : 0 < W * Real.exp (-(2 * Y))), ← hWΔ]
        exact step1
    _ = (K₀ * √(4 * π * √a) + C / (2 * √a)) * (1 / u) := by field_simp

/-- **MZ (1.8) in MZ's variable.** With `c = 12 v` and `F(Δ) = σ(-∞, Δ - c/12]` (the integrated spectral density
`∫₀^Δ ρ` of MZ, written in the variable `x = Δ - c/12` of `σ`), and `a = 4π² v = π² c / 3`:
`|F(Δ) · √(4π √(aΔ)) e^{-2√(aΔ)} - 1| ≤ K Δ^{-1/2}`; here `√(4π √(aΔ)) = 2π (cΔ/3)^{1/4}` and
`2√(aΔ) = 2π √(cΔ/3)`, so this is `F(Δ) = (1/2π) (3/(cΔ))^{1/4} e^{2π√(cΔ/3)} (1 + O(Δ^{-1/2}))`.

Difference from the source (representation): MZ state (1.8) for the density `ρ(Δ) = Σ δ(Δ - Δ_O)` of
their (2.4); here the spectrum is a positive measure `σ` in the shifted variable `x = Δ - c/12`. The
high-temperature hypothesis of `SpectralHyp` is assumed for real `β` only (MZ: `|β| → 0`, `Re β > 0`),
a weaker hypothesis; the complex modular invariance is MZ's (2.2). -/
theorem cardy_mz {σ : Measure ℝ} {v g C β₀ : ℝ} (H : SpectralHyp σ v g C β₀)
    (hmodC : ∀ z : ℂ, 0 < z.re → laplaceC σ z = laplaceC σ (4 * (Real.pi : ℂ) ^ 2 / z)) :
    ∃ K Δ₁ : ℝ, 0 ≤ K ∧ ∀ Δ : ℝ, Δ₁ ≤ Δ →
      |σ.real (Iic (Δ - v)) * (√(4 * π * √(4 * π ^ 2 * v * Δ)) * Real.exp (-(2 * √(4 * π ^ 2 * v * Δ)))) - 1| ≤
        K * Δ ^ (-(1 / 2 : ℝ)) := by
  have hv := H.hv
  have hπ : 0 < π := Real.pi_pos
  set a : ℝ := 4 * π ^ 2 * v with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨K₀, Δ₀, hK₀, h0⟩ := cardy_relative H hmodC
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  refine ⟨4 * K₀ + (2 * v + 2 * √a * v), max (max (Δ₀ + v) (2 * v)) 1, by positivity, fun Δ hΔ => ?_⟩
  have hΔ0' : Δ₀ + v ≤ Δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΔ
  have hΔv : 2 * v ≤ Δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΔ
  have hΔ1 : 1 ≤ Δ := le_trans (le_max_right _ _) hΔ
  have hΔ0 : 0 < Δ := by linarith
  set x : ℝ := Δ - v with hx
  have hx0 : 0 < x := by rw [hx]; linarith
  have hxΔ : Δ / 2 ≤ x := by rw [hx]; linarith
  have hxle : x ≤ Δ := by rw [hx]; linarith
  have h1 := h0 x (by rw [hx]; linarith)
  set F : ℝ := σ.real (Iic x) with hF
  set Yx : ℝ := √(a * x) with hYx
  set YΔ : ℝ := √(a * Δ) with hYΔ
  have hYx0 : 0 < Yx := Real.sqrt_pos.2 (by positivity)
  have hYΔ0 : 0 < YΔ := Real.sqrt_pos.2 (by positivity)
  have hYx2 : Yx ^ 2 = a * x := Real.sq_sqrt (by positivity)
  have hYΔ2 : YΔ ^ 2 = a * Δ := Real.sq_sqrt (by positivity)
  have hYle : Yx ≤ YΔ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxle ha.le)
  set Wx : ℝ := √(4 * π * Yx) with hWx
  set WΔ : ℝ := √(4 * π * YΔ) with hWΔ
  have hWx0 : 0 < Wx := Real.sqrt_pos.2 (by positivity)
  have hWΔ0 : 0 < WΔ := Real.sqrt_pos.2 (by positivity)
  have hWx2 : Wx ^ 2 = 4 * π * Yx := Real.sq_sqrt (by positivity)
  have hWΔ2 : WΔ ^ 2 = 4 * π * YΔ := Real.sq_sqrt (by positivity)
  have hWle : Wx ≤ WΔ := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hYle (by positivity))
  set Ex : ℝ := Real.exp (-(2 * Yx)) with hEx
  set EΔ : ℝ := Real.exp (-(2 * YΔ)) with hEΔ
  have hEx0 : 0 < Ex := Real.exp_pos _
  have hEΔ0 : 0 < EΔ := Real.exp_pos _
  set R : ℝ := WΔ * EΔ / (Wx * Ex) with hR
  have hR0 : 0 ≤ R := by positivity
  -- `R ≤ WΔ / Wx`
  have hEle : EΔ ≤ Ex := Real.exp_le_exp.2 (by linarith)
  have hRle : R ≤ WΔ / Wx := by
    rw [hR, div_le_div_iff₀ (by positivity) hWx0]
    have := mul_le_mul_of_nonneg_left hEle (by positivity : 0 ≤ WΔ * Wx)
    linarith only [this]
  -- `WΔ / Wx ≤ Δ / x`
  have hratio : WΔ / Wx ≤ Δ / x := by
    have t1 : WΔ / Wx ≤ (WΔ / Wx) ^ 2 := by
      have : 1 ≤ WΔ / Wx := by rw [le_div_iff₀ hWx0]; linarith
      calc WΔ / Wx = WΔ / Wx * 1 := (mul_one _).symm
        _ ≤ WΔ / Wx * (WΔ / Wx) := mul_le_mul_of_nonneg_left this (by linarith)
        _ = (WΔ / Wx) ^ 2 := (sq _).symm
    have t2 : (WΔ / Wx) ^ 2 = YΔ / Yx := by
      rw [div_pow, hWΔ2, hWx2]; field_simp
    have t3 : YΔ / Yx ≤ (YΔ / Yx) ^ 2 := by
      have : 1 ≤ YΔ / Yx := by rw [le_div_iff₀ hYx0]; linarith
      calc YΔ / Yx = YΔ / Yx * 1 := (mul_one _).symm
        _ ≤ YΔ / Yx * (YΔ / Yx) := mul_le_mul_of_nonneg_left this (by linarith)
        _ = (YΔ / Yx) ^ 2 := (sq _).symm
    have t4 : (YΔ / Yx) ^ 2 = Δ / x := by
      rw [div_pow, hYΔ2, hYx2]; field_simp
    linarith
  have hR2 : R ≤ 2 := by
    have : Δ / x ≤ 2 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  -- `|R - 1| ≤ (2v + 2√a v) Δ^{-1/2}`
  have hu : 0 < √Δ := Real.sqrt_pos.2 hΔ0
  have huΔ : √Δ ≤ Δ := by
    calc √Δ ≤ √(Δ * Δ) := Real.sqrt_le_sqrt (by nlinarith)
      _ = Δ := Real.sqrt_mul_self hΔ0.le
  have hRup : R - 1 ≤ 2 * v / √Δ := by
    have h1' : Δ / x - 1 = v / x := by
      rw [div_sub_one hx0.ne']; congr 1; rw [hx]; ring
    have h2' : v / x ≤ 2 * v / Δ := by
      rw [div_le_div_iff₀ hx0 hΔ0]; linarith only [mul_le_mul_of_nonneg_left hxΔ hv.le]
    have h3' : 2 * v / Δ ≤ 2 * v / √Δ := div_le_div_of_nonneg_left (by positivity) hu huΔ
    linarith
  have hRlow : 1 - R ≤ 2 * √a * v / √Δ := by
    -- `R ≥ EΔ / Ex = e^{-d}`, `d = 2 (YΔ - Yx)`
    have hRge : EΔ / Ex ≤ R := by
      rw [hR, div_le_div_iff₀ hEx0 (by positivity)]
      have := mul_le_mul_of_nonneg_left hWle (by positivity : 0 ≤ EΔ * Ex)
      linarith only [this]
    have hq : EΔ / Ex = Real.exp (-(2 * (YΔ - Yx))) := by
      rw [hEΔ, hEx, ← Real.exp_sub]; congr 1; ring
    have hd : 1 - 2 * (YΔ - Yx) ≤ Real.exp (-(2 * (YΔ - Yx))) := by
      have := Real.add_one_le_exp (-(2 * (YΔ - Yx))); linarith
    have hdiff : YΔ - Yx ≤ √a * v / √Δ := by
      have e1 : YΔ - Yx = a * v / (YΔ + Yx) := by
        have : (YΔ - Yx) * (YΔ + Yx) = a * v := by
          have : YΔ ^ 2 - Yx ^ 2 = a * v := by rw [hYΔ2, hYx2, hx]; ring
          calc (YΔ - Yx) * (YΔ + Yx) = YΔ ^ 2 - Yx ^ 2 := by ring
            _ = a * v := this
        field_simp; linarith
      have e2 : YΔ = √a * √Δ := Real.sqrt_mul ha.le Δ
      rw [e1]
      calc a * v / (YΔ + Yx) ≤ a * v / YΔ := div_le_div_of_nonneg_left (by positivity) hYΔ0 (by linarith)
        _ = √a * v / √Δ := by
            rw [e2, div_eq_div_iff (mul_ne_zero hsa.ne' hu.ne') hu.ne']
            have hsq : √a * √a = a := Real.mul_self_sqrt ha.le
            calc a * v * √Δ = (√a * √a) * v * √Δ := by rw [hsq]
              _ = √a * v * (√a * √Δ) := by ring
    have : 1 - R ≤ 2 * (YΔ - Yx) := by rw [hq] at hRge; linarith
    calc 1 - R ≤ 2 * (YΔ - Yx) := this
      _ ≤ 2 * (√a * v / √Δ) := by linarith
      _ = 2 * √a * v / √Δ := by ring
  -- `x^{-1/2} ≤ 2 Δ^{-1/2}`
  have hhalf : ∀ y : ℝ, 0 < y → y ^ (-(1 / 2 : ℝ)) = 1 / √y := fun y hy => by
    rw [Real.rpow_neg hy.le, Real.sqrt_eq_rpow]
    exact (one_div _).symm
  have hxu : 1 / √x ≤ 2 * (1 / √Δ) := by
    have hsx : 0 < √x := Real.sqrt_pos.2 hx0
    have : √Δ ≤ 2 * √x := by
      have h4 : √Δ ^ 2 ≤ (2 * √x) ^ 2 := by
        rw [Real.sq_sqrt hΔ0.le, mul_pow, Real.sq_sqrt hx0.le]; linarith
      exact (pow_le_pow_iff_left₀ hu.le (by positivity) (by norm_num)).1 h4
    rw [div_le_iff₀ hsx]
    rw [show 2 * (1 / √Δ) * √x = 2 * √x / √Δ by ring, le_div_iff₀ hu]
    linarith
  rw [hhalf x hx0] at h1
  rw [hhalf Δ hΔ0]
  -- the decomposition
  have hdec : F * (WΔ * EΔ) - 1 = (F * (Wx * Ex) - 1) * R + (R - 1) := by
    rw [hR]; field_simp; ring
  rw [hdec]
  have hRabs : |R - 1| ≤ (2 * v + 2 * √a * v) * (1 / √Δ) := by
    rw [abs_le]; constructor
    · rw [mul_one_div]
      have e : (2 * v + 2 * √a * v) / √Δ = 2 * v / √Δ + 2 * √a * v / √Δ := by ring
      have : 0 ≤ 2 * v / √Δ := by positivity
      rw [e]; linarith only [hRlow, this]
    · rw [mul_one_div]
      have : 0 ≤ 2 * √a * v / √Δ := by positivity
      have e : (2 * v + 2 * √a * v) / √Δ = 2 * v / √Δ + 2 * √a * v / √Δ := by ring
      rw [e]; linarith
  calc |(F * (Wx * Ex) - 1) * R + (R - 1)| ≤ |F * (Wx * Ex) - 1| * R + |R - 1| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hR0]
    _ ≤ K₀ * (1 / √x) * 2 + (2 * v + 2 * √a * v) * (1 / √Δ) := by
        refine add_le_add ?_ hRabs
        exact mul_le_mul h1 hR2 hR0 (by positivity)
    _ ≤ K₀ * (2 * (1 / √Δ)) * 2 + (2 * v + 2 * √a * v) * (1 / √Δ) := by
        have := mul_le_mul_of_nonneg_left hxu hK₀
        linarith
    _ = (4 * K₀ + (2 * v + 2 * √a * v)) * (1 / √Δ) := by ring

end Lightlike.Tauberian
