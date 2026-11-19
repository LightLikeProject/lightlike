import Lightlike.Asymptotics.Tauberian.Assembly
import Lightlike.Asymptotics.Tauberian.LocalAssembly
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The comparison at the scale `β = √(a/Δ)`

`comparison_asymp`: for a measure `μ` with the local window bound
`μ[c - ½, c + ½] ≤ K c^{-3/4} e^{2√(a c)}` for `c ≥ X₀`, and `∫ e^{-βx} dμ ≤ Z e^{a/β}` for small `β`,
there are `K', Δ₁` with `|μ(-∞, Δ] - ∫ ψ(Δ - x) dμ| ≤ K' Δ^{-3/4} e^{2√(aΔ)}` for `Δ ≥ Δ₁`,
where `ψ = psiS b β` with `β = √(a/Δ)`.
-/

open MeasureTheory Set Real Filter

noncomputable section

namespace Lightlike.Tauberian

/-- A measure with `e^{-βx}` integrable is finite on compacts. -/
lemma isFiniteMeasureOnCompacts_of_exp (μ : Measure ℝ) {β : ℝ} (hβ : 0 < β)
    (h : Integrable (fun x : ℝ => Real.exp (-β * x)) μ) : IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hε : 0 < Real.exp (-β * R) := Real.exp_pos _
  have hsub : K ⊆ {x : ℝ | Real.exp (-β * R) ≤ ‖Real.exp (-β * x)‖} := by
    intro x hx
    have := hR hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    simp only [mem_setOf_eq, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.2 (by nlinarith [le_abs_self x])
  exact lt_of_le_of_lt (measure_mono hsub) (h.measure_norm_ge_lt_top hε)

/-- **The comparison at the scale `β = √(a/Δ)`.** -/
theorem comparison_asymp (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] {b a K X₀ Z β₁ : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (hβ₁ : 0 < β₁)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) μ)
    (hW : ∀ c : ℝ, X₀ ≤ c →
      μ.real (Icc (c - 1 / 2) (c + 1 / 2)) ≤ K * c ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * c)))
    (hL : ∀ β : ℝ, 0 < β → β < β₁ → ∫ x, Real.exp (-β * x) ∂μ ≤ Z * Real.exp (a / β)) :
    ∃ K' Δ₁ : ℝ, 0 ≤ K' ∧ ∀ Δ : ℝ, Δ₁ ≤ Δ →
      |μ.real (Iic Δ) - ∫ x, psiS b (√(a / Δ)) (Δ - x) ∂μ| ≤
        K' * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * √(a * Δ)) := by
  have hN := kapN_pos hb
  have hM := kapM2_nonneg b
  set C : ℝ := farC b with hC
  have hC0 : 0 ≤ C := by rw [hC]; unfold farC; positivity
  set P : ℝ := 48 + C * a + 8 * C with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  refine ⟨6 * K * P + C * (a + 80) * Z, max (max (2 * X₀) 4) (max a (a / β₁ ^ 2 + 1)), by positivity, fun Δ hΔ => ?_⟩
  have hΔ1 : 2 * X₀ ≤ Δ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΔ
  have hΔ4 : 4 ≤ Δ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΔ
  have hΔa : a ≤ Δ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΔ
  have hΔβ : a / β₁ ^ 2 + 1 ≤ Δ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΔ
  have hΔ0 : 0 < Δ := by linarith
  set β : ℝ := √(a / Δ) with hβ
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hβ2 : β ^ 2 = a / Δ := Real.sq_sqrt (by positivity)
  have hβ1 : β ≤ 1 := by
    have : a / Δ ≤ 1 := by rw [div_le_one hΔ0]; exact hΔa
    calc β = √(a / Δ) := hβ
      _ ≤ √1 := Real.sqrt_le_sqrt this
      _ = 1 := Real.sqrt_one
  have hββ₁ : β < β₁ := by
    rw [hβ, Real.sqrt_lt' hβ₁]
    rw [div_lt_iff₀ hΔ0]
    have : a / β₁ ^ 2 < Δ := by linarith
    rw [div_lt_iff₀ (by positivity)] at this
    linarith only [this]
  obtain ⟨hs1, hs2⟩ := sqrt_div_mul a Δ ha hΔ0
  set Y : ℝ := √(a * Δ) with hY
  have hβΔ : β * Δ = Y := hs1
  have haβ : a / β = Y := hs2
  set n : ℕ := ⌊Δ / 2⌋₊ with hn
  have hn1 : Δ / 2 - 1 < n := Nat.sub_one_lt_floor _
  have hn2 : (n : ℝ) ≤ Δ / 2 := Nat.floor_le (by positivity)
  have hn3 : Δ / 4 ≤ n := by linarith
  have hn4 : 1 ≤ (n : ℝ) := by linarith
  have hX : X₀ ≤ Δ / 2 := by linarith
  have key := comparison_le μ hb hβ0.le hβ1 ha hΔ0 rfl n hn4 hn2 hX hK (hint β hβ0) hW
  refine key.trans ?_
  have hE : 0 ≤ Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by positivity
  have hΔ34 : 0 < Δ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hΔ0 _
  -- (Δ/2)^{-3/4} ≤ 2 Δ^{-3/4}
  have f1 : (Δ / 2) ^ (-(3 / 4 : ℝ)) ≤ 2 * Δ ^ (-(3 / 4 : ℝ)) := by
    have h1 : Δ ^ (-(3 / 4 : ℝ)) = 2 ^ (-(3 / 4 : ℝ)) * (Δ / 2) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
    have h2 : (1 : ℝ) / 2 ≤ 2 ^ (-(3 / 4 : ℝ)) := by
      have : (2 : ℝ) ^ (-1 : ℝ) ≤ 2 ^ (-(3 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_neg_one] at this
      rw [one_div]; exact this
    have hh : 0 < (Δ / 2) ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    rw [h1]; linarith only [mul_le_mul_of_nonneg_right h2 hh.le]
  have hexp1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have f2 : Real.exp (β / 2) ≤ 3 := by
    refine le_trans (Real.exp_le_exp.2 (by linarith : β / 2 ≤ 1)) hexp1.le
  have f3 : (1 + Real.exp β) * Real.exp β ≤ 12 := by
    have : Real.exp β ≤ 3 := le_trans (Real.exp_le_exp.2 hβ1) hexp1.le
    have h0 := Real.exp_pos β
    linarith only [this, mul_le_mul_of_nonneg_left this h0.le]
  have f4 : 4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (C * β ^ 2) + 4 * (C * (β + 1)) ≤ P := by
    have e1 : 2 * (n : ℝ) * (C * β ^ 2) ≤ C * a := by
      have : 2 * (n : ℝ) ≤ Δ := by linarith
      calc 2 * (n : ℝ) * (C * β ^ 2) ≤ Δ * (C * β ^ 2) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = C * a := by rw [hβ2]; field_simp [hΔ0.ne']
    have e2 : 4 * (C * (β + 1)) ≤ 8 * C := by
      linarith only [mul_le_mul_of_nonneg_left hβ1 hC0]
    rw [hP]; linarith only [f3, e1, e2]
  have term1 : K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) * Real.exp (β / 2) *
      (4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (C * β ^ 2) + 4 * (C * (β + 1))) ≤
      6 * K * P * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
    have hbr0 : 0 ≤ 4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (C * β ^ 2) + 4 * (C * (β + 1)) := by positivity
    have hexp0 := Real.exp_pos (2 * Y)
    calc K * (Δ / 2) ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) * Real.exp (β / 2) *
          (4 * ((1 + Real.exp β) * Real.exp β) + 2 * n * (C * β ^ 2) + 4 * (C * (β + 1)))
        ≤ K * (2 * Δ ^ (-(3 / 4 : ℝ))) * Real.exp (2 * Y) * 3 * P := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left f1 hK) le_rfl hexp0.le
            (by positivity)) f2 (Real.exp_pos _).le (by positivity)) f4 hbr0 (by positivity)
      _ = 6 * K * P * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by ring
  have term2 : C * (β ^ 2 + β / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3) * Real.exp (β * Δ) *
      ∫ x, Real.exp (-β * x) ∂μ ≤ C * (a + 80) * Z * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
    have hq : β ^ 2 + β / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3 ≤ (a + 80) * Δ ^ (-(3 / 4 : ℝ)) := by
      have hΔ1' : (1 : ℝ) ≤ Δ := by linarith
      have hinv : 1 / Δ ≤ Δ ^ (-(3 / 4 : ℝ)) := by
        have : Δ ^ (-1 : ℝ) ≤ Δ ^ (-(3 / 4 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hΔ1' (by norm_num)
        rwa [Real.rpow_neg_one, ← one_div] at this
      have hn0 : 0 < (n : ℝ) := by linarith
      have hinvle : 1 / Δ ≤ 1 := by rw [div_le_one hΔ0]; linarith
      have hinv0 : 0 ≤ 1 / Δ := by positivity
      have b1 : β ^ 2 = a * (1 / Δ) := by rw [hβ2]; ring
      have b2 : β / (n : ℝ) ^ 2 ≤ 16 * (1 / Δ) := by
        have : (n : ℝ) ^ 2 ≥ (Δ / 4) ^ 2 := pow_le_pow_left₀ (by positivity) hn3 2
        have h16 : 1 / (n : ℝ) ^ 2 ≤ 16 / Δ ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith only [this]
        calc β / (n : ℝ) ^ 2 ≤ 1 * (1 / (n : ℝ) ^ 2) := by
              rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_right hβ1 (by positivity)
          _ ≤ 16 / Δ ^ 2 := by linarith only [h16]
          _ = 16 * (1 / Δ) * (1 / Δ) := by field_simp
          _ ≤ 16 * (1 / Δ) * 1 := mul_le_mul_of_nonneg_left hinvle (by positivity)
          _ = 16 * (1 / Δ) := mul_one _
      have b3 : 1 / (n : ℝ) ^ 3 ≤ 64 * (1 / Δ) := by
        have : (n : ℝ) ^ 3 ≥ (Δ / 4) ^ 3 := pow_le_pow_left₀ (by positivity) hn3 3
        have h64 : 1 / (n : ℝ) ^ 3 ≤ 64 / Δ ^ 3 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith only [this]
        calc 1 / (n : ℝ) ^ 3 ≤ 64 / Δ ^ 3 := h64
          _ = 64 * (1 / Δ) * (1 / Δ) ^ 2 := by field_simp
          _ ≤ 64 * (1 / Δ) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hinv0 hinvle) (by positivity)
          _ = 64 * (1 / Δ) := mul_one _
      calc β ^ 2 + β / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3 ≤ (a + 80) * (1 / Δ) := by rw [b1]; linarith only [b2, b3]
        _ ≤ (a + 80) * Δ ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hinv (by positivity)
    have hLb := hL β hβ0 hββ₁
    rw [haβ] at hLb
    rw [hβΔ]
    have hexpY := Real.exp_pos Y
    calc C * (β ^ 2 + β / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 3) * Real.exp Y * ∫ x, Real.exp (-β * x) ∂μ
        ≤ C * ((a + 80) * Δ ^ (-(3 / 4 : ℝ))) * Real.exp Y * (Z * Real.exp Y) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC0) hexpY.le) hLb
            (integral_nonneg fun x => (Real.exp_pos _).le) (by positivity)
      _ = C * (a + 80) * Z * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := by
          have : Real.exp (2 * Y) = Real.exp Y * Real.exp Y := by rw [← Real.exp_add]; congr 1; ring
          rw [this]; ring
  calc _ ≤ 6 * K * P * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) +
        C * (a + 80) * Z * Δ ^ (-(3 / 4 : ℝ)) * Real.exp (2 * Y) := add_le_add term1 term2
    _ = _ := by ring

end Lightlike.Tauberian
