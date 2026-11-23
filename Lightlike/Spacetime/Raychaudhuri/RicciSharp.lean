import Lightlike.Spacetime.Raychaudhuri.RicciBound

/-!
# Sharpness of the Ricci-bound focusing time (GE3, Tier 1)

`focusing_ricci_bound` says that `Θ' ≤ -Θ²/m - c` on `[0, L)` forces
`L ≤ (m/√(mc)) (π/2 + arctan(Θ(0)/√(mc)))`. Here we show that this bound cannot be improved: the explicit
solution `Θ(s) = √(mc) · tan(arctan(Θ₀/√(mc)) - (√(mc)/m) s)` solves the Riccati *equality*
`Θ' = -Θ²/m - c` on exactly `[0, L*)`, with `L*` the bound, starts at `Θ₀`, and tends to `-∞` at `L*`.
-/

open Set Filter Topology Real

namespace Lightlike

/-- The extremal expansion profile of the Riccati equation `Θ' = -Θ²/m - c` with `Θ(0) = Θ₀`. -/
noncomputable def riccatiProfile (m c Θ₀ : ℝ) (s : ℝ) : ℝ :=
  √(m * c) * tan (arctan (Θ₀ / √(m * c)) - √(m * c) / m * s)

/-- The blow-up time of `riccatiProfile`, equal to the bound of `focusing_ricci_bound`. -/
noncomputable def riccatiTime (m c Θ₀ : ℝ) : ℝ :=
  m / √(m * c) * (π / 2 + arctan (Θ₀ / √(m * c)))

theorem riccatiProfile_zero {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (Θ₀ : ℝ) :
    riccatiProfile m c Θ₀ 0 = Θ₀ := by
  have hr0 : 0 < √(m * c) := Real.sqrt_pos.2 (mul_pos hm hc)
  simp only [riccatiProfile, mul_zero, sub_zero, tan_arctan]
  field_simp

/-- The profile in the angle variable lies in `(-π/2, π/2)` before the blow-up time. -/
theorem riccatiProfile_angle_mem {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (Θ₀ : ℝ) {s : ℝ}
    (hs : s ∈ Ico 0 (riccatiTime m c Θ₀)) :
    arctan (Θ₀ / √(m * c)) - √(m * c) / m * s ∈ Ioo (-(π / 2)) (π / 2) := by
  have hr0 : 0 < √(m * c) := Real.sqrt_pos.2 (mul_pos hm hc)
  obtain ⟨h0, h1⟩ := hs
  have hq : 0 < √(m * c) / m := div_pos hr0 hm
  have key : √(m * c) / m * s < π / 2 + arctan (Θ₀ / √(m * c)) := by
    have : √(m * c) / m * (m / √(m * c) * (π / 2 + arctan (Θ₀ / √(m * c)))) =
        π / 2 + arctan (Θ₀ / √(m * c)) := by field_simp
    rw [← this]
    exact mul_lt_mul_of_pos_left h1 hq
  constructor
  · linarith
  · have := arctan_lt_pi_div_two (Θ₀ / √(m * c))
    nlinarith [mul_nonneg hq.le h0]

/-- **The profile solves the Riccati equality** `Θ' = -Θ²/m - c` on `[0, riccatiTime)`. -/
theorem riccatiProfile_hasDerivAt {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (Θ₀ : ℝ) {s : ℝ}
    (hs : s ∈ Ico 0 (riccatiTime m c Θ₀)) :
    HasDerivAt (riccatiProfile m c Θ₀)
      (-(riccatiProfile m c Θ₀ s) ^ 2 / m - c) s := by
  have hmc : 0 < m * c := mul_pos hm hc
  have hr0 : 0 < √(m * c) := Real.sqrt_pos.2 hmc
  have hr2 : √(m * c) ^ 2 = m * c := Real.sq_sqrt hmc.le
  have hx := riccatiProfile_angle_mem hm hc Θ₀ hs
  have hcos : 0 < cos (arctan (Θ₀ / √(m * c)) - √(m * c) / m * s) := cos_pos_of_mem_Ioo hx
  have hin : HasDerivAt (fun s : ℝ => arctan (Θ₀ / √(m * c)) - √(m * c) / m * s)
      (-(√(m * c) / m)) s := by
    simpa using ((hasDerivAt_id s).const_mul (√(m * c) / m)).const_sub (arctan (Θ₀ / √(m * c)))
  have h := ((hasDerivAt_tan_of_mem_Ioo hx).comp s hin).const_mul (√(m * c))
  refine h.congr_deriv ?_
  set x := arctan (Θ₀ / √(m * c)) - √(m * c) / m * s with hxdef
  have hsc : sin x ^ 2 + cos x ^ 2 = 1 := sin_sq_add_cos_sq x
  have ht : tan x = sin x / cos x := tan_eq_sin_div_cos x
  simp only [riccatiProfile, ← hxdef, ht]
  field_simp
  nlinarith [hsc, hr2]

/-- At the blow-up time the profile tends to `-∞`: the bound of `focusing_ricci_bound` is attained. -/
theorem riccatiProfile_tendsto {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (Θ₀ : ℝ) :
    Tendsto (riccatiProfile m c Θ₀) (𝓝[<] (riccatiTime m c Θ₀)) atBot := by
  have hmc : 0 < m * c := mul_pos hm hc
  have hr0 : 0 < √(m * c) := Real.sqrt_pos.2 hmc
  have hq : 0 < √(m * c) / m := div_pos hr0 hm
  set a := arctan (Θ₀ / √(m * c)) with ha
  set T := riccatiTime m c Θ₀ with hT
  have hlin : Tendsto (fun s : ℝ => a - √(m * c) / m * s) (𝓝[<] T) (𝓝[>] (-(π / 2))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc' : Continuous fun s : ℝ => a - √(m * c) / m * s := by fun_prop
      have := (hc'.tendsto T).mono_left (nhdsWithin_le_nhds (s := Iio T))
      have hv : a - √(m * c) / m * T = -(π / 2) := by
        simp only [hT, riccatiTime]
        have : √(m * c) / m * (m / √(m * c) * (π / 2 + a)) = π / 2 + a := by field_simp
        rw [this]; ring
      rwa [hv] at this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s < T := hs
      have hv : √(m * c) / m * T = π / 2 + a := by
        simp only [hT, riccatiTime, ha]; field_simp
      show -(π / 2) < a - √(m * c) / m * s
      nlinarith [mul_lt_mul_of_pos_left hs' hq]
  exact (tendsto_tan_neg_pi_div_two.comp hlin).const_mul_atBot hr0

/-- **Sharpness of `focusing_ricci_bound`.** For every `Θ₀` there is a solution of the Riccati equality
`Θ' = -Θ²/m - c` on `[0, L*)` with `Θ(0) = Θ₀`, where `L*` is exactly the bound of `focusing_ricci_bound`,
and it diverges to `-∞` as `s ↑ L*`. -/
theorem focusing_ricci_sharp {m c : ℝ} (hm : 0 < m) (hc : 0 < c) (Θ₀ : ℝ) :
    ∃ Θ : ℝ → ℝ, Θ 0 = Θ₀ ∧
      (∀ s ∈ Ico 0 (riccatiTime m c Θ₀), HasDerivAt Θ (-(Θ s) ^ 2 / m - c) s) ∧
      Tendsto Θ (𝓝[<] (riccatiTime m c Θ₀)) atBot :=
  ⟨riccatiProfile m c Θ₀, riccatiProfile_zero hm hc Θ₀, fun _ hs => riccatiProfile_hasDerivAt hm hc Θ₀ hs,
    riccatiProfile_tendsto hm hc Θ₀⟩

end Lightlike
