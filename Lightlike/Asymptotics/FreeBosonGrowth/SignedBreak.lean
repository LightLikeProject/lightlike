import Mathlib

/-!
# A signed density breaks Karamata's theorem (trust check of SP3)

Karamata's Tauberian theorem (`Lightlike.Tauberian.karamata`, `Lightlike.Karamata.karamata_tauberian`)
needs a **positive** measure. This file shows that positivity cannot be dropped, by an explicit signed
density on `[0, ∞)`:

`f(x) = 1 + x cos x`, which is negative for some `x` (`signedDensity_pi_neg`).

* Its Laplace transform is `1/β + (β² - 1)/(1 + β²)²` (`signedLaplace_eq`), so
  `β · L(β) → 1`, the hypothesis of Karamata's theorem with `α = 1`, `ℓ = 1`
  (`tendsto_mul_signedLaplace`).
* Its counting function is `F(X) = X + X sin X + cos X - 1` (`signedCount_eq`), and `F(X) / X` does not
  tend to `1 / Γ(2) = 1`, the value Karamata's conclusion would give (`not_tendsto_signedCount`).

No catalogue entry: this is a check, not a theorem a paper states.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Asymptotics.FreeBosonGrowth

/-- The signed density `f(x) = 1 + x cos x` on `[0, ∞)`. -/
def signedDensity (x : ℝ) : ℝ := 1 + x * Real.cos x

/-- The Laplace transform `∫_0^∞ e^{-βx} f(x) dx` of a signed density. -/
def signedLaplace (f : ℝ → ℝ) (β : ℝ) : ℝ := ∫ x in Ioi 0, Real.exp (-β * x) * f x

/-- The counting function `∫_0^X f` of a signed density. -/
def signedCount (f : ℝ → ℝ) (X : ℝ) : ℝ := ∫ x in (0 : ℝ)..X, f x

/-- The density is negative somewhere: it is not a positive measure. -/
lemma signedDensity_pi_neg : signedDensity π < 0 := by
  unfold signedDensity
  rw [Real.cos_pi]
  linarith [Real.pi_gt_three]

/-- An antiderivative of `e^{-βx} x cos x`. -/
def antiderivCos (β x : ℝ) : ℝ :=
  -(Real.exp (-β * x) *
    (Real.cos x * (x * β / (β ^ 2 + 1) + (β ^ 2 - 1) / (β ^ 2 + 1) ^ 2) -
      Real.sin x * (x / (β ^ 2 + 1) + 2 * β / (β ^ 2 + 1) ^ 2)))

lemma hasDerivAt_antiderivCos (β x : ℝ) :
    HasDerivAt (antiderivCos β) (Real.exp (-β * x) * (x * Real.cos x)) x := by
  have hm : (β ^ 2 + 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-β * y)) (Real.exp (-β * x) * (-β)) x := by
    simpa using ((hasDerivAt_id x).const_mul (-β)).exp
  have hA : HasDerivAt (fun y : ℝ => y * β / (β ^ 2 + 1) + (β ^ 2 - 1) / (β ^ 2 + 1) ^ 2)
      (β / (β ^ 2 + 1)) x := by
    have := (((hasDerivAt_id x).mul_const β).div_const (β ^ 2 + 1)).add_const
      ((β ^ 2 - 1) / (β ^ 2 + 1) ^ 2)
    simpa using this
  have hB : HasDerivAt (fun y : ℝ => y / (β ^ 2 + 1) + 2 * β / (β ^ 2 + 1) ^ 2)
      (1 / (β ^ 2 + 1)) x := by
    have := ((hasDerivAt_id x).div_const (β ^ 2 + 1)).add_const (2 * β / (β ^ 2 + 1) ^ 2)
    simpa using this
  have hP := ((Real.hasDerivAt_cos x).mul hA).sub ((Real.hasDerivAt_sin x).mul hB)
  have hG := (h1.mul hP).neg
  unfold antiderivCos
  convert hG using 1
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

lemma tendsto_antiderivCos {β : ℝ} (hβ : 0 < β) : Tendsto (antiderivCos β) atTop (𝓝 0) := by
  set m : ℝ := β ^ 2 + 1 with hm
  have hm0 : 0 < m := by positivity
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 β hβ
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 β hβ
  simp only [Real.rpow_one, Real.rpow_zero, one_mul] at h1 h0
  set K : ℝ := |(β ^ 2 - 1) / m ^ 2| + |2 * β / m ^ 2| with hK
  have hbound : ∀ᶠ y : ℝ in atTop, ‖antiderivCos β y‖ ≤
      ((β + 1) / m) * (y * Real.exp (-β * y)) + K * Real.exp (-β * y) := by
    filter_upwards [eventually_ge_atTop 0] with y hy
    unfold antiderivCos
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc := Real.abs_cos_le_one y
    have hs := Real.abs_sin_le_one y
    have hE := Real.exp_pos (-β * y)
    have hT : |Real.cos y * (y * β / m + (β ^ 2 - 1) / m ^ 2) -
        Real.sin y * (y / m + 2 * β / m ^ 2)| ≤ (β + 1) / m * y + K := by
      refine (abs_sub _ _).trans ?_
      have e1 : |Real.cos y * (y * β / m + (β ^ 2 - 1) / m ^ 2)| ≤ y * β / m + |(β ^ 2 - 1) / m ^ 2| := by
        rw [abs_mul]
        have : |y * β / m + (β ^ 2 - 1) / m ^ 2| ≤ y * β / m + |(β ^ 2 - 1) / m ^ 2| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (by positivity)]
        calc _ ≤ 1 * |y * β / m + (β ^ 2 - 1) / m ^ 2| :=
              mul_le_mul_of_nonneg_right hc (abs_nonneg _)
          _ ≤ _ := by linarith
      have e2 : |Real.sin y * (y / m + 2 * β / m ^ 2)| ≤ y / m + |2 * β / m ^ 2| := by
        rw [abs_mul]
        have : |y / m + 2 * β / m ^ 2| ≤ y / m + |2 * β / m ^ 2| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_of_nonneg (by positivity)]
        calc _ ≤ 1 * |y / m + 2 * β / m ^ 2| :=
              mul_le_mul_of_nonneg_right hs (abs_nonneg _)
          _ ≤ _ := by linarith
      have e3 : y * β / m + y / m = (β + 1) / m * y := by ring
      linarith
    calc Real.exp (-β * y) * |_| ≤ Real.exp (-β * y) * ((β + 1) / m * y + K) :=
          mul_le_mul_of_nonneg_left hT hE.le
      _ = _ := by ring
  have hlim : Tendsto (fun y : ℝ => ((β + 1) / m) * (y * Real.exp (-β * y)) + K * Real.exp (-β * y))
      atTop (𝓝 0) := by
    have := (h1.const_mul ((β + 1) / m)).add (h0.const_mul K)
    simpa using this
  exact squeeze_zero_norm' hbound hlim

lemma integrableOn_cos_density {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun x : ℝ => Real.exp (-β * x) * (x * Real.cos x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := β) (by norm_num)
    one_pos hβ
  simp only [Real.rpow_one] at h
  refine h.mono'
    (by fun_prop : Continuous fun x : ℝ => Real.exp (-β * x) * (x * Real.cos x)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hx0]
  calc Real.exp (-β * x) * (x * |Real.cos x|) ≤ Real.exp (-β * x) * (x * 1) := by
        gcongr
        exact Real.abs_cos_le_one x
    _ = x * Real.exp (-β * x) := by ring

lemma integral_cos_density {β : ℝ} (hβ : 0 < β) :
    ∫ x in Ioi 0, Real.exp (-β * x) * (x * Real.cos x) = (β ^ 2 - 1) / (1 + β ^ 2) ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (f := antiderivCos β)
    (f' := fun x => Real.exp (-β * x) * (x * Real.cos x))
    (fun x _ => hasDerivAt_antiderivCos β x) (integrableOn_cos_density hβ)
    (tendsto_antiderivCos hβ)
  rw [h]
  unfold antiderivCos
  have hm : (β ^ 2 + 1) ≠ 0 := by positivity
  simp only [mul_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, zero_mul, zero_div, zero_add,
    one_mul, sub_zero]
  field_simp
  ring

/-- **Laplace transform of the signed density**: `L(β) = 1/β + (β² - 1)/(1 + β²)²`. -/
lemma signedLaplace_eq {β : ℝ} (hβ : 0 < β) :
    signedLaplace signedDensity β = 1 / β + (β ^ 2 - 1) / (1 + β ^ 2) ^ 2 := by
  unfold signedLaplace signedDensity
  have hi1 : IntegrableOn (fun x : ℝ => Real.exp (-β * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hi2 := integrableOn_cos_density hβ
  have : ∀ x : ℝ, Real.exp (-β * x) * (1 + x * Real.cos x) =
      Real.exp (-β * x) + Real.exp (-β * x) * (x * Real.cos x) := fun x => by ring
  simp_rw [this]
  rw [integral_add hi1 hi2, integral_cos_density hβ, integral_exp_mul_Ioi (by linarith : -β < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  rw [neg_div_neg_eq]

/-- **The hypothesis of Karamata's theorem holds** for the signed density with `α = 1`, `ℓ = 1`:
`β L(β) → 1` as `β → 0⁺`. -/
lemma tendsto_mul_signedLaplace :
    Tendsto (fun β : ℝ => β * signedLaplace signedDensity β) (𝓝[>] 0) (𝓝 1) := by
  have hc : Tendsto (fun β : ℝ => 1 + β * ((β ^ 2 - 1) / (1 + β ^ 2) ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun β : ℝ => 1 + β * ((β ^ 2 - 1) / (1 + β ^ 2) ^ 2) := by
      refine Continuous.add continuous_const (continuous_id.mul (Continuous.div (by fun_prop)
        (by fun_prop) fun x => by positivity))
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : 0 < β := hβ
  rw [signedLaplace_eq hβ']
  field_simp

/-- **Counting function of the signed density**: `F(X) = X + X sin X + cos X - 1`. -/
lemma signedCount_eq (X : ℝ) :
    signedCount signedDensity X = X + (X * Real.sin X + Real.cos X - 1) := by
  unfold signedCount signedDensity
  have hd : ∀ x ∈ uIcc (0 : ℝ) X, HasDerivAt (fun y : ℝ => y + (y * Real.sin y + Real.cos y))
      (1 + x * Real.cos x) x := by
    intro x _
    have := (hasDerivAt_id x).add (((hasDerivAt_id x).mul (Real.hasDerivAt_sin x)).add
      (Real.hasDerivAt_cos x))
    refine this.congr_deriv ?_
    simp only [id_eq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [zero_mul, Real.sin_zero, Real.cos_zero, zero_add]
  ring

/-- **Karamata's conclusion fails** for the signed density: `F(X) / X` does not tend to
`1 / Γ(1 + 1) = 1`. -/
theorem not_tendsto_signedCount :
    ¬ Tendsto (fun X : ℝ => signedCount signedDensity X / X ^ (1 : ℝ)) atTop
      (𝓝 (1 / Real.Gamma (1 + 1))) := by
  intro h
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.Gamma_two, div_one] at h
  have hk : Tendsto (fun k : ℕ => π / 2 + 2 * π * (k : ℝ)) atTop atTop := by
    refine tendsto_atTop_add_const_left _ _ ?_
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h2 := (h.comp hk).eventually (gt_mem_nhds (show (1 : ℝ) < 3 / 2 by norm_num))
  obtain ⟨k, hk1, hk2⟩ := ((hk.eventually_ge_atTop 4).and h2).exists
  simp only [Function.comp_apply] at hk2
  set X : ℝ := π / 2 + 2 * π * (k : ℝ) with hX
  have hX0 : 0 < X := by linarith
  have hsin : Real.sin X = 1 := by
    rw [hX, show π / 2 + 2 * π * (k : ℝ) = π / 2 + (k : ℝ) * (2 * π) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]
  have hcos : Real.cos X = 0 := by
    rw [hX, show π / 2 + 2 * π * (k : ℝ) = π / 2 + (k : ℝ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two]
  rw [signedCount_eq, hsin, hcos, Real.rpow_one, div_lt_iff₀ hX0] at hk2
  linarith

end Lightlike.Asymptotics.FreeBosonGrowth

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.antiderivCos := _root_.Lightlike.Asymptotics.FreeBosonGrowth.antiderivCos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.hasDerivAt_antiderivCos := _root_.Lightlike.Asymptotics.FreeBosonGrowth.hasDerivAt_antiderivCos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.integrableOn_cos_density := _root_.Lightlike.Asymptotics.FreeBosonGrowth.integrableOn_cos_density
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.integral_cos_density := _root_.Lightlike.Asymptotics.FreeBosonGrowth.integral_cos_density
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.not_tendsto_signedCount := _root_.Lightlike.Asymptotics.FreeBosonGrowth.not_tendsto_signedCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedCount := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedCount
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedCount_eq := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedCount_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedDensity := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedDensity
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedDensity_pi_neg := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedDensity_pi_neg
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedLaplace := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedLaplace
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.signedLaplace_eq := _root_.Lightlike.Asymptotics.FreeBosonGrowth.signedLaplace_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.tendsto_antiderivCos := _root_.Lightlike.Asymptotics.FreeBosonGrowth.tendsto_antiderivCos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.SP3Row.tendsto_mul_signedLaplace := _root_.Lightlike.Asymptotics.FreeBosonGrowth.tendsto_mul_signedLaplace
