import Lightlike.Asymptotics.Tauberian.Psi
import Lightlike.Asymptotics.Tauberian.WindowSum

/-!
# Comparison of a measure with its smoothed version

`ρ(x) = 1_{x ≤ Δ} - ψ(Δ - x)`: pointwise bound in terms of `y = Δ - x` (`rho_bound`).
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- The error function `1_{x ≤ Δ} - ψ(Δ - x)`, as a function of `y = Δ - x`. -/
def rhoErr (b β y : ℝ) : ℝ := (if 0 ≤ y then 1 else 0) - psiS b β y

lemma psiS_le_exp {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    psiS b β y ≤ Real.exp (β * max y 0) := by
  have hN := kapN_pos hb
  unfold psiS
  have h1 : ∫ u in Iio y, Real.exp (β * u) * kap b u ≤ ∫ u in Iio y, Real.exp (β * max y 0) * kap b u :=
    setIntegral_mono_on (integrableOn_exp_kap hb hβ y) ((integrable_kap hb).integrableOn.const_mul _)
      measurableSet_Iio fun u hu => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (by have : u < y := hu; nlinarith [le_max_left y 0])) (kap_nonneg b u)
  rw [integral_const_mul] at h1
  have h2 : ∫ u in Iio y, kap b u ≤ kapN b := setIntegral_le_integral (integrable_kap hb)
    (Filter.Eventually.of_forall fun u => kap_nonneg b u)
  calc 1 / kapN b * ∫ u in Iio y, Real.exp (β * u) * kap b u
      ≤ 1 / kapN b * (Real.exp (β * max y 0) * ∫ u in Iio y, kap b u) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / kapN b * (Real.exp (β * max y 0) * kapN b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity)
    _ = Real.exp (β * max y 0) := by field_simp

/-- **A crude bound for the error**: `|ρ(y)| ≤ 1 + e^{β max(y,0)}`. -/
lemma rhoErr_abs_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    |rhoErr b β y| ≤ 1 + Real.exp (β * max y 0) := by
  have h0 := psiS_nonneg (β := β) hb y
  have h1 := psiS_le_exp hb hβ y
  have h2 : 1 ≤ Real.exp (β * max y 0) := Real.one_le_exp (mul_nonneg hβ (le_max_right _ _))
  unfold rhoErr
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- The constant of the far-field bound. -/
def farC (b : ℝ) : ℝ := (kapM2 b + 8 + 6) / kapN b

lemma kapM2_nonneg (b : ℝ) : 0 ≤ kapM2 b :=
  integral_nonneg fun u => mul_nonneg (sq_nonneg u) (kap_nonneg b u)

/-- **Far-field pointwise bound.** For `0 ≤ β ≤ 1`, `R ≥ 1` and `y ≥ R` or `y < -R`:
`|ρ(y)| ≤ C (β² + β/R² + 1/R³) e^{β y}`. -/
lemma rhoErr_far {b β R : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (hR : 1 ≤ R) {y : ℝ}
    (hy : R ≤ y ∨ y < -R) :
    |rhoErr b β y| ≤ farC b * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) * Real.exp (β * y) := by
  have hN := kapN_pos hb
  have hM := kapM2_nonneg b
  have hR0 : 0 < R := by linarith
  have hC : 0 ≤ farC b := by unfold farC; positivity
  rcases hy with hy | hy
  · have hy0 : 0 < y := by linarith
    have h := psi_sub_one_le hb hβ hy0
    have : rhoErr b β y = -(psiS b β y - 1) := by unfold rhoErr; rw [if_pos hy0.le]; ring
    rw [this, abs_neg]
    refine h.trans ?_
    have e1 : 1 ≤ Real.exp (β * y) := Real.one_le_exp (by positivity)
    have h2 : 8 / y ^ 2 ≤ 8 / R ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    have h3 : 16 / (3 * y ^ 3) ≤ 6 / R ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : R ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hR0.le hy 3
      nlinarith
    unfold farC
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hN.le
    have hp : 0 ≤ β * (8 / y ^ 2) := by positivity
    have hq : 0 ≤ β / R ^ 2 := by positivity
    have hr : 0 ≤ 1 / R ^ 3 := by positivity
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    calc β ^ 2 * Real.exp (β * y) * kapM2 b + β * (8 / y ^ 2) + 16 / (3 * y ^ 3)
        ≤ β ^ 2 * Real.exp (β * y) * kapM2 b + β * (8 / R ^ 2) * Real.exp (β * y)
            + 6 / R ^ 3 * Real.exp (β * y) := by
          have := mul_le_mul_of_nonneg_left h2 hβ
          have h4 : β * (8 / R ^ 2) ≤ β * (8 / R ^ 2) * Real.exp (β * y) :=
            le_mul_of_one_le_right (by positivity) e1
          have h5 : 6 / R ^ 3 ≤ 6 / R ^ 3 * Real.exp (β * y) :=
            le_mul_of_one_le_right (by positivity) e1
          nlinarith
      _ ≤ (kapM2 b + 8 + 6) * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) * Real.exp (β * y) := by
          have e2 : β ^ 2 * kapM2 b ≤ kapM2 b * β ^ 2 := le_of_eq (mul_comm _ _)
          have : β ^ 2 * kapM2 b + β * (8 / R ^ 2) + 6 / R ^ 3 ≤
              (kapM2 b + 8 + 6) * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) := by
            have h6 : β * (8 / R ^ 2) = 8 * (β / R ^ 2) := by ring
            have h7 : 6 / R ^ 3 = 6 * (1 / R ^ 3) := by ring
            rw [h6, h7]; nlinarith [mul_nonneg hM hq, mul_nonneg hM hr, mul_nonneg hq hr,
              mul_nonneg hM hβ2, mul_nonneg hβ2 hq, mul_nonneg hβ2 hr, mul_nonneg hq hq, mul_nonneg hr hr]
          nlinarith [Real.exp_pos (β * y)]
  · have hy0 : ¬ (0 ≤ y) := by linarith
    have h := psi_neg_le hb hβ (by linarith : y < 0)
    have : rhoErr b β y = -psiS b β y := by unfold rhoErr; rw [if_neg hy0]; ring
    rw [this, abs_neg, abs_of_nonneg (psiS_nonneg hb y)]
    refine h.trans ?_
    have h3 : 16 / (3 * (-y) ^ 3) ≤ 6 / R ^ 3 := by
      have hny : 0 < -y := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : R ^ 3 ≤ (-y) ^ 3 := pow_le_pow_left₀ hR0.le (by linarith) 3
      nlinarith [pow_pos hR0 3]
    unfold farC
    have hq : 0 ≤ β / R ^ 2 := by positivity
    have hβ2 : 0 ≤ β ^ 2 := sq_nonneg β
    have hr : 0 ≤ 1 / R ^ 3 := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hN]
    have : 6 / R ^ 3 ≤ (kapM2 b + 8 + 6) * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) := by
      have h7 : 6 / R ^ 3 = 6 * (1 / R ^ 3) := by ring
      rw [h7]; nlinarith [mul_nonneg hM hq, mul_nonneg hM hr, mul_nonneg hM hβ2]
    have e := Real.exp_pos (β * y)
    calc Real.exp (β * y) * (16 / (3 * (-y) ^ 3)) ≤ Real.exp (β * y) * (6 / R ^ 3) :=
          mul_le_mul_of_nonneg_left h3 e.le
      _ ≤ _ := by nlinarith

/-- **The outer region** `x ≤ Δ - R` or `x > Δ + R`: by Markov's inequality against `e^{-β x}`,
`∫_{outer} |ρ(Δ - x)| dμ ≤ C (β² + β/R² + 1/R³) e^{βΔ} ∫ e^{-β x} dμ`. -/
lemma outer_le (μ : Measure ℝ) {b β R Δ : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (hR : 1 ≤ R)
    (hint : Integrable (fun x : ℝ => Real.exp (-β * x)) μ) :
    ∫ x in {x : ℝ | x ≤ Δ - R ∨ Δ + R < x}, |rhoErr b β (Δ - x)| ∂μ ≤
      farC b * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) * Real.exp (β * Δ) * ∫ x, Real.exp (-β * x) ∂μ := by
  set S : Set ℝ := {x : ℝ | x ≤ Δ - R ∨ Δ + R < x}
  set K : ℝ := farC b * (β ^ 2 + β / R ^ 2 + 1 / R ^ 3) * Real.exp (β * Δ) with hK
  have hR0 : 0 < R := by linarith
  have hC : 0 ≤ farC b := by unfold farC; have := kapN_pos hb; have := kapM2_nonneg b; positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hSm : MeasurableSet S := by
    simp only [S, Set.setOf_or]
    exact measurableSet_Iic.union measurableSet_Ioi
  have hg : Integrable (fun x : ℝ => K * Real.exp (-β * x)) (μ.restrict S) :=
    (hint.const_mul K).restrict
  calc ∫ x in S, |rhoErr b β (Δ - x)| ∂μ ≤ ∫ x in S, K * Real.exp (-β * x) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hg ?_
        refine (ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall fun x hx => ?_)
        have hy : R ≤ Δ - x ∨ Δ - x < -R := by
          rcases hx with h | h
          · left; linarith
          · right; linarith
        have := rhoErr_far hb hβ hR hy
        refine this.trans (le_of_eq ?_)
        show _ = K * Real.exp (-β * x)
        have : Real.exp (β * (Δ - x)) = Real.exp (β * Δ) * Real.exp (-β * x) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [hK, this]; ring
    _ ≤ ∫ x, K * Real.exp (-β * x) ∂μ :=
        setIntegral_le_integral (hint.const_mul K)
          (Filter.Eventually.of_forall fun x => mul_nonneg hK0 (Real.exp_pos _).le)
    _ = K * ∫ x, Real.exp (-β * x) ∂μ := integral_const_mul _ _

/-- The per-window weight: crude for `|t| ≤ 1`, the far-field bound with `R = |t| - 1` otherwise. -/
def Aw (b β : ℝ) (t : ℤ) : ℝ :=
  if |t| ≤ 1 then (1 + Real.exp β) * Real.exp β
  else farC b * (β ^ 2 + β / (|(t : ℝ)| - 1) ^ 2 + 1 / (|(t : ℝ)| - 1) ^ 3)

/-- **Window-wise bound for the error**: for `t - 1 ≤ y < t`, `|ρ(y)| ≤ A_t e^{β t}`. -/
lemma rhoErr_window {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (t : ℤ) {y : ℝ}
    (hy1 : (t : ℝ) - 1 ≤ y) (hy2 : y < t) :
    |rhoErr b β y| ≤ Aw b β t * Real.exp (β * t) := by
  unfold Aw
  split_ifs with ht
  · have h := rhoErr_abs_le hb hβ y
    have ht' : -1 ≤ t ∧ t ≤ 1 := abs_le.1 ht
    have ht1 : (-1 : ℝ) ≤ t := by exact_mod_cast ht'.1
    have ht2 : (t : ℝ) ≤ 1 := by exact_mod_cast ht'.2
    have e1 : Real.exp (β * max y 0) ≤ Real.exp β :=
      Real.exp_le_exp.2 (by nlinarith [max_le (by linarith : y ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)])
    have e3 : (1 + Real.exp (β * max y 0)) ≤ (1 + Real.exp β) := by linarith
    have e4 : 1 + Real.exp β ≤ (1 + Real.exp β) * Real.exp β * Real.exp (β * t) := by
      have h1 : 1 ≤ Real.exp β * Real.exp (β * t) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      nlinarith [Real.exp_pos β]
    linarith
  · have ht2 : 2 ≤ |t| := by omega
    have ht2' : (2 : ℝ) ≤ |(t : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast ht2
    have hR : (1 : ℝ) ≤ |(t : ℝ)| - 1 := by linarith
    have hfar : |(t : ℝ)| - 1 ≤ y ∨ y < -(|(t : ℝ)| - 1) := by
      rcases le_total 0 (t : ℝ) with h | h
      · left; rw [abs_of_nonneg h]; exact hy1
      · right; rw [abs_of_nonpos h]; linarith
    have h := rhoErr_far hb hβ hR hfar
    refine h.trans ?_
    have hC : 0 ≤ farC b * (β ^ 2 + β / (|(t : ℝ)| - 1) ^ 2 + 1 / (|(t : ℝ)| - 1) ^ 3) := by
      have := kapN_pos hb; have := kapM2_nonneg b; unfold farC; positivity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC

end Lightlike.Tauberian
