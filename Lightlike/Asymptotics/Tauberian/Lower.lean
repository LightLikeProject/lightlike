import Lightlike.Asymptotics.Tauberian.Window

/-!
# The lower bound for the counting function

If `L γ` lies between `exp ((a - δ) / γ)` and `exp ((a + δ) / γ)` for `γ ≤ β (1 + η / 2)`, then the
counting function at `X = (1 + η) a / β²` is at least `exp (((2 - η) a - δ) / β) / 2`: the three
windows `[0, Xl]`, `(Xl, X]`, `(X, ∞)` with `Xl = (1 - η) a / β²` carry `L β`, and the outer two are
small by the window estimates with `β'' = β (1 + η/2)` and `β' = β / (1 + η/2)`, so the middle one,
at most `exp (-β Xl) F X`, carries at least half.
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Tauberian

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

/-- **Lower bound at the saddle.** -/
theorem counting_lower (hρ : ρ (Iio 0) = 0)
    (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
    {a η δ β : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ0 : 0 < δ) (hδ : δ ≤ a * η ^ 2 / 36)
    (hβ : 0 < β) (hq : Real.log 4 ≤ a * η ^ 2 / 12 / β)
    (hLb : ∀ γ : ℝ, 0 < γ → γ ≤ β * (1 + η / 2) →
      Real.exp ((a - δ) / γ) ≤ laplace ρ γ ∧ laplace ρ γ ≤ Real.exp ((a + δ) / γ)) :
    (1 / 2) * Real.exp (((2 - η) * a - δ) / β) ≤ counting ρ ((1 + η) * a / β ^ 2) := by
  set θ : ℝ := η / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  set Xl : ℝ := (1 - η) * a / β ^ 2 with hXl
  set Xh : ℝ := (1 + η) * a / β ^ 2 with hXh
  have hXl0 : 0 ≤ Xl := by
    have : 0 ≤ 1 - η := by linarith
    positivity
  have hXlh : Xl ≤ Xh := by
    rw [hXl, hXh]
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  set κ : ℝ := a * η ^ 2 / 12 with hκ
  -- the window decomposition
  have hsplit := laplace_eq_split hint hρ hβ hXl0 hXlh
  -- lower window
  have hlow : ∫ x in Icc (0 : ℝ) Xl, Real.exp (-β * x) ∂ρ ≤
      Real.exp ((β * (1 + θ) - β) * Xl + (a + δ) / (β * (1 + θ))) := by
    have h1 := setIntegral_Icc_le hint hβ (show β ≤ β * (1 + θ) by nlinarith) hXl0
    have h2 := (hLb (β * (1 + θ)) (by positivity) (by rw [hθ])).2
    calc _ ≤ Real.exp ((β * (1 + θ) - β) * Xl) * laplace ρ (β * (1 + θ)) := h1
      _ ≤ Real.exp ((β * (1 + θ) - β) * Xl) * Real.exp ((a + δ) / (β * (1 + θ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  -- upper window
  have htail : ∫ x in Ioi Xh, Real.exp (-β * x) ∂ρ ≤
      Real.exp (-(β - β / (1 + θ)) * Xh + (a + δ) / (β / (1 + θ))) := by
    have hβ' : 0 < β / (1 + θ) := by positivity
    have h1 := setIntegral_Ioi_le hint (β := β) (β' := β / (1 + θ)) (Y := Xh) hβ'
      (by rw [div_le_iff₀ (by positivity)]; nlinarith)
    have h2 := (hLb (β / (1 + θ)) hβ' (by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_pos hβ hθ0])).2
    calc _ ≤ Real.exp (-(β - β / (1 + θ)) * Xh) * laplace ρ (β / (1 + θ)) := h1
      _ ≤ Real.exp (-(β - β / (1 + θ)) * Xh) * Real.exp ((a + δ) / (β / (1 + θ))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  -- middle window
  have hmid := setIntegral_Ioc_le hint hβ hXl0 hXlh
  -- the arithmetic
  have h1θ : 0 < 1 + θ := by positivity
  have P1 : θ * (1 - η) * a + (a + δ) / (1 + θ) ≤ a - δ - κ := by
    have : (a + δ) / (1 + θ) ≤ a - δ - κ - θ * (1 - η) * a := by
      rw [div_le_iff₀ h1θ, hθ, hκ]
      nlinarith [mul_pos ha (pow_pos hη0 2), mul_pos ha (pow_pos hη0 3),
        mul_le_mul_of_nonneg_right hδ hη0.le, mul_pos hδ0 hη0]
    linarith
  have P2 : -(θ * (1 + η) * a) / (1 + θ) + (a + δ) * (1 + θ) ≤ a - δ - κ := by
    have : (a + δ) * (1 + θ) - (a - δ - κ) ≤ θ * (1 + η) * a / (1 + θ) := by
      rw [le_div_iff₀ h1θ, hθ, hκ]
      nlinarith [mul_pos ha (pow_pos hη0 2), mul_pos ha (pow_pos hη0 3),
        mul_le_mul_of_nonneg_right hδ hη0.le, mul_pos hδ0 hη0,
        mul_le_mul_of_nonneg_right hδ (pow_pos hη0 2).le]
    rw [neg_div]
    linarith
  have e1 : (β * (1 + θ) - β) * Xl + (a + δ) / (β * (1 + θ)) ≤ (a - δ) / β - κ / β := by
    have : (β * (1 + θ) - β) * Xl + (a + δ) / (β * (1 + θ)) =
        (θ * (1 - η) * a + (a + δ) / (1 + θ)) / β := by
      rw [hXl]; field_simp; ring
    rw [this, ← sub_div]
    exact div_le_div_of_nonneg_right P1 hβ.le
  have e2 : -(β - β / (1 + θ)) * Xh + (a + δ) / (β / (1 + θ)) ≤ (a - δ) / β - κ / β := by
    have : -(β - β / (1 + θ)) * Xh + (a + δ) / (β / (1 + θ)) =
        (-(θ * (1 + η) * a) / (1 + θ) + (a + δ) * (1 + θ)) / β := by
      rw [hXh]; field_simp; ring
    rw [this, ← sub_div]
    exact div_le_div_of_nonneg_right P2 hβ.le
  -- `exp (-κ / β) ≤ 1/4`
  have hexp4 : Real.exp (-(κ / β)) ≤ 1 / 4 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 4), one_div, inv_inv]
    calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (κ / β) := Real.exp_le_exp.2 hq
  have hL0 := (hLb β hβ (by nlinarith [mul_pos hβ hθ0])).1
  set E := Real.exp ((a - δ) / β) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hlow' : ∫ x in Icc (0 : ℝ) Xl, Real.exp (-β * x) ∂ρ ≤ E / 4 := by
    refine hlow.trans ((Real.exp_le_exp.2 e1).trans ?_)
    rw [sub_eq_add_neg, ← neg_div, Real.exp_add]
    calc E * Real.exp (-κ / β) = E * Real.exp (-(κ / β)) := by rw [neg_div]
      _ ≤ E * (1 / 4) := mul_le_mul_of_nonneg_left hexp4 hE0.le
      _ = E / 4 := by ring
  have htail' : ∫ x in Ioi Xh, Real.exp (-β * x) ∂ρ ≤ E / 4 := by
    refine htail.trans ((Real.exp_le_exp.2 e2).trans ?_)
    rw [sub_eq_add_neg, ← neg_div, Real.exp_add]
    calc E * Real.exp (-κ / β) = E * Real.exp (-(κ / β)) := by rw [neg_div]
      _ ≤ E * (1 / 4) := mul_le_mul_of_nonneg_left hexp4 hE0.le
      _ = E / 4 := by ring
  -- the middle window carries at least `E / 2`
  have hmid2 : E / 2 ≤ ∫ x in Ioc Xl Xh, Real.exp (-β * x) ∂ρ := by
    have := hsplit
    linarith
  have hM : ∫ x in Ioc Xl Xh, Real.exp (-β * x) ∂ρ ≤ Real.exp (-β * Xl) * counting ρ Xh := hmid
  have hβXl : β * Xl = (1 - η) * a / β := by rw [hXl]; field_simp
  have key : E / 2 ≤ Real.exp (-((1 - η) * a / β)) * counting ρ Xh := by
    have : -β * Xl = -((1 - η) * a / β) := by rw [neg_mul, hβXl]
    rw [this] at hM
    linarith
  -- solve for `counting ρ Xh`
  have hExp : Real.exp (((2 - η) * a - δ) / β) = E * Real.exp ((1 - η) * a / β) := by
    rw [hE, ← Real.exp_add]; congr 1; field_simp; ring
  rw [hExp]
  have hpos : 0 < Real.exp ((1 - η) * a / β) := Real.exp_pos _
  have : Real.exp (-((1 - η) * a / β)) * Real.exp ((1 - η) * a / β) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 / 2) * (E * Real.exp ((1 - η) * a / β)) = (E / 2) * Real.exp ((1 - η) * a / β) := by ring
    _ ≤ (Real.exp (-((1 - η) * a / β)) * counting ρ Xh) * Real.exp ((1 - η) * a / β) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ = counting ρ Xh := by rw [mul_assoc, mul_comm (counting ρ Xh), ← mul_assoc, this, one_mul]

end Lightlike.Tauberian
