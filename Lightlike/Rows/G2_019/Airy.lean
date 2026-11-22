import Lightlike.Rows.G2_019.AiryODE
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Airy functions `Ai`, `Bi` and their Wronskian (row G2-019)

`airyAi`, `airyBi` are defined as the power-series solutions of `y'' = x y` with the standard
initial data
`Ai(0) = 3^{-2/3}/Γ(2/3)`, `Ai'(0) = -3^{-1/3}/Γ(1/3)`, `Bi(0) = √3 Ai(0)`, `Bi'(0) = -√3 Ai'(0)`.
We prove they solve the Airy equation and that the Wronskian is `W(Ai, Bi) = 1/π`
(`airy_wronskian`), via a generic Wronskian-constancy lemma and the reflection formula
`Γ(1/3)Γ(2/3) = 2π/√3`.
-/

noncomputable section

namespace Lightlike.Airy

/-- Wronskian `y₁ y₂' - y₁' y₂` of two solutions of `y'' = x y` is constant. -/
theorem wronskian_const {y1 y1' y2 y2' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt y1 (y1' x) x) (h1' : ∀ x, HasDerivAt y1' (x * y1 x) x)
    (h2 : ∀ x, HasDerivAt y2 (y2' x) x) (h2' : ∀ x, HasDerivAt y2' (x * y2 x) x) (x : ℝ) :
    y1 x * y2' x - y1' x * y2 x = y1 0 * y2' 0 - y1' 0 * y2 0 := by
  have hd : ∀ t, HasDerivAt (fun t => y1 t * y2' t - y1' t * y2 t) 0 t := by
    intro t
    have := ((h1 t).mul (h2' t)).sub ((h1' t).mul (h2 t))
    convert this using 1
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) x 0

/-- `Ai(0)`. -/
def airyAi0 : ℝ := (3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3)
/-- `Ai'(0)`. -/
def airyAiDeriv0 : ℝ := -((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3))

/-- The Airy function `Ai`, as the power-series solution of `y'' = x y`. -/
def airyAi : ℝ → ℝ := evalSeries (airyCoeff airyAi0 airyAiDeriv0)
/-- The derivative `Ai'`. -/
def airyAiDeriv : ℝ → ℝ := evalSeries (dcoef (airyCoeff airyAi0 airyAiDeriv0))
/-- The Airy function `Bi`. -/
def airyBi : ℝ → ℝ := evalSeries (airyCoeff (√3 * airyAi0) (-(√3 * airyAiDeriv0)))
/-- The derivative `Bi'`. -/
def airyBiDeriv : ℝ → ℝ :=
  evalSeries (dcoef (airyCoeff (√3 * airyAi0) (-(√3 * airyAiDeriv0))))

theorem airyAi_hasDerivAt (x : ℝ) : HasDerivAt airyAi (airyAiDeriv x) x :=
  airySeries_hasDerivAt _ _ x
theorem airyAiDeriv_hasDerivAt (x : ℝ) : HasDerivAt airyAiDeriv (x * airyAi x) x :=
  airySeries_hasDerivAt' _ _ x
theorem airyBi_hasDerivAt (x : ℝ) : HasDerivAt airyBi (airyBiDeriv x) x :=
  airySeries_hasDerivAt _ _ x
theorem airyBiDeriv_hasDerivAt (x : ℝ) : HasDerivAt airyBiDeriv (x * airyBi x) x :=
  airySeries_hasDerivAt' _ _ x

theorem airyAi_zero : airyAi 0 = airyAi0 := airySeries_zero _ _
theorem airyAiDeriv_zero : airyAiDeriv 0 = airyAiDeriv0 := airySeries_deriv_zero _ _
theorem airyBi_zero : airyBi 0 = √3 * airyAi0 := airySeries_zero _ _
theorem airyBiDeriv_zero : airyBiDeriv 0 = -(√3 * airyAiDeriv0) := airySeries_deriv_zero _ _

/-- `Γ(1/3) Γ(2/3) = 2π/√3`. -/
theorem gamma_third_mul_two_thirds : Real.Gamma (1 / 3) * Real.Gamma (2 / 3) = Real.pi / (√3 / 2) := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num,
    show Real.pi * (1 / 3) = Real.pi / 3 by ring, Real.sin_pi_div_three] at h
  exact h

/-- `Ai(0) Ai'(0) = -√3/(6π)`. -/
theorem airyAi0_mul_deriv0 : airyAi0 * airyAiDeriv0 = -(√3 / (6 * Real.pi)) := by
  have hp : (3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 3 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hg := gamma_third_mul_two_thirds
  have hg1 : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hg2 : 0 < Real.Gamma (2 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  unfold airyAi0 airyAiDeriv0
  have : (3 : ℝ) ^ (-(2 / 3 : ℝ)) / Real.Gamma (2 / 3) * -((3 : ℝ) ^ (-(1 / 3 : ℝ)) / Real.Gamma (1 / 3))
      = -(((3 : ℝ) ^ (-(2 / 3 : ℝ)) * (3 : ℝ) ^ (-(1 / 3 : ℝ))) /
        (Real.Gamma (1 / 3) * Real.Gamma (2 / 3))) := by
    field_simp
  rw [this, hp, hg]
  have hpi : 0 < Real.pi := Real.pi_pos
  field_simp
  nlinarith [h33]

/-- The Wronskian of `Ai` and `Bi` is `1/π`. -/
theorem airy_wronskian (x : ℝ) : airyAi x * airyBiDeriv x - airyAiDeriv x * airyBi x = 1 / Real.pi := by
  rw [wronskian_const airyAi_hasDerivAt airyAiDeriv_hasDerivAt airyBi_hasDerivAt
    airyBiDeriv_hasDerivAt x, airyAi_zero, airyAiDeriv_zero, airyBi_zero, airyBiDeriv_zero]
  have h := airyAi0_mul_deriv0
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have : airyAi0 * (-(√3 * airyAiDeriv0)) - airyAiDeriv0 * (√3 * airyAi0)
      = -2 * √3 * (airyAi0 * airyAiDeriv0) := by ring
  rw [this, h]
  field_simp
  nlinarith [h33]

end Lightlike.Airy
