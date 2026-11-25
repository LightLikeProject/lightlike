import Lightlike.Lorentz.SL2RPlancherel.Ladder

/-!
# The raising ladder commutes with the radial Casimir

For the radial `K`-type equations of `SL(2,ℝ)` the raising operator `ladUp l r` (type `(l, r) ↦ (l + 1, r)`) intertwines
the radial Casimir operators exactly: `radialCasimir (l + 1) r (ladUp l r F) = ladUp l r (radialCasimir l r F)` on `ξ > 0`.
This is what makes the Plancherel weight factor `(l + 1/2)² + ρ²` of the recursion on `l` independent of `r`.
It follows from the two factorisations `ladDown_ladUp` and `ladUp_ladDown` of `Ladder.lean`.
-/

open Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The derivative of `-l/sinh² - r cosh/sinh²` (the derivative of `ladCoeff`). -/
lemma hasDerivAt_ladCoeff' (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun y : ℝ => -l / Real.sinh y ^ 2 - r * Real.cosh y / Real.sinh y ^ 2)
      (-r / Real.sinh ξ + 2 * Real.cosh ξ * (l + r * Real.cosh ξ) / Real.sinh ξ ^ 3) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have h1 := Real.hasDerivAt_sinh ξ
  have h2 := Real.hasDerivAt_cosh ξ
  have hp : HasDerivAt (fun y : ℝ => Real.sinh y ^ 2) (2 * Real.sinh ξ * Real.cosh ξ) ξ := by
    exact ((h1.mul h1).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [pow_two])
  have h3 := ((hasDerivAt_const ξ (-l)).div hp (pow_ne_zero 2 hs)).sub
    ((h2.const_mul r).div hp (pow_ne_zero 2 hs))
  refine HasDerivAt.congr_deriv h3 ?_
  have hcs : Real.cosh ξ ^ 2 = 1 + Real.sinh ξ ^ 2 := by nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
  field_simp
  nlinarith [hcs]

/-- The derivative of the Casimir coefficient `(l² + r² + 2 l r cosh)/sinh²`. -/
lemma hasDerivAt_casCoeff (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun y : ℝ => (l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh y) / Real.sinh y ^ 2)
      ((2 * l * r * Real.sinh ξ * Real.sinh ξ ^ 2 -
        (l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh ξ) * (2 * Real.sinh ξ * Real.cosh ξ)) /
        (Real.sinh ξ ^ 2) ^ 2) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have h1 := Real.hasDerivAt_sinh ξ
  have h2 := Real.hasDerivAt_cosh ξ
  have hp : HasDerivAt (fun y : ℝ => Real.sinh y ^ 2) (2 * Real.sinh ξ * Real.cosh ξ) ξ :=
    ((h1.mul h1).congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp [pow_two])
  have hn : HasDerivAt (fun y : ℝ => l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh y) (2 * l * r * Real.sinh ξ) ξ := by
    simpa using (h2.const_mul (2 * l * r)).const_add (l ^ 2 + r ^ 2)
  exact hn.div hp (pow_ne_zero 2 hs)

/-- The derivative of `coth`. -/
lemma hasDerivAt_coth {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (fun y : ℝ => Real.cosh y / Real.sinh y)
      ((Real.sinh ξ * Real.sinh ξ - Real.cosh ξ * Real.cosh ξ) / Real.sinh ξ ^ 2) ξ :=
  (Real.hasDerivAt_cosh ξ).div (Real.hasDerivAt_sinh ξ) (Real.sinh_pos_iff.2 hξ).ne'

/-- **The raising ladder intertwines the radial Casimir** on `ξ > 0`, by direct differentiation. -/
theorem radialCasimir_ladUp (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ ∞ F) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir (l + 1) r (ladUp l r F) ξ = ladUp l r (radialCasimir l r F) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have h1 : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.1 hF).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv F)) := (contDiff_infty_iff_deriv.1 h1).2
  have d0 : ∀ y, HasDerivAt F (deriv F y) y := fun y => ((hF.differentiable (by simp)) y).hasDerivAt
  have d1 : ∀ y, HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    fun y => ((h1.differentiable (by simp)) y).hasDerivAt
  have d2 : ∀ y, HasDerivAt (deriv (deriv F)) (deriv (deriv (deriv F)) y) y :=
    fun y => ((h2.differentiable (by simp)) y).hasDerivAt
  -- derivative of `ladUp l r F` near `ξ`
  have hc := (hasDerivAt_ladCoeff l r hξ).ofReal_comp
  have hc1 := (hasDerivAt_ladCoeff' l r hξ).ofReal_comp
  have hG1 := (((d2 ξ).sub (hc1.mul (d0 ξ))).sub (hc.mul (d1 ξ)))
  have hg : ∀ y, 0 < y → deriv (ladUp l r F) y =
      deriv (deriv F) y - ((-l / Real.sinh y ^ 2 - r * Real.cosh y / Real.sinh y ^ 2 : ℝ) : ℂ) * F y -
        (ladCoeff l r y : ℂ) * deriv F y := fun y hy => (hasDerivAt_ladUp l r hF2 hy).deriv
  have hgg := hG1.congr_of_eventuallyEq (f₁ := deriv (ladUp l r F)) (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => hg y hy))
  have hcoth := (hasDerivAt_coth hξ).ofReal_comp
  have hq := (hasDerivAt_casCoeff l r hξ).ofReal_comp
  have hCas := (((d2 ξ).neg.sub (hcoth.mul (d1 ξ))).add (hq.mul (d0 ξ))).congr_of_eventuallyEq
    (f₁ := radialCasimir l r F) (Filter.Eventually.of_forall fun y => by
      simp [radialCasimir])
  have hu := (hasDerivAt_ladUp l r hF2 hξ)
  have hR : ladUp l r (radialCasimir l r F) ξ =
      deriv (radialCasimir l r F) ξ - (ladCoeff l r ξ : ℂ) * radialCasimir l r F ξ := rfl
  rw [hR, hCas.deriv]
  unfold radialCasimir
  rw [hgg.deriv, hu.deriv]
  simp only [ladUp, ladCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
  field_simp
  linear_combination (F ξ * (2 * (l : ℂ) * r + r) - ((Real.sinh ξ : ℝ) : ℂ) * deriv F ξ) * hrel

end Lightlike.Lorentz.SL2RPlancherel
