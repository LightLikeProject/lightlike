import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.Ladder

/-!
# Symmetry of the radial Casimir

For `F, G` twice continuously differentiable on `(0, ∞)` and `[a, b] ⊂ (0, ∞)`,
`∫_a^b (L F conj G - F conj (L G)) sinh = B(b) - B(a)` with the boundary form
`B = sinh (F conj G' - F' conj G)` (`integral_radialCasimir_symm`): the potential of
`L = radialCasimir l r` is real and `-F'' - coth F' = -(sinh F')' / sinh`.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The boundary form `sinh ξ (F conj G' - F' conj G)`. -/
def casBdry (F G : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  (Real.sinh ξ : ℂ) * (F ξ * (starRingEnd ℂ) (deriv G ξ) - deriv F ξ * (starRingEnd ℂ) (G ξ))

lemma hasDerivAt_of_contDiffOn_two {F : ℝ → ℂ} (hF : ContDiffOn ℝ 2 F (Ioi 0)) {x : ℝ}
    (hx : 0 < x) : HasDerivAt F (deriv F x) x ∧ HasDerivAt (deriv F) (deriv (deriv F) x) x := by
  have hU : Ioi (0 : ℝ) ∈ nhds x := Ioi_mem_nhds hx
  have hdF : ContDiffOn ℝ 1 (deriv F) (Ioi 0) := hF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ⟨((hF.contDiffAt hU).differentiableAt (by norm_num)).hasDerivAt,
    ((hdF.contDiffAt hU).differentiableAt (by norm_num)).hasDerivAt⟩

/-- The boundary form differentiates to the symmetric Casimir integrand. -/
theorem hasDerivAt_casBdry (l r : ℝ) {F G : ℝ → ℂ} (hF : ContDiffOn ℝ 2 F (Ioi 0))
    (hG : ContDiffOn ℝ 2 G (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (casBdry F G) ((radialCasimir l r F x * (starRingEnd ℂ) (G x) -
      F x * (starRingEnd ℂ) (radialCasimir l r G x)) * (Real.sinh x : ℂ)) x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
  have hs' : ((Real.sinh x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  obtain ⟨hF1, hF2⟩ := hasDerivAt_of_contDiffOn_two hF hx
  obtain ⟨hG1, hG2⟩ := hasDerivAt_of_contDiffOn_two hG hx
  have hsh : HasDerivAt (fun t => ((Real.sinh t : ℝ) : ℂ)) ((Real.cosh x : ℝ) : ℂ) x :=
    (Real.hasDerivAt_sinh x).ofReal_comp
  have h := hsh.mul ((hF1.mul hG2.star).sub (hF2.mul hG1.star))
  have e : casBdry F G = fun t => ((Real.sinh t : ℝ) : ℂ) *
      (F t * star (deriv G t) - deriv F t * star (G t)) := by
    funext t
    simp [casBdry]
  rw [e]
  convert h using 1
  simp only [radialCasimir, Complex.star_def, map_add, map_sub, map_mul, map_neg, map_div₀,
    Complex.conj_ofReal, Complex.ofReal_div, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

lemma continuousOn_radialCasimir (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiffOn ℝ 2 F (Ioi 0)) :
    ContinuousOn (radialCasimir l r F) (Ioi 0) := by
  have hdF : ContDiffOn ℝ 1 (deriv F) (Ioi 0) := hF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hddF : ContDiffOn ℝ 0 (deriv (deriv F)) (Ioi 0) :=
    hdF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hs : ∀ x ∈ Ioi (0 : ℝ), Real.sinh x ≠ 0 := fun x hx => (Real.sinh_pos_iff.2 hx).ne'
  have hcoth : ContinuousOn (fun x : ℝ => ((Real.cosh x / Real.sinh x : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_cosh.continuousOn.div Real.continuous_sinh.continuousOn hs)
  have hV : ContinuousOn (fun x : ℝ =>
      (((l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh x) / Real.sinh x ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.add (continuous_const.mul Real.continuous_cosh)).continuousOn.div
        (Real.continuous_sinh.pow 2).continuousOn fun x hx => pow_ne_zero 2 (hs x hx))
  unfold radialCasimir
  exact ((hddF.continuousOn.neg).sub (hcoth.mul hdF.continuousOn)).add (hV.mul hF.continuousOn)

/-- **Symmetry of the radial Casimir on an interval** `[a, b] ⊂ (0, ∞)`. -/
theorem integral_radialCasimir_symm (l r : ℝ) {F G : ℝ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hF : ContDiffOn ℝ 2 F (Ioi 0)) (hG : ContDiffOn ℝ 2 G (Ioi 0)) :
    ∫ x in a..b, (radialCasimir l r F x * (starRingEnd ℂ) (G x) -
        F x * (starRingEnd ℂ) (radialCasimir l r G x)) * (Real.sinh x : ℂ) =
      casBdry F G b - casBdry F G a := by
  have hsub : uIcc a b ⊆ Ioi 0 := by
    rw [uIcc_of_le hab]; exact fun x hx => lt_of_lt_of_le ha hx.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_casBdry l r hF hG (hsub hx)) ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine (((continuousOn_radialCasimir l r hF).mul
    (Complex.continuous_conj.comp_continuousOn hG.continuousOn)).sub
    (hF.continuousOn.mul (Complex.continuous_conj.comp_continuousOn
      (continuousOn_radialCasimir l r hG)))).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh).continuousOn |>.mono hsub

end Lightlike.Lorentz.SL2RPlancherel
