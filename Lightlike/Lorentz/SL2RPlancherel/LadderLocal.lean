import Lightlike.Lorentz.SL2RPlancherel.LadderCasimir

/-!
# The ladder adjoint identity for functions smooth on `(0, ∞)`, with boundary terms

`ladder_adjoint` of `Ladder.lean` assumes global smoothness and vanishing at both ends. The ladder images of a radial
function are smooth only on `ξ > 0` and do not vanish at a small endpoint `a`, so here the identity is stated for
`ContDiffOn ℝ 1` on `(0, ∞)` and keeps the boundary term `P(b) - P(a)`, `P = F · conj G · sinh`.
-/

open Set MeasureTheory Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Adjointness of the ladders with boundary terms** on `[a, b] ⊂ (0, ∞)`. -/
theorem ladder_adjoint_boundary (l r : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContDiffOn ℝ 1 F (Ioi 0)) (hG : ContDiffOn ℝ 1 G (Ioi 0)) :
    ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      (F b * (starRingEnd ℂ) (G b) * (Real.sinh b : ℂ) - F a * (starRingEnd ℂ) (G a) * (Real.sinh a : ℂ)) +
      ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hFd : ∀ ξ, 0 < ξ → HasDerivAt F (deriv F ξ) ξ := fun ξ hξ =>
    ((hF.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hξ)).hasDerivAt
  have hGd : ∀ ξ, 0 < ξ → HasDerivAt G (deriv G ξ) ξ := fun ξ hξ =>
    ((hG.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hξ)).hasDerivAt
  set P : ℝ → ℂ := fun ξ => F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) with hP
  have hpt : ∀ ξ, 0 < ξ → HasDerivAt P
      (ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) -
        F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) ξ := by
    intro ξ hξ
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have h1 := (hFd ξ hξ).mul ((hGd ξ hξ).star)
    have h2 := h1.mul ((Real.hasDerivAt_sinh ξ).ofReal_comp)
    refine HasDerivAt.congr_deriv h2 ?_
    have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hcs : (starRingEnd ℂ) (Complex.sinh (ξ : ℂ)) = Complex.sinh ξ := by
      rw [← Complex.ofReal_sinh, Complex.conj_ofReal]
    have hcc : (starRingEnd ℂ) (Complex.cosh (ξ : ℂ)) = Complex.cosh ξ := by
      rw [← Complex.ofReal_cosh, Complex.conj_ofReal]
    have hs'' : Complex.sinh (ξ : ℂ) ≠ 0 := by rw [← Complex.ofReal_sinh]; exact_mod_cast hs
    simp [ladUp, ladDown, ladCoeff, Complex.conj_ofReal, hcs, hcc]
    field_simp
    ring
  have hFc : ContinuousOn F (uIcc a b) := (hF.continuousOn).mono fun x hx => hpos x hx
  have hGc : ContinuousOn G (uIcc a b) := (hG.continuousOn).mono fun x hx => hpos x hx
  have hF'c : ContinuousOn (deriv F) (uIcc a b) :=
    (hF.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono fun x hx => hpos x hx
  have hG'c : ContinuousOn (deriv G) (uIcc a b) :=
    (hG.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono fun x hx => hpos x hx
  have hκc : ContinuousOn (fun ξ => (ladCoeff l r ξ : ℂ)) (uIcc a b) := by
    have : ContinuousOn (ladCoeff l r) (uIcc a b) := fun x hx =>
      (hasDerivAt_ladCoeff l r (hpos x hx)).continuousAt.continuousWithinAt
    exact Complex.continuous_ofReal.comp_continuousOn this
  have hκc1 : ContinuousOn (fun ξ => (ladCoeff (l + 1) r ξ : ℂ)) (uIcc a b) := by
    have : ContinuousOn (ladCoeff (l + 1) r) (uIcc a b) := fun x hx =>
      (hasDerivAt_ladCoeff (l + 1) r (hpos x hx)).continuousAt.continuousWithinAt
    exact Complex.continuous_ofReal.comp_continuousOn this
  have hsc : Continuous fun ξ : ℝ => (Real.sinh ξ : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have hL : ContinuousOn (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladUp
    exact ((hF'c.sub (hκc.mul hFc)).mul
      (Complex.continuous_conj.comp_continuousOn hGc)).mul hsc.continuousOn
  have hR : ContinuousOn (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladDown
    exact (hFc.mul (Complex.continuous_conj.comp_continuousOn
      ((hG'c.neg).sub (hκc1.mul hGc)))).mul hsc.continuousOn
  have hLi : IntervalIntegrable (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ))
      volume a b := hL.intervalIntegrable
  have hRi : IntervalIntegrable (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ))
      volume a b := hR.intervalIntegrable
  have hder : ∀ x ∈ uIcc a b, HasDerivAt P
      (ladUp l r F x * (starRingEnd ℂ) (G x) * (Real.sinh x : ℂ) -
        F x * (starRingEnd ℂ) (ladDown (l + 1) r G x) * (Real.sinh x : ℂ)) x :=
    fun x hx => hpt x (hpos x hx)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hLi.sub hRi)
  rw [intervalIntegral.integral_sub hLi hRi] at key
  have : ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      P b - P a + ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
    linear_combination key
  exact this

/-- **The Casimir factorisation of the raising step** for `F` smooth on `(0, ∞)`:
`ladDown (l+1) r (ladUp l r F) = radialCasimir l r F + l (l + 1) F` on `ξ > 0`. -/
theorem ladDown_ladUp_local (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiffOn ℝ 2 F (Ioi 0)) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (l + 1) r (ladUp l r F) ξ = radialCasimir l r F ξ + ((l * (l + 1) : ℝ) : ℂ) * F ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
  have h1 : ContDiffOn ℝ 1 (deriv F) (Ioi 0) := hF.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have dF : DifferentiableAt ℝ F ξ :=
    (hF.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hξ)
  have dF1 : DifferentiableAt ℝ (deriv F) ξ :=
    (h1.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hξ)
  unfold ladDown radialCasimir
  rw [(hasDerivAt_ladUp_at l r hξ dF dF1).deriv]
  simp only [ladUp, ladCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  linear_combination (F ξ * ((l : ℂ) ^ 2 + l)) * hrel

end Lightlike.Lorentz.SL2RPlancherel
