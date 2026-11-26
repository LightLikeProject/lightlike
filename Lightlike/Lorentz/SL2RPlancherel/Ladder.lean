module

public import Mathlib

/-!
# The ladder operators of the radial `K`-type equations of `SL(2,ℝ)`

On functions of the hyperbolic distance `ξ > 0` of the `K`-type `(l, r)`, `Ψ(k_ϕ a_ξ k_ϑ) = e^{i(lϕ + rϑ)} F(ξ)`, the left
raising and lowering operators of the Lie algebra act by

`ladUp l r F = F' - (l coth ξ + r / sinh ξ) F`  (type `(l, r) ↦ (l+1, r)`),
`ladDown l r F = -F' - (l coth ξ + r / sinh ξ) F`  (type `(l, r) ↦ (l-1, r)`),

(Kitaev, arXiv:1711.08169, eq. (46)). With the Haar measure `sinh ξ dξ` they are adjoint to each other,
`⟨ladUp l r F, G⟩ = ⟨F, ladDown (l+1) r G⟩`, and the composite `ladDown (l+1) r ∘ ladUp l r` is the radial Casimir
operator `-F'' - coth ξ F' + (l² + r² + 2 l r cosh ξ)/sinh² ξ · F` shifted by `l (l + 1)`.
-/

@[expose] public section

open Set MeasureTheory Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The coefficient `l coth ξ + r / sinh ξ` of the ladder operators. -/
def ladCoeff (l r : ℝ) (ξ : ℝ) : ℝ := l * (Real.cosh ξ / Real.sinh ξ) + r / Real.sinh ξ

/-- **The raising operator** `F ↦ F' - (l coth ξ + r/sinh ξ) F`, type `(l, r) ↦ (l + 1, r)`. -/
def ladUp (l r : ℝ) (F : ℝ → ℂ) (ξ : ℝ) : ℂ := deriv F ξ - (ladCoeff l r ξ : ℂ) * F ξ

/-- **The lowering operator** `F ↦ -F' - (l coth ξ + r/sinh ξ) F`, type `(l, r) ↦ (l - 1, r)`. -/
def ladDown (l r : ℝ) (F : ℝ → ℂ) (ξ : ℝ) : ℂ := -deriv F ξ - (ladCoeff l r ξ : ℂ) * F ξ

/-- The coefficient `ladCoeff` is differentiable on `ξ > 0`. -/
lemma hasDerivAt_ladCoeff (l r : ℝ) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (ladCoeff l r) (-l / Real.sinh ξ ^ 2 - r * Real.cosh ξ / Real.sinh ξ ^ 2) ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have h1 := (Real.hasDerivAt_sinh ξ)
  have h2 := (Real.hasDerivAt_cosh ξ)
  have h3 := ((h2.div h1 hs).const_mul l).add ((hasDerivAt_const ξ r).div h1 hs)
  have hf : ladCoeff l r = (fun y => l * (Real.cosh / Real.sinh) y) + (fun _ => r) / Real.sinh := by
    funext y; simp [ladCoeff, mul_div_assoc]
  rw [hf]
  refine HasDerivAt.congr_deriv h3 ?_
  have hcs : Real.sinh ξ * Real.sinh ξ - Real.cosh ξ * Real.cosh ξ = -1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq ξ]
  rw [hcs]
  field_simp
  ring

/-- **`ladUp` and `ladDown` are adjoint** for the Haar measure `sinh ξ dξ` on `[a, b] ⊂ (0, ∞)`: if `F` vanishes at the endpoints,
`∫_a^b (ladUp l r F) conj(G) sinh = ∫_a^b F conj(ladDown (l+1) r G) sinh`. -/
theorem ladder_adjoint (l r : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {F G : ℝ → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hFa : F a = 0) (hFb : F b = 0) :
    ∫ ξ in a..b, ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) =
      ∫ ξ in a..b, F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ) := by
  have hFd : ∀ ξ, HasDerivAt F (deriv F ξ) ξ := fun ξ => (hF.differentiable one_ne_zero ξ).hasDerivAt
  have hGd : ∀ ξ, HasDerivAt G (deriv G ξ) ξ := fun ξ => (hG.differentiable one_ne_zero ξ).hasDerivAt
  set P : ℝ → ℂ := fun ξ => F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) with hP
  have hpt : ∀ ξ, 0 < ξ → HasDerivAt P
      (ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ) -
        F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) ξ := by
    intro ξ hξ
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have h1 := (hFd ξ).mul ((hGd ξ).star)
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
  have hpos : ∀ x ∈ uIcc a b, 0 < x := fun x hx => by
    rw [uIcc_of_le hab] at hx; exact lt_of_lt_of_le ha hx.1
  have hκ : ContinuousOn (ladCoeff l r) (uIcc a b) := fun x hx =>
    (hasDerivAt_ladCoeff l r (hpos x hx)).continuousAt.continuousWithinAt
  have hFc : Continuous F := hF.continuous
  have hGc : Continuous G := hG.continuous
  have hF'c : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hκc : ContinuousOn (fun ξ => (ladCoeff l r ξ : ℂ)) (uIcc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hκ
  have hκc1 : ContinuousOn (fun ξ => (ladCoeff (l + 1) r ξ : ℂ)) (uIcc a b) := by
    have : ContinuousOn (ladCoeff (l + 1) r) (uIcc a b) := fun x hx =>
      (hasDerivAt_ladCoeff (l + 1) r (hpos x hx)).continuousAt.continuousWithinAt
    exact Complex.continuous_ofReal.comp_continuousOn this
  have hsc : Continuous fun ξ : ℝ => (Real.sinh ξ : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sinh
  have hL : ContinuousOn (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladUp
    exact ((hF'c.continuousOn.sub (hκc.mul hFc.continuousOn)).mul
      (Complex.continuous_conj.comp hGc).continuousOn).mul hsc.continuousOn
  have hR : ContinuousOn (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) (uIcc a b) := by
    unfold ladDown
    exact (hFc.continuousOn.mul (Complex.continuous_conj.comp_continuousOn
      ((hG'c.continuousOn.neg).sub (hκc1.mul hGc.continuousOn)))).mul hsc.continuousOn
  have hLi : IntervalIntegrable (fun ξ => ladUp l r F ξ * (starRingEnd ℂ) (G ξ) * (Real.sinh ξ : ℂ)) volume a b :=
    hL.intervalIntegrable
  have hRi : IntervalIntegrable (fun ξ => F ξ * (starRingEnd ℂ) (ladDown (l + 1) r G ξ) * (Real.sinh ξ : ℂ)) volume a b :=
    hR.intervalIntegrable
  have hder : ∀ x ∈ uIcc a b, HasDerivAt P
      (ladUp l r F x * (starRingEnd ℂ) (G x) * (Real.sinh x : ℂ) -
        F x * (starRingEnd ℂ) (ladDown (l + 1) r G x) * (Real.sinh x : ℂ)) x :=
    fun x hx => hpt x (hpos x hx)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hLi.sub hRi)
  have hP0 : P b - P a = 0 := by simp [hP, hFa, hFb]
  rw [hP0, intervalIntegral.integral_sub hLi hRi, sub_eq_zero] at key
  exact key

/-- The radial Casimir operator of the `K`-type `(l, r)`:
`-F'' - coth ξ F' + (l² + r² + 2 l r cosh ξ)/sinh² ξ · F`. -/
def radialCasimir (l r : ℝ) (F : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  -deriv (deriv F) ξ - ((Real.cosh ξ / Real.sinh ξ : ℝ) : ℂ) * deriv F ξ +
    (((l ^ 2 + r ^ 2 + 2 * l * r * Real.cosh ξ) / Real.sinh ξ ^ 2 : ℝ) : ℂ) * F ξ

/-- A `C²` function has a `C¹` derivative. -/
lemma contDiff_deriv_of_two {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (deriv F) := by
  have h : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) F := by simpa using hF
  exact ((contDiff_succ_iff_deriv (n := 1)).1 h).2.2

/-- The derivative of `ladUp F` at `ξ > 0`. -/
lemma hasDerivAt_ladUp (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (ladUp l r F)
      (deriv (deriv F) ξ - ((-l / Real.sinh ξ ^ 2 - r * Real.cosh ξ / Real.sinh ξ ^ 2 : ℝ) : ℂ) * F ξ -
        (ladCoeff l r ξ : ℂ) * deriv F ξ) ξ := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have h1 : HasDerivAt (deriv F) (deriv (deriv F) ξ) ξ :=
    ((contDiff_deriv_of_two hF).differentiable one_ne_zero ξ).hasDerivAt
  have h2 : HasDerivAt F (deriv F ξ) ξ := (hF1.differentiable one_ne_zero ξ).hasDerivAt
  have h3 := (hasDerivAt_ladCoeff l r hξ).ofReal_comp
  have h4 := h1.sub (h3.mul h2)
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

/-- **The Casimir factorisation of the raising step**:
`ladDown (l+1) r (ladUp l r F) = radialCasimir l r F + l (l + 1) F`. -/
theorem ladDown_ladUp (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (l + 1) r (ladUp l r F) ξ = radialCasimir l r F ξ + ((l * (l + 1) : ℝ) : ℂ) * F ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
  unfold ladDown radialCasimir
  rw [(hasDerivAt_ladUp l r hF hξ).deriv]
  simp only [ladUp, ladCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  linear_combination (F ξ * ((l : ℂ) ^ 2 + l)) * hrel

/-- The derivative of `ladDown F` at `ξ > 0`. -/
lemma hasDerivAt_ladDown (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt (ladDown l r F)
      (-deriv (deriv F) ξ - ((-l / Real.sinh ξ ^ 2 - r * Real.cosh ξ / Real.sinh ξ ^ 2 : ℝ) : ℂ) * F ξ -
        (ladCoeff l r ξ : ℂ) * deriv F ξ) ξ := by
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have h1 : HasDerivAt (deriv F) (deriv (deriv F) ξ) ξ :=
    ((contDiff_deriv_of_two hF).differentiable one_ne_zero ξ).hasDerivAt
  have h2 : HasDerivAt F (deriv F ξ) ξ := (hF1.differentiable one_ne_zero ξ).hasDerivAt
  have h3 := (hasDerivAt_ladCoeff l r hξ).ofReal_comp
  have h4 := h1.neg.sub (h3.mul h2)
  refine HasDerivAt.congr_deriv h4 ?_
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

/-- **The Casimir factorisation of the lowering step**:
`ladUp (l-1) r (ladDown l r F) = radialCasimir l r F + l (l - 1) F`. -/
theorem ladUp_ladDown (l r : ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (l - 1) r (ladDown l r F) ξ = radialCasimir l r F ξ + ((l * (l - 1) : ℝ) : ℂ) * F ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
  unfold ladUp radialCasimir
  rw [(hasDerivAt_ladDown l r hF hξ).deriv]
  simp only [ladDown, ladCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  linear_combination (F ξ * ((l : ℂ) ^ 2 - l)) * hrel

end Lightlike.Lorentz.SL2RPlancherel
