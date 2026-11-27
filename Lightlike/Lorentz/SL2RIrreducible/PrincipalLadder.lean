module

public import Lightlike.Lorentz.SL2RIrreducible.PrincipalWeights

/-!
# The ladder relation of the principal-series weight vectors and the matrix coefficient between
neighbouring weights

With `s = (iν - 1 - ε)/2` and `w = (iν - 1)/2 = s + ε/2`, the weight vectors `e_k` of
`PrincipalWeights.lean` satisfy `x e_k'(x) - w e_k(x) = ((s - k)/2) e_{k+1}(x) + ((s + k + ε)/2) e_{k-1}(x)`
(`ladder_weightVec`), the explicit form of Kitaev's Eq. (15), arXiv:1711.08169, for the generator of
the diagonal subgroup. Hence the matrix coefficient `t ↦ ⟪e_{k+1}, π(exp(tH)) e_k⟫` has derivative
`(s - k) ‖e_{k+1}‖²` at `t = 0` (`hasDerivAt_pairing`), which vanishes only at the reducible point:
`s - k = 0` iff `ν = 0` and `2k + ε = -1`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Metric
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The algebra of the ladder relation, in `P = x - i`, `Q = x + i`. -/
lemma ladder_alg (s ε' k' x P Q e : ℂ) (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : x = (P + Q) / 2)
    (hPQ : 1 + x ^ 2 = P * Q) :
    x * (e * (s * (2 * x / (1 + x ^ 2)) + (k' + ε') / P - k' / Q)) - (s + ε' / 2) * e =
      ((s - k') / 2) * (e * (P / Q)) + ((s + k' + ε') / 2) * (e * (Q / P)) := by
  rw [hPQ]
  subst hx
  field_simp
  ring

variable (ε : ℤ) (ν : ℝ) (k : ℤ)

lemma hasDerivAt_log_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2)) (2 * x / (1 + x ^ 2)) x := by
  have h := ((hasDerivAt_pow 2 x).const_add (1 : ℝ)).log (one_add_sq_pos x).ne'
  convert h using 1
  simp

lemma hasDerivAt_zpow_sub (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) - I) ^ m) ((m : ℂ) * ((x : ℂ) - I) ^ (m - 1)) x :=
  ((hasDerivAt_zpow m ((x : ℂ) - I) (Or.inl (ofReal_sub_I_ne_zero' x))).comp_sub_const (x : ℂ) I
    ).comp_ofReal

lemma hasDerivAt_zpow_add (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) + I) ^ m) ((m : ℂ) * ((x : ℂ) + I) ^ (m - 1)) x :=
  ((hasDerivAt_zpow m ((x : ℂ) + I) (Or.inl (ofReal_add_I_ne_zero' x))).comp_add_const (x : ℂ) I
    ).comp_ofReal

/-- **The derivative of the weight vector**: `e_k' = e_k [2 s x/(1 + x²) + (k+ε)/(x - i) - k/(x + i)]`. -/
theorem hasDerivAt_weightVec (x : ℝ) :
    HasDerivAt (weightVec ε ν k)
      (weightVec ε ν k x * (weightExp ε ν * ((2 * x / (1 + x ^ 2) : ℝ) : ℂ) +
        ((k + ε : ℤ) : ℂ) / ((x : ℂ) - I) - (k : ℂ) / ((x : ℂ) + I))) x := by
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (weightExp ε ν * ((Real.log (1 + y ^ 2) : ℝ) : ℂ)))
      (Complex.exp (weightExp ε ν * ((Real.log (1 + x ^ 2) : ℝ) : ℂ)) *
        (weightExp ε ν * ((2 * x / (1 + x ^ 2) : ℝ) : ℂ))) x :=
    ((hasDerivAt_log_one_add_sq x).ofReal_comp.const_mul (weightExp ε ν)).cexp
  have h3 := hasDerivAt_zpow_sub (k + ε) x
  have h4 := hasDerivAt_zpow_add (-k) x
  have h := (h2.mul h3).mul h4
  refine h.congr_deriv ?_
  have hP := ofReal_sub_I_ne_zero' x
  have hQ := ofReal_add_I_ne_zero' x
  simp only [Pi.mul_apply]
  unfold weightVec
  rw [zpow_sub_one₀ hP, zpow_sub_one₀ hQ]
  push_cast
  ring

/-- **The ladder relation**: `x e_k' - w e_k = ((s - k)/2) e_{k+1} + ((s + k + ε)/2) e_{k-1}`
with `w = (iν - 1)/2` (Kitaev, arXiv:1711.08169, Eq. (15)). -/
theorem ladder_weightVec (x : ℝ) :
    (x : ℂ) * deriv (weightVec ε ν k) x - ((I * ν - 1) / 2) * weightVec ε ν k x =
      ((weightExp ε ν - k) / 2) * weightVec ε ν (k + 1) x +
      ((weightExp ε ν + k + ε) / 2) * weightVec ε ν (k - 1) x := by
  rw [(hasDerivAt_weightVec ε ν k x).deriv, weightVec_succ, weightVec_pred]
  have hw : (I * ν - 1) / 2 = weightExp ε ν + (ε : ℂ) / 2 := by unfold weightExp; ring
  rw [hw]
  have hP := ofReal_sub_I_ne_zero' x
  have hQ := ofReal_add_I_ne_zero' x
  have hPQ : (1 : ℂ) + (x : ℂ) ^ 2 = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    linear_combination Complex.I_sq
  have hcast : ((2 * x / (1 + x ^ 2) : ℝ) : ℂ) = 2 * (x : ℂ) / (1 + (x : ℂ) ^ 2) := by
    push_cast; ring
  rw [hcast]
  have := ladder_alg (weightExp ε ν) (ε : ℂ) (k : ℂ) (x : ℂ) ((x : ℂ) - I) ((x : ℂ) + I)
    (weightVec ε ν k x) hP hQ (by ring) hPQ
  push_cast
  linear_combination this

end Lightlike.Lorentz.SL2R
