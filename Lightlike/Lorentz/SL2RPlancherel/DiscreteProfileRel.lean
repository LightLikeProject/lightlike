module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileLadder

/-!
# The ladder relations for the coefficients of the profile polynomials

Taking the `j`-th Taylor coefficient of the pointwise identities of `DiscreteProfileDeriv`:
for `|t| < 1` and `P_{jl} = profPoly n l j`,
`t (1 - t²) P_{j,k+1}' + ((k+1) (1 + t²) - (1 - t²) j) P_{j,k+1} = 2 (k+1) t P_{jk}` (`profPoly_lower`),
`t (1 - t²) P_{j0}' - (1 - t²) j P_{j0} = 0` (`profPoly_lower_zero`) and
`t (1 - t²) P_{jl}' + ((1 - t²) j - l (1 + t²) - 2 n t²) P_{jl} = -2 (n + l) t P_{j,l+1}` (`profPoly_raise`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma differentiableOn_genFunW (n l : ℕ) {t : ℝ} (ht : |t| < 1) :
    DifferentiableOn ℂ (genFunW n l t) (ball (0 : ℂ) 1) := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  have hV := pow_ne_zero (n + l) (one_add_mul_ne_zero ht hw)
  have hV' := pow_ne_zero (n + l + 1) (one_add_mul_ne_zero ht hw)
  unfold genFunW
  refine DifferentiableAt.sub ?_ ?_
  · exact (DifferentiableAt.mul (by fun_prop) (DifferentiableAt.inv (by fun_prop) hV))
  · exact DifferentiableAt.mul (by fun_prop) (DifferentiableAt.inv (by fun_prop) hV')

lemma discCoeff_wW (n l j : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    discCoeff (fun w => w * genFunW n l t w) j = (j : ℂ) * profPoly n l j t := by
  have h := discCoeff_mul_deriv (differentiableOn_genFun n l ht) j
  unfold profPoly
  rw [← h]
  refine discCoeff_congr (fun w hw => ?_) j
  rw [(hasDerivAt_genFun_w n l hn t w (one_add_mul_ne_zero ht hw)).deriv]

lemma discCoeff_comb (n l j : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) (a b c : ℂ) :
    discCoeff (fun w => a * genFunT n l t w + b * genFun n l t w - c * (w * genFunW n l t w)) j =
      a * discCoeff (genFunT n l t) j + b * profPoly n l j t - c * ((j : ℂ) * profPoly n l j t) := by
  have hT := differentiableOn_genFunT n l ht
  have hG := differentiableOn_genFun n l ht
  have hW : DifferentiableOn ℂ (fun w => w * genFunW n l t w) (ball (0 : ℂ) 1) :=
    differentiableOn_id.mul (differentiableOn_genFunW n l ht)
  have hTa : DifferentiableOn ℂ (fun w => a * genFunT n l t w) (ball (0 : ℂ) 1) := hT.const_mul a
  have hGb : DifferentiableOn ℂ (fun w => b * genFun n l t w) (ball (0 : ℂ) 1) := hG.const_mul b
  have hsum : DifferentiableOn ℂ (fun w => a * genFunT n l t w + b * genFun n l t w) (ball (0 : ℂ) 1) :=
    hTa.add hGb
  have hWc : DifferentiableOn ℂ (fun w => c * (w * genFunW n l t w)) (ball (0 : ℂ) 1) := hW.const_mul c
  rw [discCoeff_sub hsum hWc, discCoeff_add hTa hGb, discCoeff_const_mul hT, discCoeff_const_mul hG,
    discCoeff_const_mul hW, discCoeff_wW n l j hn ht]
  rfl

/-- **The lowering relation** for the profile polynomials. -/
theorem profPoly_lower (n k j : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * deriv (profPoly n (k + 1) j) t +
      (((k + 1 : ℕ) : ℂ) * (1 + (t : ℂ) ^ 2) - (1 - (t : ℂ) ^ 2) * j) * profPoly n (k + 1) j t =
      2 * ((k + 1 : ℕ) : ℂ) * t * profPoly n k j t := by
  have hd := (hasDerivAt_profPoly n (k + 1) j hn ht).deriv
  have hcomb := discCoeff_comb n (k + 1) j hn ht ((t : ℂ) * (1 - (t : ℂ) ^ 2))
    (((k + 1 : ℕ) : ℂ) * (1 + (t : ℂ) ^ 2)) (1 - (t : ℂ) ^ 2)
  have hfun : discCoeff (fun w => ((t : ℂ) * (1 - (t : ℂ) ^ 2)) * genFunT n (k + 1) t w +
      (((k + 1 : ℕ) : ℂ) * (1 + (t : ℂ) ^ 2)) * genFun n (k + 1) t w -
      (1 - (t : ℂ) ^ 2) * (w * genFunW n (k + 1) t w)) j =
      discCoeff (fun w => (2 * ((k + 1 : ℕ) : ℂ) * t) * genFun n k t w) j := by
    refine discCoeff_congr (fun w hw => ?_) j
    have := genFun_lower_eq n k t w (one_add_mul_ne_zero ht hw)
    linear_combination this
  rw [hfun, discCoeff_const_mul (differentiableOn_genFun n k ht)] at hcomb
  rw [hd]
  unfold profPoly at hcomb ⊢
  linear_combination (-1 : ℂ) * hcomb

/-- The lowering relation for `l = 0` (no `P_{j,-1}`). -/
theorem profPoly_lower_zero (n j : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * deriv (profPoly n 0 j) t - (1 - (t : ℂ) ^ 2) * j * profPoly n 0 j t = 0 := by
  have hd := (hasDerivAt_profPoly n 0 j hn ht).deriv
  have hcomb := discCoeff_comb n 0 j hn ht ((t : ℂ) * (1 - (t : ℂ) ^ 2)) 0 (1 - (t : ℂ) ^ 2)
  have hfun : discCoeff (fun w => ((t : ℂ) * (1 - (t : ℂ) ^ 2)) * genFunT n 0 t w +
      (0 : ℂ) * genFun n 0 t w - (1 - (t : ℂ) ^ 2) * (w * genFunW n 0 t w)) j = discCoeff (fun _ => (0 : ℂ)) j := by
    refine discCoeff_congr (fun w hw => ?_) j
    have := genFun_lower_zero n t w (one_add_mul_ne_zero ht hw)
    linear_combination this
  have h0 : discCoeff (fun _ => (0 : ℂ)) j = 0 := by
    have := discCoeff_monomial (0 : ℂ) j
    simpa using this
  rw [hfun, h0] at hcomb
  rw [hd]
  unfold profPoly at hcomb ⊢
  linear_combination (-1 : ℂ) * hcomb

/-- **The raising relation** for the profile polynomials. -/
theorem profPoly_raise (n l j : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : |t| < 1) :
    (t : ℂ) * (1 - (t : ℂ) ^ 2) * deriv (profPoly n l j) t +
      ((1 - (t : ℂ) ^ 2) * j - ((l : ℂ) * (1 + (t : ℂ) ^ 2) + 2 * (n : ℂ) * (t : ℂ) ^ 2)) * profPoly n l j t =
      -2 * ((n + l : ℕ) : ℂ) * t * profPoly n (l + 1) j t := by
  have hd := (hasDerivAt_profPoly n l j hn ht).deriv
  have hcomb := discCoeff_comb n l j hn ht ((t : ℂ) * (1 - (t : ℂ) ^ 2))
    (-((l : ℂ) * (1 + (t : ℂ) ^ 2) + 2 * (n : ℂ) * (t : ℂ) ^ 2)) (-(1 - (t : ℂ) ^ 2))
  have hfun : discCoeff (fun w => ((t : ℂ) * (1 - (t : ℂ) ^ 2)) * genFunT n l t w +
      (-((l : ℂ) * (1 + (t : ℂ) ^ 2) + 2 * (n : ℂ) * (t : ℂ) ^ 2)) * genFun n l t w -
      (-(1 - (t : ℂ) ^ 2)) * (w * genFunW n l t w)) j =
      discCoeff (fun w => (-2 * ((n + l : ℕ) : ℂ) * t) * genFun n (l + 1) t w) j := by
    refine discCoeff_congr (fun w hw => ?_) j
    have := genFun_raise_eq n l t w (one_add_mul_ne_zero ht hw)
    linear_combination this
  rw [hfun, discCoeff_const_mul (differentiableOn_genFun n (l + 1) ht)] at hcomb
  rw [hd]
  unfold profPoly at hcomb ⊢
  linear_combination (-1 : ℂ) * hcomb

end Lightlike.Lorentz.SL2RPlancherel
