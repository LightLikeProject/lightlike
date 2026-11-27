import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalKType

/-!
# The radial matrix coefficients of the even principal series

`Φ^ν_{m,n}(ξ) = ⟪e_m, π(a(ξ)) e_n⟫ = ∫ conj(e_m(x)) e^{-wξ} e_n(e^ξ x) dx` with `w = (iν - 1)/2`
(`mcoefP_eq_integral`).  The generator of the diagonal subgroup acts on the `K`-types by
`y e_n'(y) - w e_n(y) = ((w - n)/2) e_{n+1}(y) + ((w + n)/2) e_{n-1}(y)` (`deriv_kVecP_rel`).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (identification of the block transforms with
matrix coefficients), milestone HA3.
-/

open MeasureTheory Set Real Complex Lightlike.Lorentz.SL2R

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The exponent `w = (iν - 1)/2` of the `K`-type vectors. -/
def wP (ν : ℝ) : ℂ := (I * ν - 1) / 2

/-- **The matrix coefficients as an integral**:
`Φ^ν_{m,n}(ξ) = ∫ conj(e_m(x)) e^{-wξ} e_n(e^ξ x) dx`. -/
theorem mcoefP_eq_integral (ν : ℝ) (m n : ℤ) (ξ : ℝ) :
    mcoefP ν m n ξ = ∫ x, (starRingEnd ℂ) (kVecP ν m x) *
      (Complex.exp (-(wP ν * ξ)) * kVecP ν n (Real.exp ξ * x)) := by
  rw [mcoefP, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 : (kVecL2 ν m : ℝ → ℂ) =ᵐ[volume] kVecP ν m := MemLp.coeFn_toLp (memLp_kVecP ν m)
  have h2 := coeFn_principalSeries 0 ν (aR ξ) (kVecL2 ν n)
  have h3 := ae_eq_comp_mob (aR ξ) (MemLp.coeFn_toLp (memLp_kVecP ν n))
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [Function.comp_apply] at e3
  rw [e1, e2, RCLike.inner_apply']
  congr 1
  have := act_aR ν ξ (kVecP ν n) x
  rw [act] at this
  rw [show (kVecL2 ν n : ℝ → ℂ) (mob (aR ξ) x) = kVecP ν n (mob (aR ξ) x) from e3, this, wP]
  congr 1
  · congr 1; ring

/-- The phase `u(x) = (x - i)/(x + i)` and its derivative `u' = 2i/(x + i)²`. -/
lemma hasDerivAt_phaseP (x : ℝ) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) - I) / ((y : ℂ) + I)) (2 * I / ((x : ℂ) + I) ^ 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) - I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.sub_const I
  have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) + I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const I
  have h := h1.div h2 (ofReal_add_I_ne_zero x)
  convert h using 1
  have hne := ofReal_add_I_ne_zero x
  field_simp
  ring

/-- The derivative of the `K`-type vector `e_n`. -/
lemma hasDerivAt_kVecP (ν : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (kVecP ν n)
      (wP ν * (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) * ((2 * x : ℝ) : ℂ) *
          (((x : ℂ) - I) / ((x : ℂ) + I)) ^ n +
        (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) *
          ((n : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ (n - 1) * (2 * I / ((x : ℂ) + I) ^ 2))) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hslit : (((1 + x ^ 2 : ℝ)) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hpos
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := wP ν) hslit).hasDerivAt
  have hi : HasDerivAt (fun y : ℝ => (((1 + y ^ 2 : ℝ)) : ℂ)) (((2 * x : ℝ)) : ℂ) x := by
    have := ((hasDerivAt_id x).pow 2).const_add 1
    simpa using this.ofReal_comp
  have h1 := hc.comp x hi
  have hu := hasDerivAt_phaseP x
  have hune : ((x : ℂ) - I) / ((x : ℂ) + I) ≠ 0 :=
    div_ne_zero (ofReal_sub_I_ne_zero x) (ofReal_add_I_ne_zero x)
  have h2 := (hasDerivAt_zpow n _ (Or.inl hune)).comp x hu
  have h := h1.mul h2
  have hfun : kVecP ν n = ((fun z : ℂ => z ^ wP ν) ∘ fun y : ℝ => (((1 + y ^ 2 : ℝ)) : ℂ)) *
      ((fun z : ℂ => z ^ n) ∘ fun y : ℝ => ((y : ℂ) - I) / ((y : ℂ) + I)) := by
    funext y; simp [kVecP, wP]
  rw [hfun]
  convert h using 1
  simp only [Function.comp_apply]

/-- **The generator of the diagonal subgroup on the `K`-types**:
`x e_n'(x) - w e_n(x) = ((w - n)/2) e_{n+1}(x) + ((w + n)/2) e_{n-1}(x)`. -/
theorem deriv_kVecP_rel (ν : ℝ) (n : ℤ) (x : ℝ) :
    (x : ℂ) * (wP ν * (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) * ((2 * x : ℝ) : ℂ) *
          (((x : ℂ) - I) / ((x : ℂ) + I)) ^ n +
        (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) *
          ((n : ℂ) * (((x : ℂ) - I) / ((x : ℂ) + I)) ^ (n - 1) * (2 * I / ((x : ℂ) + I) ^ 2))) -
      wP ν * kVecP ν n x =
      (wP ν - n) / 2 * kVecP ν (n + 1) x + (wP ν + n) / 2 * kVecP ν (n - 1) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hP0 : (((1 + x ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hp := ofReal_add_I_ne_zero x
  have hm := ofReal_sub_I_ne_zero x
  have hune : ((x : ℂ) - I) / ((x : ℂ) + I) ≠ 0 := div_ne_zero hm hp
  set P := (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν) with hP
  set u := ((x : ℂ) - I) / ((x : ℂ) + I) with hu
  have hPm : (((1 + x ^ 2 : ℝ)) : ℂ) ^ (wP ν - 1) = P / (((1 + x ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.cpow_sub _ _ hP0, Complex.cpow_one]
  have h1 : u ^ (n + 1) = u ^ n * u := zpow_add_one₀ hune n
  have h2 : u ^ (n - 1) = u ^ n / u := zpow_sub_one₀ hune n
  have hx2 : (((1 + x ^ 2 : ℝ)) : ℂ) = ((x : ℂ) - I) * ((x : ℂ) + I) := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  simp only [kVecP, show ((I * (ν : ℂ) - 1) / 2) = wP ν from rfl]
  rw [← hP, ← hu, hPm, h1, h2]
  rw [hx2] at hP0 ⊢
  rw [hu]
  field_simp
  push_cast
  ring

end Lightlike.Lorentz.SL2RPlancherel
