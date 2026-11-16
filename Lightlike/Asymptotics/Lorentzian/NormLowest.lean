import Lightlike.Asymptotics.Lorentzian.LinkIntegral
import Lightlike.Asymptotics.Lorentzian.RadialBeta

/-!
# The norm of the lowest-level vector of the principal series

`‖tlin n 0 ρ e₀‖² = π/(n+1)`: the explicit constant of `link_integral`.
-/

open Matrix Complex MeasureTheory
open scoped ComplexConjugate InnerProductSpace
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam

namespace Lightlike.Asymptotics.Lorentzian

/-- **The modulus of the weight on the chart**: `‖wgt p q ρ z‖² = (1 + ‖z‖²)^{-2-(p+q)}`; the
imaginary part of the exponent drops out of the modulus. -/
theorem norm_sq_wgt (p q : ℕ) (ρ : ℝ) (z : ℂ) :
    ‖wgt p q ρ z‖ ^ 2 = (1 + ‖z‖ ^ 2) ^ (-(2 : ℝ) - (p + q : ℕ)) := by
  have hx : 0 < 1 + ‖z‖ ^ 2 := by positivity
  unfold wgt
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub, Complex.one_re]
  rw [sqrt_inv_pow_eq_rpow hx, ← Real.rpow_add hx, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  push_cast
  ring

/-- The first basis vector is the coherent state of the identity. -/
theorem bv_zero_eq_cohState (n p q : ℕ) (hp : p = n) (hq : q = 0) :
    (bv (0 : Fin (p + q + 1)) : Fin (p + q + 1) → ℂ) =
      fun k : Fin (p + q + 1) => cohState n (1 : Matrix (Fin 2) (Fin 2) ℂ) (Fin.cast (by omega) k) := by
  subst hp hq
  funext k
  simp [cohState, spinMat_one, bv, Matrix.one_apply, eq_comm]

/-- **`tlin` on the first basis vector**: `tfun e₀ (z) = wgt z · z^n`. -/
theorem tfun_bv_zero (n : ℕ) (ρ : ℝ) (z : ℂ) :
    tfun (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ (bv 0) z =
      wgt (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ z * z ^ n := by
  have hp : 0 + p0 (n : ℤ) = n := by simp [p0]
  have hq : 0 + q0 (n : ℤ) = 0 := by simp [q0]
  unfold tfun
  rw [chart_hvec]
  congr 1
  rw [bv_zero_eq_cohState n _ _ hp hq, lam_emb_cohState_cast n _ _ hp hq]
  simp

/-- The squared `L²` norm of an element given by a function. -/
theorem norm_sq_toLp (f : ℂ → ℂ) (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ z : ℂ, ‖f z‖ ^ 2 := by
  have h : (((‖hf.toLp f‖ ^ 2 : ℝ)) : ℂ) = (((∫ z : ℂ, ‖f z‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    have h0 : (((‖hf.toLp f‖ ^ 2 : ℝ)) : ℂ) = inner ℂ (hf.toLp f) (hf.toLp f) := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [h0, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf] with z hz
    rw [hz, inner_self_eq_norm_sq_to_K]
    simp
  exact_mod_cast h

/-- The radial integrand in the form used by `lintegral_comp_normSq`. -/
theorem rpow_form (n : ℕ) {u : ℝ} (hu : 0 < u) :
    u ^ n * (1 + u) ^ (-(2 : ℝ) - n) = u ^ n / (1 + u) ^ (n + 2) := by
  have h1 : 0 < 1 + u := by linarith
  rw [show (-(2 : ℝ) - n) = -((n + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg h1.le,
    Real.rpow_natCast, div_eq_mul_inv]

/-- **The norm of the lowest-level vector.** In the `L²(ℂ)` normalisation of
`PrincipalSeries.lean` (Lebesgue measure on the chart `z ↦ (z, 1)`), the norm `nrmA = ‖A e₀‖` of the
explicit intertwiner `A = tlin` of the lowest level `(p, q) = (n, 0)` of `(n/2, ρ)` satisfies
`nrmA² = π/(n+1)`, because `∫_ℂ (1+|z|²)^{-2-n} |z|^{2n} dz = π ∫₀^∞ u^n (1+u)^{-n-2} du =
π B(n+1, 1) = π/(n+1)` (polar coordinates, `lintegral_comp_normSq`; DLMF 5.12.3 with `a = n+1`,
`b = 1`). It covers only the lowest K-type; the value is checked numerically in
`scripts/asymptotics/link_integral_check.py`. -/
theorem nrmA_sq_lowest (n : ℕ) (ρ : ℝ) :
    nrmA (tlin (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ) ^ 2 = Real.pi / (n + 1) := by
  have hm := memLp_tfun (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ (bv 0)
  have h1 : nrmA (tlin (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ) ^ 2 =
      ∫ z : ℂ, ‖tfun (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ (bv 0) z‖ ^ 2 := by
    unfold nrmA
    exact norm_sq_toLp _ hm
  rw [h1]
  set h : ℝ → ℝ := fun u => u ^ n * (1 + u) ^ (-(2 : ℝ) - n) with hh
  have h2 : ∀ z : ℂ, ‖tfun (0 + p0 (n : ℤ)) (0 + q0 (n : ℤ)) ρ (bv 0) z‖ ^ 2 = h (‖z‖ ^ 2) := by
    intro z
    rw [tfun_bv_zero, norm_mul, mul_pow, norm_sq_wgt, norm_pow, ← pow_mul]
    have : (0 + p0 (n : ℤ)) + (0 + q0 (n : ℤ)) = n := by simp [p0, q0]
    rw [this, hh, mul_comm n 2, pow_mul]
    simp only [mul_comm]
  simp_rw [h2]
  have hmeas : Measurable h := by
    rw [hh]; fun_prop
  have hnonneg : ∀ u : ℝ, 0 ≤ u → 0 ≤ h u := fun u hu => by
    rw [hh]; have : 0 < 1 + u := by linarith
    positivity
  have hrad : ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (h u) = ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    obtain ⟨hint, hval⟩ := radial_integral n
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun u => ENNReal.ofReal
      (u ^ n / (1 + u) ^ (n + 2))) (fun u hu => by rw [hh]; simp only [rpow_form n hu]),
      ← ofReal_integral_eq_lintegral_ofReal hint, hval]
    exact (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => by
      have : (0 : ℝ) < u := hu
      positivity)
  have hcomp := lintegral_comp_normSq (fun u => ENNReal.ofReal (h u)) hmeas.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun z => hnonneg _ (by positivity))
    (hmeas.comp (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ 2)).aestronglyMeasurable, hcomp, hrad,
    ← ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **`link_integral` with the explicit constant**: the constant `(‖A e₀‖²)⁻¹` is `(n+1)/π`.
Same hypotheses and limits as `link_integral`; the Lebesgue measure on the chart is that of
`PrincipalSeries.lean`. -/
theorem link_integral_explicit (γ : ℝ) (n : ℕ) (g1 g2 : SU2) (a b : SL2C) :
    ∑ m : Fin (dsp (n : ℤ) 0 + 1), ∑ m' : Fin (dsp (n : ℤ) 0 + 1),
        conj (cohVec n (g1 : Matrix (Fin 2) (Fin 2) ℂ) m) *
          cohVec n (g2 : Matrix (Fin 2) (Fin 2) ℂ) m' * eprlCoeff γ n m m' (a⁻¹ * b) =
      ((((n : ℝ) + 1) / Real.pi : ℝ) : ℂ) *
        ∫ w : ℂ, Complex.exp (triAction ((n : ℝ) / 2) (eprlRho γ n)
            (spinAct ((a : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
            (firstCol ((g1 : Matrix (Fin 2) (Fin 2) ℂ).map star))
            (spinAct ((b : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
            (firstCol (wM * (g2 : Matrix (Fin 2) (Fin 2) ℂ)))) *
          (((‖spinAct ((a : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2 *
            ‖spinAct ((b : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [link_integral, nrmA_sq_lowest, inv_div]

end Lightlike.Asymptotics.Lorentzian
