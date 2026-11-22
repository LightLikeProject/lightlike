import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelTruncation
import Lightlike.Lorentz.SL2RPlancherel.CoshChange

/-!
# The `L²(1,∞)` norm of `F` as a quadrant form of `(𝒜F)'`

For `F` of class `C²` with compact support and `g = 𝒜F` its Abel transform,
`π² ∫_{v>1} |F v|² = ½ ∫_{t>0} ∫_{s>0} g'(t) conj g'(s) (L(s-t) - L(s+t)) ds dt`,
`L = logTanhKernel`.  Combined with `integral_logTanhKernel_deriv_quadrant` this is the
Plancherel identity for the spherical principal series of SL(2,ℝ) with density `ρ tanh(πρ)`
(milestone HA3).
-/

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Quadrant form of the norm.** For `F` of class `C²` with compact support, with
`g = abelTransform F`,
`π² ∫_{v>1} F conj F = ½ ∫_{t>0} ∫_{s>0} g'(t) conj g'(s) quadKernel t s`. -/
theorem norm_sq_eq_quadrant (F : ℝ → ℂ) (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) :
    (π : ℂ) ^ 2 * ∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v) =
      (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        deriv (abelTransform F) t * (starRingEnd ℂ) (deriv (abelTransform F) s) *
          ((quadKernel t s : ℝ) : ℂ) := by
  obtain ⟨R, M, φ, hφ, hM, hR, hag, hint, htriple⟩ := exists_triple_integral_eq F hF hc
  rw [← htriple, triple_integral_eq_quadrant φ (fun x => (starRingEnd ℂ) (φ x)),
    ← integral_const_mul]
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have h2 : (√2 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < √2 := by positivity
    exact_mod_cast this.ne'
  have h22 : (√2 : ℂ) * (√2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    simp
  have key : ∀ t : ℝ, 0 < t →
      (Real.sinh t : ℂ) * φ (Real.cosh t) = deriv (abelTransform F) t / (√2 : ℂ) := by
    intro t ht
    rw [(hasDerivAt_abelTransform F hF1 hc t).deriv, hag _ (Real.one_lt_cosh.2 ht.ne')]
    field_simp
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  have hk1 := key t ht
  have hk2 : (Real.sinh s : ℂ) * (starRingEnd ℂ) (φ (Real.cosh s)) =
      (starRingEnd ℂ) (deriv (abelTransform F) s / (√2 : ℂ)) := by
    rw [← key s hs, map_mul, Complex.conj_ofReal]
  rw [hk1, hk2, map_div₀]
  have : (starRingEnd ℂ) (√2 : ℂ) = √2 := by
    exact Complex.conj_ofReal _
  rw [this]
  field_simp
  rw [pow_two, h22]
  ring

end Lightlike.Lorentz.SL2RPlancherel
