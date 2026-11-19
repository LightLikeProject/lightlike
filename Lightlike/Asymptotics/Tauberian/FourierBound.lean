import Lightlike.Asymptotics.Tauberian.FourierExchange

/-!
# A norm bound for Fourier integrals against a compactly supported kernel

If `g ≥ 0` is integrable with support in `|t| ≤ Λ` and `‖D t‖ ≤ M` for `|t| ≤ Λ`, then
`‖∫ g(t) e^{i t Δ} D(t) dt‖ ≤ (∫ g) · M` (`norm_kernel_integral_le`): the estimate of the remainder term
in MZ (5.19) and of the heavy term in (4.7).
-/

open MeasureTheory Set Complex

noncomputable section

namespace Lightlike.Tauberian

/-- **Norm bound of a kernel integral.** -/
lemma norm_kernel_integral_le {g : ℝ → ℝ} {Λ M : ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hgs : ∀ t, Λ < |t| → g t = 0) (hgi : Integrable g) {D : ℝ → ℂ}
    (hD : ∀ t, |t| ≤ Λ → ‖D t‖ ≤ M) (hM : 0 ≤ M) (Δ : ℝ) :
    ‖∫ t, (g t : ℂ) * Complex.exp (t * Δ * Complex.I) * D t‖ ≤ (∫ t, g t) * M := by
  have hb : Integrable (fun t => g t * M) := hgi.mul_const M
  refine (norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall fun t => ?_)).trans
    (le_of_eq (integral_mul_const M g))
  have hexp : ‖Complex.exp (t * Δ * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_of_nonneg (hg0 t)]
  by_cases ht : |t| ≤ Λ
  · exact mul_le_mul_of_nonneg_left (hD t ht) (hg0 t)
  · rw [hgs t (not_le.1 ht)]
    simp

end Lightlike.Tauberian
