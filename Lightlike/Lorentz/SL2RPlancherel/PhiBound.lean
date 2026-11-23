import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.SqrtWeight

/-!
# An `H¹`-type bound for the weighted Fourier transform

For a Schwartz function `g` on `ℝ` put `Φ g (ρ) = √(ρ tanh πρ)/(2π) · ĝ(ρ/2π)`; for
`g = 𝒜F` (the Abel transform of a test function `F`) this is `sphL2fun F`
(`phi_abelSchwartz`).  Since `ρ tanh πρ ≤ |ρ|`, Plancherel for the Fourier transform on `ℝ`
gives `‖Φ g‖²_{L²(0,∞)} ≤ ‖g‖² + ‖g'‖²` (`integral_norm_sq_phi_le`).  This continuity of `Φ` in the
`H¹` norm is the analytic input to the surjectivity of the spherical Plancherel isometry for
`SL(2,ℝ)` (milestone HA3): it lets the range of `sphericalL2` be shown to contain `Φ g` for `g`
that is only an `H¹` limit of Abel transforms.
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The square-root Plancherel weight `√(ρ tanh πρ)/(2π)`. -/
def phiW (ρ : ℝ) : ℝ := Real.sqrt (ρ * Real.tanh (Real.pi * ρ)) / (2 * Real.pi)

/-- The weighted Fourier transform `Φ g (ρ) = √(ρ tanh πρ)/(2π) · ĝ(ρ/2π)` of a Schwartz function. -/
def phi (g : SchwartzMap ℝ ℂ) (ρ : ℝ) : ℂ :=
  (phiW ρ : ℂ) * (SchwartzMap.fourierTransformCLM ℂ g) (ρ / (2 * Real.pi))

/-- `Φ (𝒜F) = sphL2fun F`. -/
theorem phi_abelSchwartz (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    phi (abelSchwartz F hF hc) = sphL2fun F := by
  funext ρ
  unfold phi sphL2fun
  rw [sphTransformH_eq_schwartz F hF hc]
  rfl

/-- `ρ tanh(πρ) ≤ |ρ|`. -/
theorem mul_tanh_le_abs (ρ : ℝ) : ρ * Real.tanh (Real.pi * ρ) ≤ |ρ| := by
  have h1 := Real.tanh_lt_one (Real.pi * ρ)
  have h2 := Real.neg_one_lt_tanh (Real.pi * ρ)
  rcases le_total 0 ρ with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

/-- Pointwise bound: `phiW(ρ)² a ≤ (a + b/(4π²)) / (4π)` when `b = ρ² a`. -/
theorem phiW_sq_mul_le (ρ a b : ℝ) (ha : 0 ≤ a) (hb : b = ρ ^ 2 * a) :
    phiW ρ ^ 2 * a ≤ (a + b / (4 * Real.pi ^ 2)) / (4 * Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h1 : phiW ρ ^ 2 ≤ |ρ| / (4 * Real.pi ^ 2) := by
    unfold phiW
    rw [div_pow, Real.sq_sqrt (mul_tanh_pi_mul_nonneg ρ)]
    have : (2 * Real.pi) ^ 2 = 4 * Real.pi ^ 2 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (mul_tanh_le_abs ρ) (by positivity)
  calc phiW ρ ^ 2 * a ≤ |ρ| / (4 * Real.pi ^ 2) * a := mul_le_mul_of_nonneg_right h1 ha
    _ ≤ _ := by
      rw [← sub_nonneg, hb]
      have e : (a + ρ ^ 2 * a / (4 * Real.pi ^ 2)) / (4 * Real.pi) -
          |ρ| / (4 * Real.pi ^ 2) * a =
          a * ((2 * Real.pi - |ρ|) ^ 2) / (16 * Real.pi ^ 3) := by
        have : ρ ^ 2 = |ρ| ^ 2 := (sq_abs ρ).symm
        rw [this]
        field_simp
        ring
      rw [e]
      positivity

/-- **`H¹` bound**: `‖Φ g‖²_{L²(0,∞)} ≤ ‖g‖²_{L²} + ‖g'‖²_{L²}` for a Schwartz function `g`. -/
theorem integral_norm_sq_phi_le (g : SchwartzMap ℝ ℂ) :
    ∫ ρ in Ioi (0 : ℝ), ‖phi g ρ‖ ^ 2 ≤ (∫ x, ‖g x‖ ^ 2) + ∫ x, ‖deriv g x‖ ^ 2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set dg : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ g with hdg
  set G : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ g with hG
  set G' : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ dg with hG'
  have hdgf : (dg : ℝ → ℂ) = deriv g := funext fun x => SchwartzMap.derivCLM_apply ℂ g x
  have hGG' : ∀ ξ : ℝ, G' ξ = ((2 * Real.pi * Complex.I * ξ : ℂ)) • G ξ := by
    intro ξ
    have h := congrFun (Real.fourier_deriv (E := ℂ) g.integrable g.differentiable
      (by rw [← hdgf]; exact dg.integrable)) ξ
    rw [← hdgf] at h
    exact h
  have hnorm : ∀ ξ : ℝ, ‖G' ξ‖ ^ 2 = (2 * Real.pi * ξ) ^ 2 * ‖G ξ‖ ^ 2 := by
    intro ξ
    rw [hGG', norm_smul, mul_pow]
    congr 1
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_real, abs_of_pos hπ]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  -- integrability of the squared norms
  have hint : ∀ S : SchwartzMap ℝ ℂ, Integrable (fun x => ‖S x‖ ^ 2) := fun S =>
    (memLp_two_iff_integrable_sq_norm S.continuous.aestronglyMeasurable).1 (S.memLp 2)
  have hI1 : Integrable (fun ρ : ℝ => ‖G (ρ / (2 * Real.pi))‖ ^ 2) :=
    (hint G).comp_div (by positivity)
  have hI2 : Integrable (fun ρ : ℝ => ‖G' (ρ / (2 * Real.pi))‖ ^ 2) :=
    (hint G').comp_div (by positivity)
  set M : ℝ → ℝ := fun ρ => (‖G (ρ / (2 * Real.pi))‖ ^ 2 +
    ‖G' (ρ / (2 * Real.pi))‖ ^ 2 / (4 * Real.pi ^ 2)) / (4 * Real.pi) with hM
  have hMi : Integrable M := ((hI1.add (hI2.div_const _)).div_const _)
  have hpt : ∀ ρ : ℝ, ‖phi g ρ‖ ^ 2 ≤ M ρ := by
    intro ρ
    unfold phi
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    apply phiW_sq_mul_le ρ _ _ (by positivity)
    rw [hnorm]
    congr 1
    field_simp
  have hnn : ∀ ρ : ℝ, 0 ≤ ‖phi g ρ‖ ^ 2 := fun ρ => by positivity
  have hMnn : ∀ ρ : ℝ, 0 ≤ M ρ := fun ρ => (hnn ρ).trans (hpt ρ)
  calc ∫ ρ in Ioi (0 : ℝ), ‖phi g ρ‖ ^ 2
      ≤ ∫ ρ in Ioi (0 : ℝ), M ρ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hMi.integrableOn
          (Filter.Eventually.of_forall hpt)
    _ ≤ ∫ ρ, M ρ := setIntegral_le_integral hMi (Filter.Eventually.of_forall hMnn)
    _ = (∫ x, ‖g x‖ ^ 2) / 2 + (∫ x, ‖deriv g x‖ ^ 2) / (8 * Real.pi ^ 2) := by
      have e1 : ∫ ρ : ℝ, ‖G (ρ / (2 * Real.pi))‖ ^ 2 = 2 * Real.pi * ∫ x, ‖g x‖ ^ 2 := by
        rw [Measure.integral_comp_div (fun ξ => ‖G ξ‖ ^ 2) (2 * Real.pi),
          abs_of_pos (by positivity), smul_eq_mul]
        have h1 : ∫ y, ‖G y‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := SchwartzMap.integral_norm_sq_fourier g
        rw [h1]
      have e2 : ∫ ρ : ℝ, ‖G' (ρ / (2 * Real.pi))‖ ^ 2 = 2 * Real.pi * ∫ x, ‖deriv g x‖ ^ 2 := by
        rw [Measure.integral_comp_div (fun ξ => ‖G' ξ‖ ^ 2) (2 * Real.pi),
          abs_of_pos (by positivity), smul_eq_mul]
        have h2 : ∫ y, ‖G' y‖ ^ 2 = ∫ x, ‖dg x‖ ^ 2 := SchwartzMap.integral_norm_sq_fourier dg
        rw [h2, hdgf]
      simp only [hM]
      rw [integral_div, integral_add hI1 (hI2.div_const _), integral_div, e1, e2]
      field_simp
      ring
    _ ≤ _ := by
      have h0 : 0 ≤ ∫ x, ‖g x‖ ^ 2 := integral_nonneg fun x => by positivity
      have h0' : 0 ≤ ∫ x, ‖deriv g x‖ ^ 2 := integral_nonneg fun x => by positivity
      have hp : (1 : ℝ) ≤ 8 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have : (∫ x, ‖deriv g x‖ ^ 2) / (8 * Real.pi ^ 2) ≤ ∫ x, ‖deriv g x‖ ^ 2 :=
        div_le_self h0' hp
      linarith

end Lightlike.Lorentz.SL2RPlancherel
