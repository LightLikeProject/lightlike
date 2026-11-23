import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.AbelSchwartz
import Lightlike.Lorentz.SL2RPlancherel.QuadrantIdentity
import Lightlike.Lorentz.SL2RPlancherel.DerivativePlancherel

/-!
# The spherical Plancherel identity for the hyperbolic plane (test-function form)

For `F` smooth with compact support and `g = 𝒜F` its Abel transform (an even Schwartz function),
`π² ∫_{v>1} |F v|² dv = ¼ ∫_{ξ>0} (ρπ tanh(πρ)) · 2 |𝓕 g ξ|² dξ`, `ρ = 2πξ`.
This is the Plancherel formula for the `K`-biinvariant functions on `SL(2,ℝ)/SO(2)` with the
density `ρ tanh(πρ)` of the spherical principal series (milestone HA3).
-/

open MeasureTheory Set Real
open scoped FourierTransform ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Spherical Plancherel identity, test-function form.**  For `F` smooth with compact support and
`g = 𝒜F`,
`π² ∫_{v>1} F conj F = ¼ ∫_{ξ>0} (ρπ tanh(πρ)) · 2 (conj(𝓕 g ξ) 𝓕 g ξ) dξ`, `ρ = 2πξ`. -/
theorem norm_sq_eq_fourier (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (π : ℂ) ^ 2 * ∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v) =
      (1 / 4 : ℂ) * ∫ ξ in Ioi (0 : ℝ),
        (((2 * Real.pi * ξ) * Real.pi * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (2 * (starRingEnd ℂ (𝓕 (abelTransform F) ξ) * 𝓕 (abelTransform F) ξ)) := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_cast)
  have h1 := norm_sq_eq_quadrant F hF2 hc
  set g := abelSchwartz F hF hc with hg
  have hgc : (g : ℝ → ℂ) = abelTransform F := rfl
  have hge : ∀ x, g (-x) = g x := fun x => abelTransform_neg F x
  have h2 := integral_logTanhKernel_deriv_quadrant g hge
  rw [hgc] at h2
  have hN : (starRingEnd ℂ) (∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v)) =
      ∫ v in Ioi (1 : ℝ), F v * (starRingEnd ℂ) (F v) := by
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    simp [mul_comm]
  have hconj : (starRingEnd ℂ) (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        deriv (abelTransform F) t * (starRingEnd ℂ) (deriv (abelTransform F) s) *
          ((quadKernel t s : ℝ) : ℂ)) =
      ∫ y in Ioi (0:ℝ), starRingEnd ℂ (deriv (abelTransform F) y) *
        ∫ z in Ioi (0:ℝ), (((logTanhKernel (z - y) : ℝ) : ℂ) - ((logTanhKernel (z + y) : ℝ) : ℂ)) *
          deriv (abelTransform F) z := by
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [← integral_conj, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, quadKernel]
    push_cast
    ring
  have hcj : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  have h1' := congrArg (starRingEnd ℂ) h1
  rw [map_mul, map_mul, hN, hconj, map_pow, Complex.conj_ofReal, hcj] at h1'
  rw [h1']
  have h2' : (∫ y in Ioi (0:ℝ), starRingEnd ℂ (deriv (abelTransform F) y) *
        ∫ z in Ioi (0:ℝ), (((logTanhKernel (z - y) : ℝ) : ℂ) - ((logTanhKernel (z + y) : ℝ) : ℂ)) *
          deriv (abelTransform F) z) = (1 / 2 : ℂ) * ∫ ξ in Ioi (0:ℝ),
        (((2 * Real.pi * ξ) * Real.pi * Real.tanh (Real.pi * (2 * Real.pi * ξ)) : ℝ) : ℂ) *
        (2 * (starRingEnd ℂ (𝓕 (abelTransform F) ξ) * 𝓕 (abelTransform F) ξ)) := by
    rw [← h2]; ring
  rw [h2']
  ring

end Lightlike.Lorentz.SL2RPlancherel
