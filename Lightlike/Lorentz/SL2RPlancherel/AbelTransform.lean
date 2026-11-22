module

public import Mathlib

/-!
# The spherical transform of `SL(2,ℝ)` as a Fourier transform of the Abel transform

A radial (`SO(2)`-biinvariant) function on `SL(2,ℝ)` is `F ∘ coshDistR`, and on the upper half-plane
`cosh d(i, x + iy) = (x² + y² + 1)/(2y)` (`coshDistR_toSL2R`). The spherical function of the
principal series with exponent `s = 1/2 + iρ` averages `y^s` over `SO(2)`; against a radial
function it may be replaced by `y^s` itself, so the spherical transform is

  `f̂(ρ) = ∫_ℍ F((x² + y² + 1)/(2y)) y^{1/2 + iρ} dx dy / y²`.

Writing `y = eᵗ` and `x = e^{t/2} w` gives `f̂(ρ) = ∫ e^{iρt} (𝒜F)(t) dt` with the Abel transform
`𝒜F(t) = ∫_ℝ F(cosh t + w²/2) dw` (`sphTransform_eq_integral_abel`). This is the first step of
Plancherel's theorem for the hyperbolic plane (Mehler–Fock), whose density is `ρ tanh(πρ)`.

## References

* S. Helgason, *Groups and Geometric Analysis* (1984), Chapter III: the Abel transform.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The **Abel transform** of `F : ℝ → ℂ` on the hyperbolic plane:
`𝒜F(t) = ∫_ℝ F(cosh t + w²/2) dw`, the integral of `F ∘ coshDistR` over the horocycle `y = eᵗ`
with the measure normalised by `dx = e^{t/2} dw`. -/
noncomputable def abelTransform (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ w : ℝ, F (Real.cosh t + w ^ 2 / 2)

/-- The **spherical transform** of the radial function `F ∘ coshDistR` on the upper half-plane,
`f̂(ρ) = ∫_ℍ F((x² + y² + 1)/(2y)) y^{1/2 + iρ} dx dy / y²`, written as an iterated integral. -/
noncomputable def sphTransformH (F : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ∫ x : ℝ, F ((x ^ 2 + y ^ 2 + 1) / (2 * y)) *
    Complex.exp ((-3 / 2 + ρ * Complex.I) * (Real.log y : ℂ))

/-- **The spherical transform is the Fourier transform of the Abel transform**:
`f̂(ρ) = ∫ e^{iρt} 𝒜F(t) dt`. No integrability is assumed. -/
theorem sphTransformH_eq_integral_abel (F : ℝ → ℂ) (ρ : ℝ) :
    sphTransformH F ρ = ∫ t : ℝ, Complex.exp (ρ * t * Complex.I) * abelTransform F t := by
  unfold sphTransformH
  rw [← integral_comp_exp (fun y => ∫ x : ℝ, F ((x ^ 2 + y ^ 2 + 1) / (2 * y)) *
    Complex.exp ((-3 / 2 + ρ * Complex.I) * (Real.log y : ℂ)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.log_exp]
  rw [integral_mul_const]
  have ha : (Real.exp (t / 2)) ≠ 0 := (Real.exp_pos _).ne'
  have hsc := Measure.integral_comp_mul_left (fun x : ℝ => F ((x ^ 2 + Real.exp t ^ 2 + 1) /
    (2 * Real.exp t))) (Real.exp (t / 2))
  rw [abs_of_pos (by positivity)] at hsc
  have hcongr : ∀ w : ℝ, F (((Real.exp (t / 2) * w) ^ 2 + Real.exp t ^ 2 + 1) /
      (2 * Real.exp t)) = F (Real.cosh t + w ^ 2 / 2) := fun w => by
    congr 1
    have h1 : Real.exp (t / 2) ^ 2 = Real.exp t := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h2 := Real.exp_pos t
    rw [Real.cosh_eq, Real.exp_neg, mul_pow, h1]
    field_simp
    ring
  simp only [hcongr] at hsc
  have hI : ∫ x : ℝ, F ((x ^ 2 + Real.exp t ^ 2 + 1) / (2 * Real.exp t)) =
      (Real.exp (t / 2) : ℂ) * abelTransform F t := by
    have ha' : (Real.exp (t / 2) : ℂ) ≠ 0 := by exact_mod_cast ha
    rw [abelTransform, hsc, Complex.real_smul]
    push_cast
    field_simp
  rw [hI, Complex.real_smul]
  have hprod : (Real.exp t : ℂ) * (Real.exp (t / 2) : ℂ) *
      Complex.exp ((-3 / 2 + ρ * Complex.I) * (t : ℂ)) = Complex.exp (ρ * t * Complex.I) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hprod]
  ring

end Lightlike.Lorentz.SL2RPlancherel
