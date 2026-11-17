import Mathlib

/-!
# The real Beta integral

For real `a, b > 0`, `∫₀¹ s^(a-1) (1-s)^(b-1) ds = Γ(a) Γ(b) / Γ(a + b)` (`real_beta`). Mathlib states
this only over `ℂ` (`Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`); the real form is
obtained by comparing the complex powers of non-negative reals with the real powers. It is used for
the radial integrals of the Myrheim–Meyer relation count in general dimension, which is part of a
bridge between Lorentzian geometry and causal sets.

## References

* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2 (the context of the application, the relation count).
-/

open Set

namespace Lightlike.CausalSets

/-- **The Beta integral for real exponents**: `∫₀¹ s^(a-1) (1-s)^(b-1) ds = Γ(a) Γ(b) / Γ(a + b)`
for `a, b > 0`. It is the real form of Mathlib's `Complex.Gamma_mul_Gamma_eq_betaIntegral`. -/
lemma real_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (1 - s) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  unfold Complex.betaIntegral at h
  have h1 : ∀ x ∈ uIcc (0 : ℝ) 1, ((x : ℂ) ^ ((a : ℂ) - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) =
      ((x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    have e1 : ((x ^ (a - 1) : ℝ) : ℂ) = (x : ℂ) ^ ((a : ℂ) - 1) := by
      rw [Complex.ofReal_cpow hx.1]; push_cast; rfl
    have e2 : (((1 - x) ^ (b - 1) : ℝ) : ℂ) = (1 - (x : ℂ)) ^ ((b : ℂ) - 1) := by
      rw [Complex.ofReal_cpow (sub_nonneg.2 hx.2)]; push_cast; rfl
    rw [Complex.ofReal_mul, e1, e2]
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_ofReal] at h
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    show (a : ℂ) + b = ((a + b : ℝ) : ℂ) by push_cast; rfl, Complex.Gamma_ofReal] at h
  have h3 : Real.Gamma a * Real.Gamma b = Real.Gamma (a + b) * ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (1 - s) ^ (b - 1) := by
    exact_mod_cast h
  have hg : 0 < Real.Gamma (a + b) := Real.Gamma_pos_of_pos (add_pos ha hb)
  rw [h3]; field_simp

end Lightlike.CausalSets
