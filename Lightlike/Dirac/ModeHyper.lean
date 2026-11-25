import Mathlib
import Lightlike.Dirac.ModeSeries
import Lightlike.Dirac.GaussSum

/-!
# The regular mode solution as a hypergeometric series

`G(x) = Σ hgTerm a (m+1) n · xⁿ` is `₂F₁(a, −a; m+1; x)`.  It is differentiable twice on `(-1, 1)` and satisfies
`x(1−x) G'' + (m+1−x) G' + a² G = 0`.
-/

namespace Lightlike.Dirac

/-- The coefficients of `₂F₁(a, −a; m+1; x)`. -/
noncomputable def hgCoef (a : ℂ) (m : ℕ) : ℕ → ℂ := hgTerm a ((m : ℂ) + 1)

/-- Recurrence of the coefficients. -/
lemma hgCoef_succ (a : ℂ) (m n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + m + 1) * hgCoef a m (n + 1) = ((n : ℂ) ^ 2 - a ^ 2) * hgCoef a m n := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : ((n : ℂ) + m + 1) ≠ 0 := by
    have : (0 : ℝ) < n + m + 1 := by positivity
    exact_mod_cast this.ne'
  unfold hgCoef
  rw [hgTerm]
  have : ((m : ℂ) + 1 + n) = ((n : ℂ) + m + 1) := by ring
  rw [this]
  field_simp
  ring

/-- The sum `G(x)`. -/
noncomputable def hgSum (a : ℂ) (m : ℕ) : ℝ → ℂ := powerSum (hgCoef a m)

/-- First derivative coefficients `(n+1) γ_{n+1}`. -/
noncomputable def hgCoef1 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef a m (n + 1)

/-- Second derivative coefficients `(n+1)(n+2) γ_{n+2}`. -/
noncomputable def hgCoef2 (a : ℂ) (m : ℕ) (n : ℕ) : ℂ := ((n : ℂ) + 1) * hgCoef1 a m (n + 1)

lemma hgCoef_bound (a : ℂ) (m n : ℕ) : ‖hgCoef a m n‖ ≤ 1 * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1) := by
  rw [one_mul]; exact hgTerm_bound a m n

/-- `G' = Σ (n+1) γ_{n+1} xⁿ`. -/
theorem hasDerivAt_hgSum (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (hgSum a m) (powerSum (hgCoef1 a m) x) x :=
  hasDerivAt_powerSum zero_le_one (hgCoef_bound a m) hx

/-- Growth bound of the first derivative coefficients. -/
lemma hgCoef1_bound (a : ℂ) (m n : ℕ) :
    ‖hgCoef1 a m n‖ ≤ (1 * 2 ^ (2 * max ‖a‖ 1)) * ((n : ℝ) + 1) ^ (2 * max ‖a‖ 1 + 1) :=
  deriv_coeff_bound (by positivity) zero_le_one (hgCoef_bound a m) n

/-- `G'' = Σ (n+1)(n+2) γ_{n+2} xⁿ`. -/
theorem hasDerivAt_hgSum1 (a : ℂ) (m : ℕ) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (powerSum (hgCoef1 a m)) (powerSum (hgCoef2 a m) x) x :=
  hasDerivAt_powerSum (by positivity) (hgCoef1_bound a m) hx

end Lightlike.Dirac
