import Mathlib
import Lightlike.Dirac.ModeODE

/-!
# The regular solution of the radial mode system as a power series (stage S1)

With `a = r^m F(t)`, `b = r^{m+1} H(t)`, `t = r²`, `μ = ν/2`, the system is `(1+t) F' = μ H`,
`(1+t)(t H' + (m+1) H) = μ F`.  The Taylor coefficients `f_n`, `h_n` (normalised by `f₀ = 1`) satisfy
`(n+1) f_{n+1} + n f_n = μ h_n` and `(n+m+1) h_n + (n+m) h_{n-1} = μ f_n`.
They grow at most polynomially, so the series converge for `|t| < 1`.
-/

namespace Lightlike.Dirac

/-- The pair `(f_n, h_{n-1})` of Taylor coefficients (with `h_{-1} = 0`), `f₀ = 1`. -/
noncomputable def coefPair (μ : ℂ) (m : ℕ) : ℕ → ℂ × ℂ
  | 0 => (1, 0)
  | n + 1 =>
    let p := coefPair μ m n
    let hn := (μ * p.1 - ((n : ℂ) + m) * p.2) / ((n : ℂ) + m + 1)
    ((μ * hn - (n : ℂ) * p.1) / ((n : ℂ) + 1), hn)

/-- The coefficients of `F`. -/
noncomputable def coefF (μ : ℂ) (m : ℕ) (n : ℕ) : ℂ := (coefPair μ m n).1

/-- The coefficients of `H`. -/
noncomputable def coefH (μ : ℂ) (m : ℕ) (n : ℕ) : ℂ := (coefPair μ m (n + 1)).2

/-- `h_n` from the pair at stage `n`. -/
lemma coefH_eq (μ : ℂ) (m n : ℕ) :
    ((n : ℂ) + m + 1) * coefH μ m n = μ * coefF μ m n - ((n : ℂ) + m) * (coefPair μ m n).2 := by
  have hne : ((n : ℂ) + m + 1) ≠ 0 := by
    have : (0 : ℝ) < n + m + 1 := by positivity
    exact_mod_cast this.ne'
  unfold coefH coefF
  rw [coefPair]
  simp only []
  field_simp

/-- First recurrence: `(n+1) f_{n+1} + n f_n = μ h_n`. -/
lemma coefF_succ (μ : ℂ) (m n : ℕ) :
    ((n : ℂ) + 1) * coefF μ m (n + 1) + (n : ℂ) * coefF μ m n = μ * coefH μ m n := by
  have hne : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold coefF coefH
  rw [coefPair]
  simp only []
  field_simp
  ring

end Lightlike.Dirac
