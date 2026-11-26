import Lightlike.GR.KerrHorizon

/-!
# Kerr: the norm of the horizon Killing field, factorised at `r₊`

Row G1-065, first piece. The Killing field `χ = ∂_t + Ω_H ∂_φ` has squared norm
`N(r, θ) = g_tt + 2 Ω_H g_tφ + Ω_H² g_φφ` (`kerrChiNorm`). It vanishes on `r = r₊`, so `N = (r - r₊) Q`
with an explicit `Q` (`kerrChiNorm_eq`), regular at `r₊`.
-/

open Matrix Real

noncomputable section

namespace Lightlike

variable (M a : ℝ)

/-- The squared norm `N(r, θ) = χ·χ` of `χ = ∂_t + Ω_H ∂_φ` in Boyer–Lindquist coordinates. -/
def kerrChiNorm (r θ : ℝ) : ℝ :=
  kerrMetric M a ![0, r, θ, 0] 0 0 + 2 * kerrOmega M a * kerrMetric M a ![0, r, θ, 0] 0 3 +
    kerrOmega M a ^ 2 * kerrMetric M a ![0, r, θ, 0] 3 3

/-- The quotient `Q = N/(r - r₊)`, in closed form. -/
def kerrChiQ (r θ : ℝ) : ℝ :=
  (-(r ^ 2 + a ^ 2 * cos θ ^ 2) ^ 2 * (r - (2 * M - kerrRplus M a)) +
      sin θ ^ 2 * a ^ 2 * (r - kerrRplus M a) *
        ((r - (2 * M - kerrRplus M a)) * (r ^ 2 + 2 * M * r + a ^ 2 * (1 - sin θ ^ 2)) + 4 * M ^ 2 * r) ^ 2 /
          (2 * M * kerrRplus M a) ^ 2) /
    (((r ^ 2 + a ^ 2) ^ 2 - (r ^ 2 - 2 * M * r + a ^ 2) * a ^ 2 * sin θ ^ 2) * (r ^ 2 + a ^ 2 * cos θ ^ 2))

/-- **Factorisation of `N`.** For `r > 0`: `N(r, θ) = (r - r₊) Q(r, θ)`. -/
theorem kerrChiNorm_eq (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    kerrChiNorm M a r θ = (r - kerrRplus M a) * kerrChiQ M a r θ := by
  have hp : 0 < kerrRplus M a := by
    unfold kerrRplus; have := Real.sqrt_nonneg (M ^ 2 - a ^ 2); linarith
  have h1 := rplus_sq_add M a h
  have hc := sin_sq_add_cos_sq θ
  have hc2 : cos θ ^ 2 = 1 - sin θ ^ 2 := by linarith
  have hs0 := sin_sq_le_one θ
  have hs1 := sq_nonneg (sin θ)
  have hS : 0 < r ^ 2 + a ^ 2 * cos θ ^ 2 := by positivity
  have hA : 0 < (r ^ 2 + a ^ 2) ^ 2 - (r ^ 2 - 2 * M * r + a ^ 2) * a ^ 2 * sin θ ^ 2 := by
    have e1 : (r ^ 2 - 2 * M * r + a ^ 2) ≤ r ^ 2 + a ^ 2 := by nlinarith
    have e2 : (r ^ 2 - 2 * M * r + a ^ 2) * a ^ 2 * sin θ ^ 2 ≤ (r ^ 2 + a ^ 2) * a ^ 2 := by
      have : (r ^ 2 - 2 * M * r + a ^ 2) * (a ^ 2 * sin θ ^ 2) ≤ (r ^ 2 + a ^ 2) * a ^ 2 := by
        calc (r ^ 2 - 2 * M * r + a ^ 2) * (a ^ 2 * sin θ ^ 2)
            ≤ (r ^ 2 + a ^ 2) * (a ^ 2 * sin θ ^ 2) :=
              mul_le_mul_of_nonneg_right e1 (by positivity)
          _ ≤ (r ^ 2 + a ^ 2) * a ^ 2 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith [sq_nonneg a]
      linarith
    nlinarith [sq_nonneg a, sq_nonneg r, mul_pos hr hr]
  unfold kerrChiNorm kerrChiQ
  rw [mul_div_assoc', eq_div_iff (mul_ne_zero hA.ne' hS.ne')]
  unfold kerrOmega
  simp only [kerrMetric, kerrS]
  simp
  rw [hc2] at hS ⊢
  clear hA hc hc2 hs0 hs1
  generalize kerrRplus M a = p at *
  have hM' : M = (p ^ 2 + a ^ 2) / (2 * p) := by
    field_simp; linarith
  subst hM'
  have hS' := hS.ne'
  field_simp
  ring

end Lightlike
