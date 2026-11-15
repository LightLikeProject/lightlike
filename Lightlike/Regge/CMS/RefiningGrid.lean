import Mathlib
import Lightlike.Regge.CMS.HyperbolicGrid

/-!
# A refining family of grids on a fixed square

The `n × n` grid triangulation of the unit square, with mesh `h = 1 / n`, satisfies every
hypothesis of the convergence theorem for each `n`, with the constants `ρ = 1`, `N = 6`,
`M = 1`, `m = 8` independent of `n` (`grid_bound_general`). Hence one pair `(C, h₀)` serves the
whole family: the weighted deficit sum differs from the curvature integral over the interior
triangles by at most `C / n` for every `n ≥ 1 / h₀`.

For the hyperbolic plane the integral term is bounded away from `0` along the family (at most
`-1/4` for `n ≥ 4`; its limit is the integral of `-e^{x}` over the square), so the bound is not
a statement about a vanishing term.
-/

open MeasureTheory Set Real Lightlike Lightlike.Geodesic

namespace Lightlike.CMS

/-- **The refining family for any Riemannian metric.** One constant pair `(C, h₀)` for all
`n × n` grids of the unit square. -/
theorem refining_grid_bound {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    (hg : IsRiemMetric g univ) :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ n : ℕ, 1 ≤ n → 1 / (n : ℝ) ≤ h₀ →
      |∑ v ∈ gV n, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP (1 / n) v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist g univ (gP (1 / n) v) (gP (1 / n) (gnb v j)) ^ 2)
            (dist g univ (gP (1 / n) v) (gP (1 / n) (gnb v (j + 1))) ^ 2)
            (dist g univ (gP (1 / n) (gnb v j)) (gP (1 / n) (gnb v (j + 1))) ^ 2)) -
        ∫ x in gInterior n (1 / n), (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
          (scalarCurvature g x / 2 * √(g x).det)| ≤ C * (1 / n) := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := grid_bound_general hg (R := 1) one_pos
  refine ⟨C, h₀, hh₀, fun n hn hh => ?_⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact hmain n (1 / n) (by positivity) hh (by rw [one_div, inv_mul_cancel₀ hn0.ne'])

/-- **The refining family on the hyperbolic plane**, with a curvature integral at most `-1/4`
for every `n ≥ 4`, independent of `n`. -/
theorem hyp_refining_grid :
    ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ n : ℕ, 4 ≤ n → 1 / (n : ℝ) ≤ h₀ →
      |∑ v ∈ gV n, (fun _ : Fin 2 → ℝ => (1 : ℝ)) (gP (1 / n) v) *
          (2 * π - ∑ j : ZMod 6, triAngle
            (dist hypMetric univ (gP (1 / n) v) (gP (1 / n) (gnb v j)) ^ 2)
            (dist hypMetric univ (gP (1 / n) v) (gP (1 / n) (gnb v (j + 1))) ^ 2)
            (dist hypMetric univ (gP (1 / n) (gnb v j)) (gP (1 / n) (gnb v (j + 1))) ^ 2)) -
        ∫ x in gInterior n (1 / n), (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
          (scalarCurvature hypMetric x / 2 * √(hypMetric x).det)| ≤ C * (1 / n) ∧
      ∫ x in gInterior n (1 / n), (fun _ : Fin 2 → ℝ => (1 : ℝ)) x *
          (scalarCurvature hypMetric x / 2 * √(hypMetric x).det) ≤ -(1 / 4) := by
  obtain ⟨C, h₀, hh₀, hmain⟩ := refining_grid_bound isRiemMetric_hyp
  refine ⟨C, h₀, hh₀, fun n hn hh => ⟨hmain n (by omega) hh, ?_⟩⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine (hyp_integral_neg (m := n) (by omega) (h := 1 / n) (by positivity)).trans ?_
  have h4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have e : ((n - 2 : ℕ) : ℝ) = n - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [e]
  have : (1 : ℝ) / 4 ≤ ((n : ℝ) - 2) ^ 2 * (1 / n) ^ 2 := by
    have : ((n : ℝ) - 2) ^ 2 * (1 / n) ^ 2 = (1 - 2 / n) ^ 2 := by field_simp
    rw [this]
    have h12 : (1 : ℝ) / 2 ≤ 1 - 2 / n := by
      have : 2 / (n : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hn0 two_pos]; linarith
      linarith
    nlinarith
  linarith

end Lightlike.CMS
