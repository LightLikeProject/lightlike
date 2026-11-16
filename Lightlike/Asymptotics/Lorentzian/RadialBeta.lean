import Mathlib

/-!
# The Beta integral `∫₀^∞ u^n (1+u)^{-n-2} du = 1/(n+1)`

DLMF 5.12.3, `∫₀^∞ t^{a-1} (1+t)^{-a-b} dt = B(a, b)`, with `a = n + 1`, `b = 1`, and
`B(n+1, 1) = Γ(n+1) Γ(1) / Γ(n+2) = 1/(n+1)` (DLMF 5.12.1). It is proved here without the Gamma
function, from the antiderivative `(t/(1+t))^{n+1}/(n+1)`; it gives the norm of the lowest-level
vector of the principal series (`π/(n+1)`).
-/

open MeasureTheory Set Filter Topology

namespace Lightlike.Asymptotics.Lorentzian

/-- `∫₀^∞ u^n / (1+u)^(n+2) du = 1/(n+1)` (DLMF 5.12.3 with `a = n+1`, `b = 1`). -/
theorem radial_integral (n : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ n / (1 + u) ^ (n + 2)) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), u ^ n / (1 + u) ^ (n + 2) = 1 / ((n : ℝ) + 1) := by
  set F : ℝ → ℝ := fun t => (t / (1 + t)) ^ (n + 1) / ((n : ℝ) + 1) with hF
  have hder : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F (x ^ n / (1 + x) ^ (n + 2)) x := by
    intro x hx
    have hx1 : (1 + x) ≠ 0 := by have : (0:ℝ) ≤ x := hx; positivity
    have h1 : HasDerivAt (fun t : ℝ => t / (1 + t)) (1 / (1 + x) ^ 2) x := by
      have := ((hasDerivAt_id' x).div ((hasDerivAt_id' x).const_add 1) hx1)
      exact this.congr_deriv (by field_simp; ring)
    have h2 := (h1.pow (n + 1)).div_const ((n : ℝ) + 1)
    refine h2.congr_deriv ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    push_cast
    rw [div_pow]
    field_simp
    rw [pow_add]; ring
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x ^ n / (1 + x) ^ (n + 2) := by
    intro x hx
    have : (0:ℝ) < x := hx
    positivity
  have hlim : Tendsto F atTop (𝓝 (1 / ((n : ℝ) + 1))) := by
    have h : Tendsto (fun t : ℝ => t / (1 + t)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun t : ℝ => 1 - 1 / (1 + t)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_id))
      rw [sub_zero] at h0
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have : (1 + t) ≠ 0 := by positivity
      field_simp; ring
    have := (h.pow (n + 1)).div_const ((n : ℝ) + 1)
    simpa using this
  have hint := integrableOn_Ioi_deriv_of_nonneg' hder hnonneg hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hder hint hlim]
  simp [hF]

end Lightlike.Asymptotics.Lorentzian
