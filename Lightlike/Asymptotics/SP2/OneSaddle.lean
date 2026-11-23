import Lightlike.Asymptotics.SaddleAssemblyTests

/-!
# Trust check for SP2: one of the two complex-conjugate saddles is not enough

The Racah sum is real, and its saddle-point asymptotics comes from the two complex-conjugate
saddles `s` and `s̄` of the phase: each contributes half of the amplitude, and together they give
`cos (S + π/4) / (√(12π) (2π)²)` (`racahSumAsymptotics`). Keeping a single saddle gives half of
that amplitude. This file shows that the formula with the amplitude of one saddle fails, at the
regular tetrahedron `j = (1, …, 1)`, where the Regge action is `6θ λ + 3θ`, `θ = π − arccos ⅓`.

The proof: if both the full and the half amplitude held, `cos (α λ + β) → 0` with `α = 6θ`; then
`sin (α λ + β)² → 1`, and the angle-addition formula forces `sin α = 0`, i.e. `cos 6θ = ±1`, but
`cos 6θ = T₆(⅓) = 329/729`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- If `cos (α n + β) → 0` along the naturals, then `sin α = 0`. -/
lemma sin_eq_zero_of_tendsto_cos_zero (α β : ℝ)
    (h : Tendsto (fun n : ℕ => Real.cos (α * n + β)) atTop (𝓝 0)) : Real.sin α = 0 := by
  have h1 : Tendsto (fun n : ℕ => Real.cos (α * ((n + 1 : ℕ) : ℝ) + β)) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun n : ℕ => (Real.sin (α * n + β) * Real.sin α) ^ 2) atTop
      (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => Real.cos (α * n + β) * Real.cos α -
        Real.cos (α * ((n + 1 : ℕ) : ℝ) + β)) atTop (𝓝 (0 * Real.cos α - 0)) :=
      (h.mul_const _).sub h1
    have h4 : ∀ n : ℕ, Real.cos (α * n + β) * Real.cos α -
        Real.cos (α * ((n + 1 : ℕ) : ℝ) + β) = Real.sin (α * n + β) * Real.sin α := by
      intro n
      have : α * ((n + 1 : ℕ) : ℝ) + β = (α * n + β) + α := by push_cast; ring
      rw [this, Real.cos_add (α * n + β) α]; ring
    simp only [h4, zero_mul, sub_zero] at h3
    simpa using h3.pow 2
  have h5 : Tendsto (fun n : ℕ => (Real.sin (α * n + β) * Real.sin α) ^ 2) atTop
      (𝓝 ((1 - 0 ^ 2) * Real.sin α ^ 2)) := by
    have : Tendsto (fun n : ℕ => (1 - Real.cos (α * n + β) ^ 2) * Real.sin α ^ 2) atTop
        (𝓝 ((1 - 0 ^ 2) * Real.sin α ^ 2)) :=
      ((tendsto_const_nhds.sub (h.pow 2)).mul_const _)
    refine this.congr fun n => ?_
    have := Real.sin_sq_add_cos_sq (α * n + β)
    rw [mul_pow]; congr 1; linarith
  have := tendsto_nhds_unique h5 h2
  have h6 : Real.sin α ^ 2 = 0 := by simpa using this
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h6

/-- `cos (6 (π − arccos ⅓)) = 329/729` (`T₆(⅓)`), so `sin (6 (π − arccos ⅓)) ≠ 0`. -/
lemma sin_six_theta_ne_zero : Real.sin (6 * (π - Real.arccos (1 / 3))) ≠ 0 := by
  intro h
  have hc : Real.cos (6 * (π - Real.arccos (1 / 3))) = 329 / 729 := by
    have e : 6 * (π - Real.arccos (1 / 3)) = 2 * (3 * (π - Real.arccos (1 / 3))) := by ring
    have hc1 : Real.cos (π - Real.arccos (1 / 3)) = -(1 / 3) := by
      rw [Real.cos_pi_sub, Real.cos_arccos (by norm_num) (by norm_num)]
    rw [e, Real.cos_two_mul, Real.cos_three_mul, hc1]
    norm_num
  have := Real.sin_sq_add_cos_sq (6 * (π - Real.arccos (1 / 3)))
  rw [h, hc] at this
  norm_num at this

/-- **One saddle is not enough**: at the regular tetrahedron, the formula of
`racahSumAsymptotics_regular` with the amplitude of a single saddle (half of the full amplitude)
is false. -/
theorem not_racahSumAsymptotics_one_saddle_regular :
    ¬ Tendsto (fun lam : ℕ =>
      √(√(vol2l (PR.lengths (fun _ => 1) lam))) *
          Real.exp (-prefactorRate (PR.lengths (fun _ => 1) lam)) * racahSum (fun _ => lam) -
        (1 / 2) * Real.cos (6 * (π - Real.arccos (1 / 3)) * lam +
          3 * (π - Real.arccos (1 / 3)) + π / 4) /
          (√(12 * π) * (2 * π) ^ 2)) atTop (𝓝 0) := by
  intro h
  have hd := racahSumAsymptotics_regular.sub h
  have hC : 0 < √(12 * π) * (2 * π) ^ 2 := by positivity
  have hcos : Tendsto (fun n : ℕ => Real.cos (6 * (π - Real.arccos (1 / 3)) * n +
      (3 * (π - Real.arccos (1 / 3)) + π / 4))) atTop (𝓝 0) := by
    have := hd.const_mul (-(2 * (√(12 * π) * (2 * π) ^ 2)))
    simp only [sub_self, mul_zero] at this
    refine this.congr fun n => ?_
    field_simp
    ring_nf
  exact sin_six_theta_ne_zero (sin_eq_zero_of_tendsto_cos_zero _ _ hcos)

end Lightlike.Asymptotics
