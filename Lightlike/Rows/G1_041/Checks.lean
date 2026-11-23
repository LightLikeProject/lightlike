import Mathlib
import Lightlike.Rows.G1_041.NoHair

/-!
# The two checks of CO15 (G1-041)

* `kasner_no_isotropization`: with `Λ = 0` there is no isotropization. The Kasner solution (vacuum,
  `ρ = p = R = 0`, `σ² = 3H²`, `H = 1/(3t)`) solves the scalar system and is admissible, `H → 0`, but the
  ratio `σ²/H²` stays equal to `3`.
* `recollapse_example`: the hypothesis `R ≤ 0` (no type IX) cannot be dropped from `rate_ge`. A solution
  of the scalar system with `Λ = 3`, `ρ = σ² = 0`, `p = 4` (strong energy condition holds) and positive
  slice curvature at the initial time has `H > 0` initially, but `H` reaches `0` and becomes negative:
  the model recollapses and never expands at the de Sitter rate. As a recollapsing model has a
  big crunch in finite time, the example is a solution on a compact time window, not on `[t₀, ∞)`.
  It is not a physical type IX model: its pressure is a constant and the dominant energy condition fails.
-/

open Set Filter Topology
open scoped Real

namespace Lightlike
namespace Cosmology
namespace Bianchi

/-- **No isotropization for `Λ = 0`** (Kasner). The vacuum Kasner model `H = 1/(3t)`, `σ² = 1/(3t²)`
solves the scalar system with `Λ = 0` from `t₀ = 1` on, is admissible, has `H → 0`, and its shear
ratio `σ²/H²` is the constant `3`. -/
theorem kasner_no_isotropization :
    ∃ H ρ p σ2 R : ℝ → ℝ, IsSolution 0 1 H ρ p σ2 R ∧ IsAdmissible 1 ρ p σ2 R ∧
      Tendsto H atTop (𝓝 0) ∧ ∀ t, 1 ≤ t → σ2 t = 3 * H t ^ 2 ∧ 0 < H t := by
  refine ⟨fun t => (3 * t)⁻¹, fun _ => 0, fun _ => 0, fun t => 1 / (3 * t ^ 2), fun _ => 0,
    ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t ht
    have ht0 : t ≠ 0 := by positivity
    have h : HasDerivAt (fun t : ℝ => (3 * t)⁻¹) (-(3 * 1) / (3 * t) ^ 2) t :=
      ((hasDerivAt_id t).const_mul 3).inv (by simpa using ht0)
    convert h using 1
    field_simp
    ring
  · intro t ht
    have ht0 : t ≠ 0 := by positivity
    field_simp
    ring
  · intro t _; exact le_rfl
  · intro t _; simp
  · intro t ht
    have : 0 < t := by linarith
    positivity
  · intro t _; exact le_rfl
  · have : Tendsto (fun t : ℝ => 3 * t) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
    exact tendsto_inv_atTop_zero.comp this
  · intro t ht
    have ht0 : 0 < t := by linarith
    refine ⟨?_, by positivity⟩
    field_simp

/-- **Large positive curvature recollapses** (`R ≤ 0` cannot be dropped from `rate_ge`). With `Λ = 3`,
`ρ = σ² = 0`, `p = 4`, `H = -tan t` on `[-π/6, π/4]` solves the scalar system with
`R = 6 - 6 tan² t`, `R(-π/6) > 0`; `H(-π/6) > 0` but `H(0) = 0 < √(Λ/3) = 1` and `H(π/4) < 0`. -/
theorem recollapse_example :
    ∃ H ρ p σ2 R : ℝ → ℝ,
      (∀ t ∈ Icc (-(π / 6)) (π / 4),
        HasDerivAt H (-(H t) ^ 2 - 2 / 3 * σ2 t - (ρ t + 3 * p t) / 6 + 3 / 3) t ∧
        3 * (H t) ^ 2 = ρ t + 3 + σ2 t - R t / 2) ∧
      (∀ t, 0 ≤ ρ t ∧ 0 ≤ ρ t + 3 * p t ∧ 0 ≤ σ2 t) ∧
      0 < R (-(π / 6)) ∧ 0 < H (-(π / 6)) ∧ H 0 = 0 ∧ H 0 < deSitterRate 3 ∧ H (π / 4) < 0 := by
  have hcos : ∀ t ∈ Icc (-(π / 6)) (π / 4), Real.cos t ≠ 0 := by
    intro t ht
    apply ne_of_gt
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [ht.1, ht.2, Real.pi_pos]
  have hds : deSitterRate 3 = 1 := by
    unfold deSitterRate; simp
  have htan6 : Real.tan (π / 6) = 1 / Real.sqrt 3 := Real.tan_pi_div_six
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have htan4 : Real.tan (π / 4) = 1 := Real.tan_pi_div_four
  refine ⟨fun t => -Real.tan t, fun _ => 0, fun _ => 4, fun _ => 0, fun t => 6 - 6 * Real.tan t ^ 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, by ring⟩
    have h := (Real.hasDerivAt_tan (hcos t ht)).neg
    convert h using 1
    have hc := hcos t ht
    have : 1 / Real.cos t ^ 2 = 1 + Real.tan t ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [this]; ring
  · intro t; refine ⟨le_rfl, by norm_num, le_rfl⟩
  · show 0 < 6 - 6 * Real.tan (-(π / 6)) ^ 2
    rw [Real.tan_neg, htan6]
    have : (-(1 / Real.sqrt 3)) ^ 2 = 1 / 3 := by
      rw [neg_sq, div_pow, hs3]; simp
    rw [this]
    norm_num
  · show 0 < -Real.tan (-(π / 6))
    rw [Real.tan_neg, htan6]
    simp only [neg_neg]
    positivity
  · simp
  · rw [hds]; simp
  · simp [htan4]

end Bianchi
end Cosmology
end Lightlike
