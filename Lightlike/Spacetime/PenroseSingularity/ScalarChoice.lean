import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constants of the broken variation (G1-012, step D4)

With `A > 0` (the squared length of the covariant derivative of the Jacobi field at the focal point), `K` the index
form of the cutoff field and `L > 0` the length of the null geodesic, there are `ε, κ, μ > 0` with
`-2 ε A + ε² K + 2 κ L + 2 μ = 0`: the index form of the broken field is negative with room to spare.
-/

open Set

namespace Lightlike.Penrose

/-- **Choice of `ε`, `κ`, `μ`.** -/
theorem exists_constants {A K L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    ∃ ε κ μ : ℝ, 0 < ε ∧ 0 < κ ∧ 0 < μ ∧ -2 * ε * A + ε ^ 2 * K + 2 * κ * L + 2 * μ = 0 := by
  set ε : ℝ := A / (2 * (|K| + 1)) with hε
  have hK : 0 < |K| + 1 := by positivity
  have hεpos : 0 < ε := by positivity
  have hKε : ε ^ 2 * K ≤ ε * A / 2 := by
    have h1 : ε * |K| ≤ A / 2 := by
      have : ε * (|K| + 1) = A / 2 := by rw [hε]; field_simp
      nlinarith
    calc ε ^ 2 * K ≤ ε ^ 2 * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) (sq_nonneg ε)
      _ = ε * (ε * |K|) := by ring
      _ ≤ ε * (A / 2) := mul_le_mul_of_nonneg_left h1 hεpos.le
      _ = ε * A / 2 := by ring
  set N : ℝ := -2 * ε * A + ε ^ 2 * K with hN
  have hNneg : N < 0 := by
    have : 0 < ε * A := by positivity
    linarith
  -- `κ = -N / (4 L)`, `μ = -N / 4`
  refine ⟨ε, -N / (4 * L), -N / 4, hεpos, ?_, ?_, ?_⟩
  · have : 0 < -N := by linarith
    positivity
  · linarith
  · field_simp
    ring

end Lightlike.Penrose
