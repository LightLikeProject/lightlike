import Lightlike.Rows.G1_011.NonVacuous

/-!
# Test for row G1-011: the sphere `r = 1` in Schwarzschild with `M = 1` is trapped, and the
hypothesis of the definition is satisfiable.
-/

open Lightlike Lightlike.Trapped

example (t₀ : ℝ) : IsTrappedSphere (schMetric 1) ![0, -1, 0, 0] t₀ 1 :=
  schwarzschild_interior_trapped t₀ one_pos (by norm_num)

example (t₀ : ℝ) :
    ∃ k : (Fin 4 → ℝ) → Fin 4 → ℝ, ∀ y ∈ sphere t₀ 1,
      IsFutureNullNormal (schMetric 1) ![0, -1, 0, 0] (k y) y :=
  interior_nullNormal_exists t₀ one_pos (by norm_num)

/-- Combined: in the interior there exist null normals and all of them have `θ < 0`. -/
example (t₀ : ℝ) :
    ∃ k : (Fin 4 → ℝ) → Fin 4 → ℝ,
      (∀ y ∈ sphere t₀ 1, IsFutureNullNormal (schMetric 1) ![0, -1, 0, 0] (k y) y) ∧
      ∀ y ∈ sphere t₀ 1, nullExpansion (schMetric 1) k y < 0 := by
  obtain ⟨k, hk⟩ := interior_nullNormal_exists (M := 1) t₀ one_pos (by norm_num)
  exact ⟨k, hk, schwarzschild_interior_trapped t₀ one_pos (by norm_num) k hk⟩
