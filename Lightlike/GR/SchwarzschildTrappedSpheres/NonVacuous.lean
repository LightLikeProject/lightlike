import Lightlike.GR.SchwarzschildTrappedSpheres.Trapped

/-!
# Non-vacuity of `IsTrappedSphere` in the Schwarzschild interior (row G1-011)

`Trapped.interior_nullNormal_exists`: for `0 < r₀ < 2M` there is a (constant) vector field
`k = (1/f, -1, 0, 0)`, `f = 1 - 2M/r₀`, that is a future-directed null normal along the sphere,
so the hypothesis of `IsTrappedSphere` is satisfiable and `schwarzschild_interior_trapped` is not
vacuous.
-/

open Matrix Real

noncomputable section

namespace Lightlike
namespace Trapped

/-- In the Schwarzschild interior the constant field `k = (1/f, -1, 0, 0)` is a future-directed null
normal of every coordinate sphere `{t = t₀, r = r₀}` (for `T = -∂ᵣ`). -/
lemma interior_nullNormal_exists {M : ℝ} (t₀ : ℝ) {r₀ : ℝ} (hr : 0 < r₀) (hM : r₀ < 2 * M) :
    ∃ k : (Fin 4 → ℝ) → Fin 4 → ℝ, ∀ y ∈ sphere t₀ r₀,
      IsFutureNullNormal (schMetric M) ![0, -1, 0, 0] (k y) y := by
  have hf : 1 - 2 * M / r₀ < 0 := by
    rw [sub_neg, one_lt_div hr]; exact hM
  have hfne : 1 - 2 * M / r₀ ≠ 0 := hf.ne
  refine ⟨fun _ => ![(1 - 2 * M / r₀)⁻¹, -1, 0, 0], ?_⟩
  intro y hy
  obtain ⟨h0, h1, h2, h2'⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 1
    simp at this
  · simp only [bil_sch, Fin.sum_univ_four, schD, h1]
    simp
    field_simp
    ring
  · intro A
    fin_cases A <;>
      simp [bil_sch, tan, Pi.single_apply, schD]
  · simp only [bil_sch, Fin.sum_univ_four, schD, h1]
    simp
    linarith

end Trapped
end Lightlike
