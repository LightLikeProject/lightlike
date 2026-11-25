import Lightlike.GR.SchwarzschildTrappedSpheres.Trapped

/-!
# Minkowski space has no trapped sphere (row G1-011, trust check)

`schMetric 0` is Minkowski space in spherical coordinates. The outgoing null normal `k = ∂ₜ + ∂ᵣ` has expansion
`2 / r₀ > 0`, so no coordinate sphere is trapped, for the time orientation `T = -∂ᵣ` used in the interior (and
the same field works for any `T` with `g(k, T) < 0`).
-/

open Matrix Real

noncomputable section

namespace Lightlike
namespace Trapped

/-- **Minkowski space has no trapped sphere**: for `r₀ > 0` the coordinate sphere `{t = t₀, r = r₀}` of Minkowski
space (`schMetric 0`) is not trapped, for `T = -∂ᵣ`. -/
theorem minkowski_not_trapped (t₀ : ℝ) {r₀ : ℝ} (hr : 0 < r₀) :
    ¬ IsTrappedSphere (schMetric 0) ![0, -1, 0, 0] t₀ r₀ := by
  intro h
  set k : (Fin 4 → ℝ) → Fin 4 → ℝ := fun _ => ![1, 1, 0, 0] with hk
  have hn : ∀ y ∈ sphere t₀ r₀, IsFutureNullNormal (schMetric 0) ![0, -1, 0, 0] (k y) y := by
    intro y hy
    obtain ⟨h0, h1, h2, h2'⟩ := hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0'
      have := congrFun h0' 0
      simp [hk] at this
    · simp [hk, bil_sch, Fin.sum_univ_four, schD, h1]
    · intro A
      fin_cases A <;> simp [hk, bil_sch, Fin.sum_univ_four, schD, tan]
    · simp [hk, bil_sch, Fin.sum_univ_four, schD, h1]
  have hy : ((![t₀, r₀, π / 2, 0] : Fin 4 → ℝ)) ∈ sphere t₀ r₀ :=
    ⟨by simp, by simp, by simp [pi_pos], by simp [pi_pos]⟩
  have := h k hn _ hy
  rw [nullExpansion_sch 0 hr (by linarith) (fun _ _ => rfl) (fun _ _ => rfl) hy] at this
  have h1 : (0 : ℝ) < 2 * k (![t₀, r₀, π / 2, 0]) 1 / r₀ := by
    simp [hk]; positivity
  linarith

end Trapped
end Lightlike
