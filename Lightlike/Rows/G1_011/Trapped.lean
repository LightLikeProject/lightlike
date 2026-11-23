import Lightlike.Rows.G1_011.Expansion

/-!
# Trapped spheres in the Schwarzschild interior (row G1-011)

* `Trapped.bil_sch`: the bilinear form of the Schwarzschild metric is diagonal.
* `Trapped.schwarzschild_interior_trapped`: for `0 < M` and `0 < r₀ < 2M`, every coordinate sphere
  `{t = t₀, r = r₀}` is trapped, for the time orientation `T = -∂ᵣ` (inside the horizon `r` is
  a time function decreasing to the future).
-/

open Matrix Real

noncomputable section

namespace Lightlike
namespace Trapped

variable (M : ℝ)

/-- In Schwarzschild coordinates `g(u, v) = ∑ μ, schD μ · uᵘ vᵘ`. -/
lemma bil_sch (y u v : Fin 4 → ℝ) :
    bil (schMetric M) y u v = ∑ μ, u μ * schD M y μ * v μ := by
  unfold bil
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ]
  · simp [schMetric]
  · intro ν _ hν
    simp [schMetric, Ne.symm hν]
  · simp

/-- **Trapped spheres in the Schwarzschild interior.**  For `0 < M` and `0 < r₀ < 2M`, every
coordinate sphere `{t = t₀, r = r₀}` is trapped for the time orientation `T = -∂ᵣ`: any
future-directed null normal field has negative expansion `θ = 2 k¹ / r₀ < 0`. -/
theorem schwarzschild_interior_trapped {M : ℝ} (t₀ : ℝ) {r₀ : ℝ} (hr : 0 < r₀) (hM : r₀ < 2 * M) :
    IsTrappedSphere (schMetric M) ![0, -1, 0, 0] t₀ r₀ := by
  intro k hk y hy
  have hs := hy
  obtain ⟨h0, h1, h2, h2'⟩ := hs
  have hsin : 0 < sin (y 2) := sin_pos_of_pos_of_lt_pi h2 h2'
  have hf : 1 - 2 * M / r₀ < 0 := by
    rw [sub_neg, one_lt_div hr]; exact hM
  have hfne : 1 - 2 * M / r₀ ≠ 0 := hf.ne
  -- the normal conditions at an arbitrary sphere point
  have key : ∀ z ∈ sphere t₀ r₀, k z 2 = 0 ∧ k z 3 = 0 ∧ k z 1 < 0 := by
    intro z hz
    have hz' := hz
    obtain ⟨z0, z1, z2, z2'⟩ := hz'
    have zs : 0 < sin (z 2) := sin_pos_of_pos_of_lt_pi z2 z2'
    obtain ⟨-, -, hperp, hT⟩ := hk z hz
    have p2 := hperp 0
    have p3 := hperp 1
    simp only [tan, Matrix.cons_val_zero, Matrix.cons_val_one, bil_sch, Fin.sum_univ_four,
      schD] at p2 p3 hT
    simp [z1] at p2 p3 hT
    refine ⟨?_, ?_, ?_⟩
    · rcases p2 with h | h
      · exact h
      · exact absurd h hr.ne'
    · rcases p3 with h | h
      · exact h
      · rcases h with h | h
        · exact absurd h hr.ne'
        · exact absurd h zs.ne'
    · have hinv : (1 - 2 * M / r₀)⁻¹ < 0 := inv_lt_zero.mpr hf
      by_contra hcon
      rw [not_lt] at hcon
      have : 0 ≤ k z 1 * (1 - 2 * M / r₀)⁻¹ * -1 := by nlinarith
      linarith
  rw [nullExpansion_sch M hr (by linarith) (fun z hz => (key z hz).1) (fun z hz => (key z hz).2.1) hy]
  have := (key y hy).2.2
  have : 2 * k y 1 / r₀ < 0 := div_neg_of_neg_of_pos (by linarith) hr
  exact this

end Trapped
end Lightlike
