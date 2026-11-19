import Lightlike.OperatorAlgebras.Semigroup.Construct

/-!
# `A` is contained in the generator of the limit semigroup

For `x ∈ dom A` the difference quotient `t⁻¹ (S t x - x)` of the limit semigroup converges to `A x`
as `t → 0⁺`: for the approximating semigroups `‖exp (t Y_n) x - x - t Y_n x‖ ≤ t sup_{r ≤ t}
‖(exp (r Y_n) - 1) Y_n x‖`, and `Y_n x → A x`, `exp (r Y_n) A x → S r (A x)` uniformly on compact
intervals, with `S r (A x) → A x` as `r → 0` (strong continuity).

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, proof of Theorem 1.9
  (the generator contains `A`).
-/

open NormedSpace Filter Topology Set NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} (h : HYHyp A)

/-- For `x ∈ dom A` and `ε > 0` there is `δ > 0` with
`‖(S t x - x) - t A x‖ ≤ 4 ε t` for `0 ≤ t ≤ δ`. -/
lemma HYHyp.norm_S_sub_smul_le (x : A.domain) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      ‖(h.S t (x : X) - x) - ((t : ℝ) : 𝕜) • A x‖ ≤ 4 * ε * (t : ℝ) := by
  -- strong continuity of `S` at `0` for `y = A x`
  have hS := Metric.tendsto_nhds.1 (h.tendsto_S (A x)) ε hε
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.eventually_nhds_iff.1 hS
  refine ⟨δ₀ / 2, by positivity, fun t ht => ?_⟩
  -- uniform convergence of the approximating semigroups applied to `A x`
  obtain ⟨N₁, hN₁⟩ := h.exists_uniform_tendsto (A x) (show 0 ≤ δ₀ / 2 by positivity) hε
  -- convergence of the Yosida approximants at `x`
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (h.tendsto_yos x) ε hε
  have hbound : ∀ n ≥ max N₁ N₂, ‖(h.T n (t : ℝ) (x : X) - x) -
      ((t : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1) (x : X)‖ ≤ 4 * ε * (t : ℝ) := by
    intro n hn
    have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have := norm_exp_sub_smul_le (h.yos ((n : ℝ) + 1)) (x : X) (h.yos ((n : ℝ) + 1) (x : X)) t.2
      (C := 4 * ε) (fun r hr hrt => by
        have hrδ : r ≤ δ₀ / 2 := hrt.trans ht
        have hY : ‖h.yos ((n : ℝ) + 1) (x : X) - A x‖ < ε := by
          have := hN₂ n hn2; rwa [dist_eq_norm] at this
        have hTy : ‖h.T n r (A x) - h.lim r (A x)‖ ≤ ε := hN₁ n hn1 r hr hrδ
        have hSy : ‖h.lim r (A x) - A x‖ < ε := by
          have hs_eq : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr
          have hs : dist (Real.toNNReal r) (0 : ℝ≥0) < δ₀ := by
            rw [NNReal.dist_eq, hs_eq]
            simp only [NNReal.coe_zero, sub_zero]
            rw [abs_of_nonneg hr]
            linarith
          have := hδ hs
          rw [dist_eq_norm, h.S_apply, hs_eq] at this
          exact this
        have e : h.T n r (h.yos ((n : ℝ) + 1) (x : X)) - h.yos ((n : ℝ) + 1) (x : X) =
            h.T n r (h.yos ((n : ℝ) + 1) (x : X) - A x) + (h.T n r (A x) - h.lim r (A x)) +
              (h.lim r (A x) - A x) + (A x - h.yos ((n : ℝ) + 1) (x : X)) := by
          simp only [map_sub]; abel
        simp only [HYHyp.T] at hTy e ⊢
        rw [e]
        have a1 := h.T_apply_norm_le n hr (h.yos ((n : ℝ) + 1) (x : X) - A x)
        simp only [HYHyp.T] at a1
        have a2 : ‖A x - h.yos ((n : ℝ) + 1) (x : X)‖ < ε := by rwa [norm_sub_rev]
        calc _ ≤ ‖exp (((r : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1)) (h.yos ((n : ℝ) + 1) (x : X) - A x)‖ +
              ‖exp (((r : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1)) (A x) - h.lim r (A x)‖ +
              ‖h.lim r (A x) - A x‖ + ‖A x - h.yos ((n : ℝ) + 1) (x : X)‖ := by
              refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
                (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
          _ ≤ 4 * ε := by linarith)
    simpa [HYHyp.T] using this
  -- pass to the limit
  have hl1 : Tendsto (fun n : ℕ => ‖(h.T n (t : ℝ) (x : X) - x) -
      ((t : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1) (x : X)‖) atTop
      (𝓝 ‖(h.lim (t : ℝ) (x : X) - x) - ((t : ℝ) : 𝕜) • A x‖) :=
    (((h.tendsto_lim (x : X) t.2).sub_const _).sub ((h.tendsto_yos x).const_smul _)).norm
  have := le_of_tendsto hl1 (eventually_atTop.2 ⟨max N₁ N₂, hbound⟩)
  simpa [HYHyp.S_apply] using this

end Lightlike.OperatorAlgebras
