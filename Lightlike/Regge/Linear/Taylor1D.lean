import Mathlib

/-!
# A second-order Taylor bound on `[0, 1]` for a function with a Lipschitz second derivative

`taylor2_line`: if `G' = G1`, `G1' = G2` and `|G2 t - G2 0| ≤ L t` on `[0, 1]`, then
`|G 1 - G 0 - G1 0 - G2 0 / 2| ≤ L / 6`. Proved by two applications of a monotonicity argument,
without iterated derivatives.
-/

open Set

namespace Lightlike.Regge.Linear

/-- If `F 0 = 0` and `|F' t| ≤ c t^m` on `[0, 1]`, then `|F t| ≤ c t^(m+1) / (m+1)` there. -/
lemma abs_le_of_deriv_le {F F' : ℝ → ℝ} {c : ℝ} {m : ℕ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (h0 : F 0 = 0) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |F' t| ≤ c * t ^ m) :
    ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ c * t ^ (m + 1) / (m + 1) := by
  have hc : 0 ≤ c := by
    have := hb 1 ⟨zero_le_one, le_rfl⟩
    simp at this
    exact (abs_nonneg _).trans this
  have hP : ∀ t : ℝ, HasDerivAt (fun t : ℝ => c * t ^ (m + 1) / (m + 1)) (c * t ^ m) t := by
    intro t
    have := ((hasDerivAt_pow (m + 1) t).const_mul c).div_const ((m : ℝ) + 1)
    convert this using 1
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have mono : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → MonotoneOn
      (fun t => c * t ^ (m + 1) / (m + 1) - σ * F t) (Icc (0 : ℝ) 1) := by
    intro σ hσ
    have hd : ∀ t, HasDerivAt (fun t => c * t ^ (m + 1) / (m + 1) - σ * F t)
        (c * t ^ m - σ * F' t) t := fun t => (hP t).sub ((hF t).const_mul σ)
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t _ => (hd t).continuousAt.continuousWithinAt) (fun t _ => (hd t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hd t).deriv]
    have := hb t (interior_subset ht)
    rw [abs_le] at this
    rcases hσ with rfl | rfl <;> linarith [this.1, this.2]
  intro t ht
  have m1 := mono 1 (Or.inl rfl) ⟨le_rfl, zero_le_one⟩ ht ht.1
  have m2 := mono (-1) (Or.inr rfl) ⟨le_rfl, zero_le_one⟩ ht ht.1
  simp [h0] at m1 m2
  rw [abs_le]
  constructor <;> linarith

/-- **Second-order Taylor bound on `[0, 1]`.** -/
theorem taylor2_line {G G1 G2 : ℝ → ℝ} {L : ℝ} (hG : ∀ t, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t, HasDerivAt G1 (G2 t) t) (hL : ∀ t ∈ Icc (0 : ℝ) 1, |G2 t - G2 0| ≤ L * t) :
    |G 1 - G 0 - G1 0 - G2 0 / 2| ≤ L / 6 := by
  have d1 : ∀ t, HasDerivAt (fun t => G1 t - G1 0 - t * G2 0) (G2 t - G2 0) t := by
    intro t
    have := ((hG1 t).sub_const (G1 0)).sub ((hasDerivAt_id t).mul_const (G2 0))
    convert this using 1
    · funext x; simp
    · simp
  have s1 := abs_le_of_deriv_le (F := fun t => G1 t - G1 0 - t * G2 0) (F' := fun t => G2 t - G2 0)
    (c := L) (m := 1) d1 (by simp) (fun t ht => by simpa using hL t ht)
  have d2 : ∀ t, HasDerivAt (fun t => G t - G 0 - t * G1 0 - t ^ 2 * G2 0 / 2)
      (G1 t - G1 0 - t * G2 0) t := by
    intro t
    have h1 := ((hG t).sub_const (G 0)).sub ((hasDerivAt_id t).mul_const (G1 0))
    have h2 := ((hasDerivAt_pow 2 t).mul_const (G2 0)).div_const 2
    have := h1.sub h2
    convert this using 1
    · funext x; simp
    · simp; ring
  have s2 := abs_le_of_deriv_le (F := fun t => G t - G 0 - t * G1 0 - t ^ 2 * G2 0 / 2)
    (F' := fun t => G1 t - G1 0 - t * G2 0) (c := L / 2) (m := 2) d2 (by simp) (fun t ht => by
        have := s1 t ht
        norm_num at this ⊢
        linarith)
  have := s2 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_mul, mul_one, one_pow] at this
  refine this.trans (le_of_eq ?_)
  norm_num; ring

end Lightlike.Regge.Linear
