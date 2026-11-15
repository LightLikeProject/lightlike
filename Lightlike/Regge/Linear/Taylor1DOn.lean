import Mathlib

/-!
# A second-order Taylor bound on `[0, 1]` with derivatives assumed only on the interval

The variant of `taylor2_line` for a function that is differentiable only near `[0, 1]`: the
derivative hypotheses are required at the points of `[0, 1]` (as `HasDerivAt`, so on a neighbourhood
of each point) and not on all of `ℝ`. This is the form needed when the function is a smooth map
restricted to a segment inside an open set.

## Main results

* `taylor2_line_on`: if `G' = G1`, `G1' = G2` on `[0, 1]` and `|G2 t - G2 0| ≤ L t` there, then
  `|G 1 - G 0 - G1 0 - G2 0 / 2| ≤ L / 6`.
-/

open Set

namespace Lightlike.Regge.Linear

/-- If `F 0 = 0` and `|F' t| ≤ c t^m` on `[0, 1]`, then `|F t| ≤ c t^(m+1) / (m+1)` there;
the derivative is only assumed on `[0, 1]`. -/
lemma abs_le_of_deriv_le_on {F F' : ℝ → ℝ} {c : ℝ} {m : ℕ}
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (h0 : F 0 = 0) (hb : ∀ t ∈ Icc (0 : ℝ) 1, |F' t| ≤ c * t ^ m) :
    ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ c * t ^ (m + 1) / (m + 1) := by
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
    have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => c * t ^ (m + 1) / (m + 1) - σ * F t)
        (c * t ^ m - σ * F' t) t := fun t ht => (hP t).sub ((hF t ht).const_mul σ)
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    have := hb t (interior_subset ht)
    rw [abs_le] at this
    rcases hσ with rfl | rfl <;> linarith [this.1, this.2]
  intro t ht
  have m1 := mono 1 (Or.inl rfl) ⟨le_rfl, zero_le_one⟩ ht ht.1
  have m2 := mono (-1) (Or.inr rfl) ⟨le_rfl, zero_le_one⟩ ht ht.1
  simp [h0] at m1 m2
  rw [abs_le]
  constructor <;> linarith

/-- **Second-order Taylor bound on `[0, 1]`**, with the derivatives assumed only there. -/
theorem taylor2_line_on {G G1 G2 : ℝ → ℝ} {L : ℝ}
    (hG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G1 t) t)
    (hG1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G1 (G2 t) t)
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, |G2 t - G2 0| ≤ L * t) :
    |G 1 - G 0 - G1 0 - G2 0 / 2| ≤ L / 6 := by
  have d1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => G1 t - G1 0 - t * G2 0) (G2 t - G2 0) t := by
    intro t ht
    have := (((hG1 t ht).sub_const (G1 0)).sub ((hasDerivAt_id t).mul_const (G2 0)))
    convert this using 1
    · funext x; simp
    · simp
  have s1 := abs_le_of_deriv_le_on (F := fun t => G1 t - G1 0 - t * G2 0)
    (F' := fun t => G2 t - G2 0) (c := L) (m := 1) d1 (by simp)
    (fun t ht => by simpa using hL t ht)
  have d2 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => G t - G 0 - t * G1 0 - t ^ 2 * G2 0 / 2)
      (G1 t - G1 0 - t * G2 0) t := by
    intro t ht
    have h1 := ((hG t ht).sub_const (G 0)).sub ((hasDerivAt_id t).mul_const (G1 0))
    have h2 := ((hasDerivAt_pow 2 t).mul_const (G2 0)).div_const 2
    have := h1.sub h2
    convert this using 1
    · funext x; simp
    · simp; ring
  have s2 := abs_le_of_deriv_le_on (F := fun t => G t - G 0 - t * G1 0 - t ^ 2 * G2 0 / 2)
    (F' := fun t => G1 t - G1 0 - t * G2 0) (c := L / 2) (m := 2) d2 (by simp) (fun t ht => by
        have := s1 t ht
        norm_num at this ⊢
        linarith)
  have := s2 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_mul, mul_one, one_pow] at this
  refine this.trans (le_of_eq ?_)
  norm_num; ring

end Lightlike.Regge.Linear
