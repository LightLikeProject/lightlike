import Lightlike.Cosmology.QuintessenceFixedPoints.Fixed

/-!
# Quintessence with an exponential potential: the list of fixed points is complete

Row G1-029 (milestone CO17).  `Fixed.lean` shows that the matter point, the two kinetic points, the
scalar-field-dominated point and the scaling point are zeros of the vector field `(vfx, vfy)`.  Here we
show that there are no others (outside the degenerate parameter values `γ = 2`, and `μ = γ = 0`, where
a whole line of zeros occurs).

## Main statements

* `vf_zero_classify`: a zero of the vector field is one of the five points, stated with `μ = (√6/2) λ`.
* `vf_zero_classify_half_disc`: the same for `y ≥ 0`, with `λ` and the named points
  `sfPoint`, `scPoint`.

## References

* copeland-2006
-/

namespace Lightlike.Rows.G1_029

noncomputable section

/-- **Completeness of the fixed points (algebraic form).**  If `γ ≠ 2` and `(μ, γ) ≠ (0, 0)`, every zero
of `(vfx, vfy)` is the origin, a kinetic point `(±1, 0)`, a point `(μ/3, y)` with `y² = 1 - μ²/9`, or a
point `(3γ/(2μ), y)` with `y² = 9γ(2-γ)/(4μ²)` and `μ ≠ 0`. -/
theorem vf_zero_classify {μ γ x y : ℝ} (hγ : γ ≠ 2) (hμγ : μ ≠ 0 ∨ γ ≠ 0)
    (h1 : vfx μ γ x y = 0) (h2 : vfy μ γ x y = 0) :
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨
      (x = μ / 3 ∧ y ^ 2 = 1 - μ ^ 2 / 9) ∨
      (μ ≠ 0 ∧ x = 3 * γ / (2 * μ) ∧ y ^ 2 = 9 * γ * (2 - γ) / (4 * μ ^ 2)) := by
  by_cases hy0 : y = 0
  · subst hy0
    have h : x * (1 - x) * (1 + x) * (3 / 2 * (γ - 2)) = 0 := by
      unfold vfx aux at h1; linear_combination h1
    have hγ' : (3 / 2 * (γ - 2)) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.2 hγ)
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr (Or.inl ⟨by linarith, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, rfl⟩))
    · exact absurd h hγ'
  · rw [vfy_eq] at h2
    have hb : -μ * x + 3 / 2 * (2 * x ^ 2 + γ * (1 - x ^ 2 - y ^ 2)) = 0 :=
      (mul_eq_zero.1 h2).resolve_left hy0
    have hc : μ * (x ^ 2 + y ^ 2) = 3 * x := by
      unfold vfx aux at h1
      linear_combination h1 - x * hb
    by_cases hμ : μ = 0
    · subst hμ
      have hγ0 : γ ≠ 0 := hμγ.resolve_left (by simp)
      have hx : x = 0 := by linarith
      subst hx
      have : γ * (1 - y ^ 2) = 0 := by linear_combination (2 / 3 : ℝ) * hb
      have := (mul_eq_zero.1 this).resolve_left hγ0
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by linarith⟩)))
    · have hq : (x - μ / 3) * (6 * μ * x - 9 * γ) = 0 := by
        linear_combination 2 * μ * hb + 3 * γ * hc
      rcases mul_eq_zero.1 hq with h | h
      · have hx : x = μ / 3 := by linarith
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, ?_⟩)))
        apply mul_left_cancel₀ hμ
        rw [hx] at hc
        linear_combination hc
      · have hx : x = 3 * γ / (2 * μ) := by
          field_simp
          linarith
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hμ, hx, ?_⟩)))
        rw [eq_div_iff (by positivity)]
        linear_combination (4 * μ) * hc + ((6 - 2 * μ * x - 3 * γ) / 3) * h

/-- **Completeness of the fixed points, in the half disc** (`y ≥ 0`), in terms of `λ` (`μ = c32 * λ`):
for `γ ≠ 2` and `(λ, γ) ≠ (0, 0)`, every zero of the vector field with `y ≥ 0` is the origin, a kinetic
point, `sfPoint λ`, or (for `λ ≠ 0`) `scPoint λ γ`. -/
theorem vf_zero_classify_half_disc {l γ x y : ℝ} (hγ : γ ≠ 2) (hlγ : l ≠ 0 ∨ γ ≠ 0) (hy : 0 ≤ y)
    (h1 : vfx (c32 * l) γ x y = 0) (h2 : vfy (c32 * l) γ x y = 0) :
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x, y) = sfPoint l ∨
      (l ≠ 0 ∧ (x, y) = scPoint l γ) := by
  have hc : c32 ≠ 0 := c32_pos.ne'
  have hμγ : c32 * l ≠ 0 ∨ γ ≠ 0 := by
    rcases hlγ with h | h
    · exact Or.inl (mul_ne_zero hc h)
    · exact Or.inr h
  rcases vf_zero_classify hγ hμγ h1 h2 with h | h | h | ⟨hx, hy2⟩ | ⟨hl, hx, hy2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    unfold sfPoint
    rw [hx, ← hy2, Real.sqrt_sq hy]
  · have hl' : l ≠ 0 := fun h => hl (by simp [h])
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hl', ?_⟩)))
    have hx' : x = c32 * γ / l := by
      rw [hx]
      have := c32_sq
      field_simp
      linear_combination (-2 * γ) * this
    have hy' : y ^ 2 = 3 * (2 - γ) * γ / (2 * l ^ 2) := by
      rw [hy2]
      have := c32_sq
      field_simp
      linear_combination (-12 * γ) * this
    unfold scPoint
    rw [hx', ← hy', Real.sqrt_sq hy]

end

end Lightlike.Rows.G1_029
