import Mathlib

/-!
# The radial system of an angular mode of the sphere Dirac equation

For `ν : ℂ`, an integer `m` and `K r = 1 + r²`, the radial parts `(a, b)` of a mode satisfy
`a' = (m/r) a + (ν/K) b`, `b' = -((m+1)/r) b + (ν/K) a` on `r > 0`.  The Wronskian `a₁ b₂ - a₂ b₁` of two
solutions times `r` is constant, so at most a one-dimensional space of solutions is bounded at `0` and at most a
one-dimensional space decays at infinity.
-/

namespace Lightlike.Dirac

open Set

/-- `(a, b)` solves the radial mode system with parameter `ν` and angular index `m` on `r > 0`. -/
def IsModeSol (ν : ℂ) (m : ℤ) (a b : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0 < r →
    HasDerivAt a (((m : ℂ) / r) * a r + (ν / (1 + (r : ℂ) ^ 2)) * b r) r ∧
    HasDerivAt b (-(((m + 1 : ℤ) : ℂ) / r) * b r + (ν / (1 + (r : ℂ) ^ 2)) * a r) r

/-- **The Wronskian of two mode solutions is `C / r`.** -/
theorem mode_wronskian {ν : ℂ} {m : ℤ} {a₁ b₁ a₂ b₂ : ℝ → ℂ} (h₁ : IsModeSol ν m a₁ b₁)
    (h₂ : IsModeSol ν m a₂ b₂) :
    ∀ r s : ℝ, 0 < r → 0 < s → (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r) = (s : ℂ) * (a₁ s * b₂ s - a₂ s * b₁ s) := by
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt (fun r : ℝ => (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r)) 0 r := by
    intro r hr
    obtain ⟨d1a, d1b⟩ := h₁ r hr
    obtain ⟨d2a, d2b⟩ := h₂ r hr
    have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 r := by simpa using (hasDerivAt_id r).ofReal_comp
    have := hid.mul ((d1a.mul d2b).sub (d2a.mul d1b))
    refine (this : HasDerivAt (fun r : ℝ => (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r)) _ r).congr_deriv ?_
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    simp only [Pi.mul_apply, Pi.sub_apply]
    push_cast
    field_simp
    ring
  intro r s hr hs
  have hconv : Convex ℝ (Ioi (0 : ℝ)) := convex_Ioi 0
  have hdiff : DifferentiableOn ℝ (fun r : ℝ => (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r)) (Ioi 0) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  exact hconv.is_const_of_fderivWithin_eq_zero hdiff
    (fun x hx => by
      rw [fderivWithin_eq_fderiv (isOpen_Ioi.uniqueDiffWithinAt hx) (hd x hx).differentiableAt]
      ext
      simp [(hd x hx).deriv]) hr hs

/-- If `r · W(r) → 0` at `0` (or at `∞`) for two mode solutions, their Wronskian vanishes identically. -/
theorem mode_wronskian_zero {ν : ℂ} {m : ℤ} {a₁ b₁ a₂ b₂ : ℝ → ℂ} (h₁ : IsModeSol ν m a₁ b₁)
    (h₂ : IsModeSol ν m a₂ b₂) {l : Filter ℝ} [l.NeBot] (hl : l ≤ Filter.principal (Ioi 0))
    (ht : Filter.Tendsto (fun r : ℝ => (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r)) l (nhds 0)) :
    ∀ s : ℝ, 0 < s → a₁ s * b₂ s - a₂ s * b₁ s = 0 := by
  intro s hs
  have hconst : Filter.Tendsto (fun r : ℝ => (r : ℂ) * (a₁ r * b₂ r - a₂ r * b₁ r)) l
      (nhds ((s : ℂ) * (a₁ s * b₂ s - a₂ s * b₁ s))) := by
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ r in l, r ∈ Ioi (0 : ℝ) := Filter.le_principal_iff.mp hl
    filter_upwards [this] with r hr
    exact mode_wronskian h₁ h₂ s r hs hr
  have h0 := tendsto_nhds_unique hconst ht
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  exact (mul_eq_zero.mp h0).resolve_left hs'

/-- **At most one bounded solution at the origin**: two mode solutions bounded near `0` have vanishing Wronskian. -/
theorem mode_wronskian_zero_of_bounded {ν : ℂ} {m : ℤ} {a₁ b₁ a₂ b₂ : ℝ → ℂ} (h₁ : IsModeSol ν m a₁ b₁)
    (h₂ : IsModeSol ν m a₂ b₂) {C : ℝ}
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖a₁ r‖ ≤ C ∧ ‖b₁ r‖ ≤ C ∧ ‖a₂ r‖ ≤ C ∧ ‖b₂ r‖ ≤ C) :
    ∀ s : ℝ, 0 < s → a₁ s * b₂ s - a₂ s * b₁ s = 0 := by
  refine mode_wronskian_zero h₁ h₂ (l := nhdsWithin 0 (Ioi 0)) (Filter.le_principal_iff.mpr self_mem_nhdsWithin) ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => norm_nonneg _) ?_
    (g := fun r : ℝ => r * (2 * C ^ 2)) ?_
  · filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
    obtain ⟨c1, c2, c3, c4⟩ := hb r hr.1 hr.2
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
    have h1 : ‖a₁ r * b₂ r - a₂ r * b₁ r‖ ≤ 2 * C ^ 2 := by
      calc _ ≤ ‖a₁ r * b₂ r‖ + ‖a₂ r * b₁ r‖ := norm_sub_le _ _
        _ ≤ C * C + C * C := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul c1 c4 (norm_nonneg _) ((norm_nonneg _).trans c1))
            (mul_le_mul c3 c2 (norm_nonneg _) ((norm_nonneg _).trans c3))
        _ = 2 * C ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left h1 hr.1.le
  · have : Filter.Tendsto (fun r : ℝ => r * (2 * C ^ 2)) (nhdsWithin 0 (Ioi 0)) (nhds (0 * (2 * C ^ 2))) :=
      (continuous_id.mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using this

/-- **At most one solution decaying at infinity**: two mode solutions with `‖·‖ ≤ C / r` for `r ≥ 1` have
vanishing Wronskian. -/
theorem mode_wronskian_zero_of_decay {ν : ℂ} {m : ℤ} {a₁ b₁ a₂ b₂ : ℝ → ℂ} (h₁ : IsModeSol ν m a₁ b₁)
    (h₂ : IsModeSol ν m a₂ b₂) {C : ℝ}
    (hb : ∀ r : ℝ, 1 ≤ r → ‖a₁ r‖ ≤ C / r ∧ ‖b₁ r‖ ≤ C / r ∧ ‖a₂ r‖ ≤ C / r ∧ ‖b₂ r‖ ≤ C / r) :
    ∀ s : ℝ, 0 < s → a₁ s * b₂ s - a₂ s * b₁ s = 0 := by
  refine mode_wronskian_zero h₁ h₂ (l := Filter.atTop) ?_ ?_
  · rw [Filter.le_principal_iff]
    exact Filter.eventually_gt_atTop 0
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun r => norm_nonneg _) ?_
    (g := fun r : ℝ => 2 * C ^ 2 / r) ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with r hr
    obtain ⟨c1, c2, c3, c4⟩ := hb r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have h1 : ‖a₁ r * b₂ r - a₂ r * b₁ r‖ ≤ 2 * C ^ 2 / r ^ 2 := by
      calc _ ≤ ‖a₁ r * b₂ r‖ + ‖a₂ r * b₁ r‖ := norm_sub_le _ _
        _ ≤ C / r * (C / r) + C / r * (C / r) := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul c1 c4 (norm_nonneg _) ((norm_nonneg _).trans c1))
            (mul_le_mul c3 c2 (norm_nonneg _) ((norm_nonneg _).trans c3))
        _ = 2 * C ^ 2 / r ^ 2 := by field_simp; ring
    calc r * ‖a₁ r * b₂ r - a₂ r * b₁ r‖ ≤ r * (2 * C ^ 2 / r ^ 2) := mul_le_mul_of_nonneg_left h1 hr0.le
      _ = 2 * C ^ 2 / r := by field_simp
  · exact tendsto_const_nhds.div_atTop Filter.tendsto_id

end Lightlike.Dirac
