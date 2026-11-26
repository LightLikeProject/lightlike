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

/-- The right-hand side of the mode system as a map `ℂ × ℂ → ℂ × ℂ`. -/
noncomputable def modeField (ν : ℂ) (m : ℤ) (r : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (((m : ℂ) / r) * z.1 + (ν / (1 + (r : ℂ) ^ 2)) * z.2,
    -(((m + 1 : ℤ) : ℂ) / r) * z.2 + (ν / (1 + (r : ℂ) ^ 2)) * z.1)

/-- **A mode solution vanishing at one point vanishes identically** (uniqueness for the linear system). -/
theorem mode_sol_zero {ν : ℂ} {m : ℤ} {a b : ℝ → ℂ} (h : IsModeSol ν m a b) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (ha : a r₀ = 0) (hb : b r₀ = 0) : ∀ r : ℝ, 0 < r → a r = 0 ∧ b r = 0 := by
  intro r hr
  set ε : ℝ := min r r₀ / 2 with hε
  set R : ℝ := max r r₀ + 1 with hR
  have hε0 : 0 < ε := by have := lt_min hr hr₀; rw [hε]; linarith
  have hεr : ε < r := by have := min_le_left r r₀; rw [hε]; linarith
  have hεr₀ : ε < r₀ := by have := min_le_right r r₀; rw [hε]; linarith
  have hrR : r < R := by have := le_max_left r r₀; rw [hR]; linarith
  have hr₀R : r₀ < R := by have := le_max_right r r₀; rw [hR]; linarith
  -- Lipschitz constant
  set Kc : ℝ := (|(m : ℝ)| + 1) / ε + ‖ν‖ with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hlip : ∀ t ∈ Set.Ioo ε R, LipschitzOnWith (Real.toNNReal Kc) (modeField ν m t) Set.univ := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε0 ht.1
    have hK1 : ‖ν / (1 + (t : ℂ) ^ 2)‖ ≤ ‖ν‖ := by
      rw [norm_div]
      have : (1 : ℝ) ≤ ‖1 + (t : ℂ) ^ 2‖ := by
        have : ‖1 + (t : ℂ) ^ 2‖ = 1 + t ^ 2 := by
          have : (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [this]; nlinarith [sq_nonneg t]
      exact div_le_self (norm_nonneg _) this
    have hm1 : ‖((m : ℂ) / t)‖ ≤ (|(m : ℝ)| + 1) / ε := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      have : ‖(m : ℂ)‖ = |(m : ℝ)| := by simp
      rw [this]
      calc |(m : ℝ)| / t ≤ |(m : ℝ)| / ε := div_le_div_of_nonneg_left (abs_nonneg _) hε0 ht.1.le
        _ ≤ (|(m : ℝ)| + 1) / ε := by gcongr; linarith
    have hm2 : ‖(((m + 1 : ℤ) : ℂ) / t)‖ ≤ (|(m : ℝ)| + 1) / ε := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      have : ‖(((m + 1 : ℤ) : ℂ))‖ ≤ |(m : ℝ)| + 1 := by
        have : (((m + 1 : ℤ) : ℂ)) = (((m + 1 : ℤ) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs]
        push_cast
        calc |(m : ℝ) + 1| ≤ |(m : ℝ)| + |(1 : ℝ)| := abs_add_le _ _
          _ = |(m : ℝ)| + 1 := by simp
      calc ‖(((m + 1 : ℤ) : ℂ))‖ / t ≤ (|(m : ℝ)| + 1) / t := by gcongr
        _ ≤ (|(m : ℝ)| + 1) / ε := div_le_div_of_nonneg_left (by positivity) hε0 ht.1.le
    refine (LipschitzWith.of_dist_le_mul fun z w => ?_).lipschitzOnWith
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, modeField]
    have hz1 : ‖z.1 - w.1‖ ≤ max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := le_max_left _ _
    have hz2 : ‖z.2 - w.2‖ ≤ max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := le_max_right _ _
    have hD : 0 ≤ max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := le_trans (norm_nonneg _) hz1
    have hKn : (Real.toNNReal Kc : ℝ) = Kc := Real.coe_toNNReal _ hKc0
    rw [hKn]
    refine max_le ?_ ?_
    · have e : ((m : ℂ) / t * z.1 + ν / (1 + (t : ℂ) ^ 2) * z.2) - ((m : ℂ) / t * w.1 + ν / (1 + (t : ℂ) ^ 2) * w.2) =
          ((m : ℂ) / t) * (z.1 - w.1) + (ν / (1 + (t : ℂ) ^ 2)) * (z.2 - w.2) := by ring
      rw [e]
      calc _ ≤ ‖((m : ℂ) / t) * (z.1 - w.1)‖ + ‖(ν / (1 + (t : ℂ) ^ 2)) * (z.2 - w.2)‖ := norm_add_le _ _
        _ ≤ (|(m : ℝ)| + 1) / ε * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ + ‖ν‖ * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := by
          rw [norm_mul, norm_mul]
          exact add_le_add (mul_le_mul hm1 hz1 (norm_nonneg _) (by positivity))
            (mul_le_mul hK1 hz2 (norm_nonneg _) (norm_nonneg _))
        _ = Kc * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := by rw [hKc]; ring
    · have e : (-(((m + 1 : ℤ) : ℂ) / t) * z.2 + ν / (1 + (t : ℂ) ^ 2) * z.1) -
          (-(((m + 1 : ℤ) : ℂ) / t) * w.2 + ν / (1 + (t : ℂ) ^ 2) * w.1) =
          (-(((m + 1 : ℤ) : ℂ) / t)) * (z.2 - w.2) + (ν / (1 + (t : ℂ) ^ 2)) * (z.1 - w.1) := by ring
      rw [e]
      calc _ ≤ ‖(-(((m + 1 : ℤ) : ℂ) / t)) * (z.2 - w.2)‖ + ‖(ν / (1 + (t : ℂ) ^ 2)) * (z.1 - w.1)‖ := norm_add_le _ _
        _ ≤ (|(m : ℝ)| + 1) / ε * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ + ‖ν‖ * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := by
          rw [norm_mul, norm_mul, norm_neg]
          exact add_le_add (mul_le_mul hm2 hz2 (norm_nonneg _) (by positivity))
            (mul_le_mul hK1 hz1 (norm_nonneg _) (norm_nonneg _))
        _ = Kc * max ‖z.1 - w.1‖ ‖z.2 - w.2‖ := by rw [hKc]; ring
  have hf : ∀ t ∈ Set.Ioo ε R, HasDerivAt (fun t => (a t, b t)) (modeField ν m t (a t, b t)) t ∧
      (a t, b t) ∈ (Set.univ : Set (ℂ × ℂ)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε0 ht.1
    exact ⟨(h t ht0).1.prodMk (h t ht0).2, Set.mem_univ _⟩
  have hg : ∀ t ∈ Set.Ioo ε R, HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) (modeField ν m t ((0 : ℂ), (0 : ℂ))) t ∧
      ((0 : ℂ), (0 : ℂ)) ∈ (Set.univ : Set (ℂ × ℂ)) := by
    intro t ht
    refine ⟨?_, Set.mem_univ _⟩
    have : modeField ν m t ((0 : ℂ), (0 : ℂ)) = 0 := by simp [modeField]
    rw [this]
    exact (hasDerivAt_const t ((0 : ℂ), (0 : ℂ)))
  have := ODE_solution_unique_of_mem_Ioo (f := fun t => (a t, b t)) (g := fun _ => ((0 : ℂ), (0 : ℂ)))
    (v := modeField ν m) (s := fun _ => Set.univ) hlip ⟨hεr₀, hr₀R⟩ hf hg (by simp [ha, hb])
  have := this ⟨hεr, hrR⟩
  simp only [Prod.mk.injEq] at this
  exact this

/-- Scalar multiples of mode solutions are mode solutions. -/
theorem IsModeSol.smul {ν : ℂ} {m : ℤ} {a b : ℝ → ℂ} (h : IsModeSol ν m a b) (c : ℂ) :
    IsModeSol ν m (fun r => c * a r) (fun r => c * b r) := by
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  refine ⟨(h1.const_mul c).congr_deriv ?_, (h2.const_mul c).congr_deriv ?_⟩ <;> ring

/-- Differences of mode solutions are mode solutions. -/
theorem IsModeSol.sub {ν : ℂ} {m : ℤ} {a b a' b' : ℝ → ℂ} (h : IsModeSol ν m a b) (h' : IsModeSol ν m a' b') :
    IsModeSol ν m (fun r => a r - a' r) (fun r => b r - b' r) := by
  intro r hr
  obtain ⟨h1, h2⟩ := h r hr
  obtain ⟨h1', h2'⟩ := h' r hr
  refine ⟨(h1.sub h1').congr_deriv ?_, (h2.sub h2').congr_deriv ?_⟩ <;> ring

end Lightlike.Dirac
