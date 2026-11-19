import Lightlike.Cosmology.BigBang

/-!
# The big bang singularity is at `a = 0` (G1-025)

For a scale factor `a > 0` on `(t₁, t₂)` solving both Friedmann equations with `Λ = 0`, with the strong energy condition
`ρ + 3p ≥ 0` and `p ≤ ρ`, and expanding at `t₀` (`a'(t₀) > 0`): **either `a → 0` as `t ↓ t₁`, or `a'`, `a''`, `ρ` and `p`
stay bounded on `(t₁, t₀]`** (`bigBang_singularity`), so a singularity at the left end of the interval (an unbounded
expansion rate, acceleration, density or pressure) is at `a = 0`. The key is `(ρ a⁶)' = 3 a⁵ a' (ρ - p) ≥ 0`, in the form
`((a'² + k) a⁴)' = 2 a' a³ (a a'' + 2 (a'² + k)) = 8πG a' a⁵ (ρ - p)`: Carroll's (8.34) (gr-qc/9712019),
`a''/a + 2(a'/a)² + 2k/a² = 4πG(ρ - p)`, combines (8.35) and (8.36).

The hypothesis `p ≤ ρ` is needed: `onePlusSqrt_friedmann` (`a = 1 + √t` on `(0, ∞)`, `k = 0`) has `ρ > 0`, `p > 0`, `a' > 0`,
`a'' < 0`, solves both Friedmann equations, and `a' → ∞` as `t ↓ 0` while `a → 1` (the density diverges, `p/ρ → ∞`).
-/

open Set Filter Topology

namespace Lightlike
namespace Cosmology

variable {a ρ p : ℝ → ℝ} {Gn t₁ t₂ t₀ : ℝ}

/-- Friedmann's equations in the form of Carroll's (8.34): `a a'' + 2(a'² + k) = 4πG a² (ρ - p)`. -/
theorem friedmann_834 {k : ℝ} {t : ℝ} (hat : 0 < a t) (h1 : FirstFriedmann a ρ k 0 Gn t)
    (h2 : SecondFriedmann a ρ p 0 Gn t) :
    a t * deriv (deriv a) t + 2 * (deriv a t ^ 2 + k) = 4 * Real.pi * Gn * a t ^ 2 * (ρ t - p t) := by
  unfold FirstFriedmann at h1
  unfold SecondFriedmann at h2
  have ha : a t ≠ 0 := hat.ne'
  rw [div_pow] at h1
  field_simp at h1 h2
  nlinarith [h1, h2]

/-- **The big bang singularity is at `a = 0`.** -/
theorem bigBang_singularity {k : ℝ} (hG : 0 < Gn) (hC : ContDiffOn ℝ 2 a (Ioo t₁ t₂))
    (hpos : ∀ t ∈ Ioo t₁ t₂, 0 < a t) (hF1 : ∀ t ∈ Ioo t₁ t₂, FirstFriedmann a ρ k 0 Gn t)
    (hF2 : ∀ t ∈ Ioo t₁ t₂, SecondFriedmann a ρ p 0 Gn t) (hS : ∀ t ∈ Ioo t₁ t₂, 0 ≤ ρ t + 3 * p t)
    (hD : ∀ t ∈ Ioo t₁ t₂, p t ≤ ρ t) (ht₀ : t₀ ∈ Ioo t₁ t₂) (hH : 0 < deriv a t₀) :
    Tendsto a (𝓝[>] t₁) (𝓝 0) ∨
      ∃ M, ∀ t ∈ Ioc t₁ t₀, |deriv a t| ≤ M ∧ |deriv (deriv a) t| ≤ M ∧ |ρ t| ≤ M ∧ |p t| ≤ M := by
  have hdd := deriv2_nonpos_of_strong_energy hG hpos hF2 hS
  have hsub : Ioc t₁ t₀ ⊆ Ioo t₁ t₂ := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 ht₀.2⟩
  have hd1 : ContDiffOn ℝ 1 (deriv a) (Ioo t₁ t₂) := hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hda : ∀ t ∈ Ioo t₁ t₂, HasDerivAt a (deriv a t) t := fun t ht =>
    (((hC.differentiableOn (by norm_num)) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have hdda : ∀ t ∈ Ioo t₁ t₂, HasDerivAt (deriv a) (deriv (deriv a) t) t := fun t ht =>
    (((hd1.differentiableOn (by norm_num)) t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  -- `a' ≥ a'(t₀) > 0` on `(t₁, t₀]`, so `a` is increasing there
  have hge : ∀ t ∈ Ioc t₁ t₀, deriv a t₀ ≤ deriv a t := fun t ht =>
    deriv_ge_of_strong_energy hC hdd (hsub ht) ht₀ ht.2
  have hmono : MonotoneOn a (Ioc t₁ t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc t₁ t₀) ?_ ?_ ?_
    · exact fun t ht => (hda t (hsub ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (hda t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hda t (hsub (interior_subset ht))).deriv]
      linarith [hge t (interior_subset ht)]
  -- `Q = (a'² + k) a⁴` is nondecreasing on `(t₁, t₀]`
  set Q : ℝ → ℝ := fun t => (deriv a t ^ 2 + k) * a t ^ 4 with hQ
  have hQd : ∀ t ∈ Ioo t₁ t₂, HasDerivAt Q
      ((2 * deriv a t * deriv (deriv a) t) * a t ^ 4 + (deriv a t ^ 2 + k) * (4 * a t ^ 3 * deriv a t)) t := by
    intro t ht
    have h1 := ((hdda t ht).pow 2).add_const k
    have h2 := (hda t ht).pow 4
    have := h1.mul h2
    convert this using 1
    simp
  have hQmono : MonotoneOn Q (Ioc t₁ t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc t₁ t₀) ?_ ?_ ?_
    · exact fun t ht => (hQd t (hsub ht)).continuousAt.continuousWithinAt
    · exact fun t ht => (hQd t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hQd t (hsub ht')).deriv]
      have h834 := friedmann_834 (hpos t (hsub ht')) (hF1 t (hsub ht')) (hF2 t (hsub ht'))
      have hat := hpos t (hsub ht')
      have hdt : 0 < deriv a t := lt_of_lt_of_le hH (hge t ht')
      have hρp := hD t (hsub ht')
      have : (2 * deriv a t * deriv (deriv a) t) * a t ^ 4 + (deriv a t ^ 2 + k) * (4 * a t ^ 3 * deriv a t) =
          2 * deriv a t * a t ^ 3 * (a t * deriv (deriv a) t + 2 * (deriv a t ^ 2 + k)) := by ring
      rw [this, h834]
      have : 0 ≤ 4 * Real.pi * Gn * a t ^ 2 * (ρ t - p t) := by
        have : 0 ≤ ρ t - p t := by linarith
        positivity
      positivity
  -- the dichotomy
  by_cases hL : ∀ ε > 0, ∃ t ∈ Ioc t₁ t₀, a t < ε
  · left
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨s, hs, has⟩ := hL ε hε
    refine ⟨s - t₁, by linarith [hs.1], fun t ht htd => ?_⟩
    rw [Real.dist_eq] at htd ⊢
    have ht1 : t₁ < t := ht
    have hts : t < s := by rw [abs_lt] at htd; linarith
    have htI : t ∈ Ioc t₁ t₀ := ⟨ht1, by linarith [hs.2]⟩
    have := hmono htI hs hts.le
    have hat := hpos t (hsub htI)
    rw [sub_zero, abs_of_pos hat]
    linarith
  · right
    push Not at hL
    obtain ⟨L, hL0, hLa⟩ := hL
    have ht₀I : t₀ ∈ Ioc t₁ t₀ := ⟨ht₀.1, le_rfl⟩
    have hp8 : 0 < 8 * Real.pi * Gn / 3 := by positivity
    set C := Q t₀
    have hQle : ∀ t ∈ Ioc t₁ t₀, Q t ≤ C := fun t ht => hQmono ht ht₀I ht.2
    have hρeq : ∀ t ∈ Ioo t₁ t₂, ρ t * a t ^ 2 = (deriv a t ^ 2 + k) / (8 * Real.pi * Gn / 3) := by
      intro t ht
      have h := hF1 t ht
      have hat := hpos t ht
      unfold FirstFriedmann at h
      rw [eq_div_iff hp8.ne']
      rw [div_pow] at h
      field_simp at h
      nlinarith [h]
    -- bounds on `(t₁, t₀]`
    have hdbound : ∀ t ∈ Ioc t₁ t₀, deriv a t ^ 2 + k ≤ max C 0 / L ^ 4 := by
      intro t ht
      have hat : L ≤ a t := hLa t ht
      have hL4 : 0 < L ^ 4 := by positivity
      have hq := hQle t ht
      simp only [hQ] at hq
      have h4 : L ^ 4 ≤ a t ^ 4 := pow_le_pow_left₀ hL0.le hat 4
      rw [le_div_iff₀ hL4]
      by_cases hs : 0 ≤ deriv a t ^ 2 + k
      · calc (deriv a t ^ 2 + k) * L ^ 4 ≤ (deriv a t ^ 2 + k) * a t ^ 4 := mul_le_mul_of_nonneg_left h4 hs
          _ ≤ C := hq
          _ ≤ max C 0 := le_max_left _ _
      · push Not at hs
        have : (deriv a t ^ 2 + k) * L ^ 4 < 0 := mul_neg_of_neg_of_pos hs hL4
        linarith [le_max_right C 0]
    set B := max C 0 / L ^ 4 + |k|
    refine ⟨max (max (Real.sqrt B) (3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2)))
      (4 * Real.pi * Gn / 3 * (4 * (3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2))) * a t₀), fun t ht => ?_⟩
    have hat : L ≤ a t := hLa t ht
    have hat0 : 0 < a t := hpos t (hsub ht)
    have hata : a t ≤ a t₀ := hmono ht ht₀I ht.2
    have hdt : 0 < deriv a t := lt_of_lt_of_le hH (hge t ht)
    have hd2 : deriv a t ^ 2 ≤ B := by
      have := hdbound t ht; have := neg_abs_le k; simp only [B]; linarith
    have hB0 : 0 ≤ B := le_trans (sq_nonneg _) hd2
    -- `|a'| ≤ √B`
    have hA : |deriv a t| ≤ Real.sqrt B := by
      rw [abs_of_pos hdt]; exact Real.le_sqrt_of_sq_le hd2
    -- `|ρ| ≤ (3/8πG) (B + |k|)/L²`
    have hρ' : ρ t = (deriv a t ^ 2 + k) / (8 * Real.pi * Gn / 3) / a t ^ 2 := by
      rw [← hρeq t (hsub ht)]; field_simp
    have hL2 : L ^ 2 ≤ a t ^ 2 := pow_le_pow_left₀ hL0.le hat 2
    have hρb : |ρ t| ≤ 3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2) := by
      rw [hρ', abs_div, abs_div, abs_of_pos hp8, abs_of_pos (by positivity : (0 : ℝ) < a t ^ 2)]
      have hnum : |deriv a t ^ 2 + k| ≤ B + |k| := by
        calc |deriv a t ^ 2 + k| ≤ |deriv a t ^ 2| + |k| := abs_add_le _ _
          _ ≤ B + |k| := by rw [abs_of_nonneg (sq_nonneg _)]; linarith
      have hL2p : 0 < L ^ 2 := by positivity
      rw [div_div, div_le_iff₀ (by positivity)]
      calc |deriv a t ^ 2 + k| ≤ B + |k| := hnum
        _ = 3 / (8 * Real.pi * Gn) * ((B / L ^ 2 + |k| / L ^ 2)) * (8 * Real.pi * Gn / 3 * L ^ 2) := by
          field_simp
        _ ≤ 3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2) * (8 * Real.pi * Gn / 3 * a t ^ 2) := by
          have : 0 ≤ 3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2) := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 hp8.le) this
    set R := 3 / (8 * Real.pi * Gn) * (B / L ^ 2 + |k| / L ^ 2)
    have hρle : ρ t ≤ R := le_trans (le_abs_self _) hρb
    have hS' := hS t (hsub ht)
    have hD' := hD t (hsub ht)
    -- `|p| ≤ |ρ|`: `-ρ/3 ≤ p ≤ ρ`
    have hρ0 : 0 ≤ ρ t := by linarith
    have hpb : |p t| ≤ R := by
      rw [abs_le]; constructor <;> linarith
    -- `|a''| = (4πG/3)(ρ + 3p) a ≤ (4πG/3) 4R a(t₀)`
    have h2 := hF2 t (hsub ht)
    unfold SecondFriedmann at h2
    have hdd' : deriv (deriv a) t = -(4 * Real.pi * Gn / 3) * (ρ t + 3 * p t) * a t := by
      field_simp at h2 ⊢; linarith
    have hAA : |deriv (deriv a) t| ≤ 4 * Real.pi * Gn / 3 * (4 * R) * a t₀ := by
      rw [hdd', abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi * Gn / 3),
        abs_of_nonneg hS', abs_of_pos hat0]
      have h1 : ρ t + 3 * p t ≤ 4 * R := by linarith
      have : 0 ≤ 4 * Real.pi * Gn / 3 := by positivity
      calc 4 * Real.pi * Gn / 3 * (ρ t + 3 * p t) * a t ≤ 4 * Real.pi * Gn / 3 * (4 * R) * a t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 this) hat0.le
        _ ≤ 4 * Real.pi * Gn / 3 * (4 * R) * a t₀ := by
            have : 0 ≤ 4 * Real.pi * Gn / 3 * (4 * R) := by
              have : 0 ≤ R := le_trans (abs_nonneg _) hρb
              positivity
            exact mul_le_mul_of_nonneg_left hata this
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact le_trans hA (le_trans (le_max_left _ _) (le_max_left _ _))
    · exact le_trans hAA (le_max_right _ _)
    · exact le_trans hρb (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact le_trans hpb (le_trans (le_max_right _ _) (le_max_left _ _))

/-! ## Without `p ≤ ρ` the singularity need not be at `a = 0` -/

/-- The scale factor `a(t) = 1 + √t`. -/
noncomputable def onePlusSqrt (t : ℝ) : ℝ := 1 + Real.sqrt t

theorem hasDerivAt_onePlusSqrt {t : ℝ} (ht : 0 < t) :
    HasDerivAt onePlusSqrt (1 / (2 * Real.sqrt t)) t := by
  have := (Real.hasDerivAt_sqrt ht.ne').const_add 1
  unfold onePlusSqrt
  exact this

theorem deriv_onePlusSqrt {t : ℝ} (ht : 0 < t) : deriv onePlusSqrt t = 1 / (2 * Real.sqrt t) :=
  (hasDerivAt_onePlusSqrt ht).deriv

theorem deriv2_onePlusSqrt {t : ℝ} (ht : 0 < t) :
    deriv (deriv onePlusSqrt) t = -(1 / (4 * t * Real.sqrt t)) := by
  have heq : deriv onePlusSqrt =ᶠ[𝓝 t] fun s => 1 / (2 * Real.sqrt s) :=
    Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht) fun s hs => deriv_onePlusSqrt hs
  rw [heq.deriv_eq]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have h1 : HasDerivAt (fun s => 2 * Real.sqrt s) (2 * (1 / (2 * Real.sqrt t))) t :=
    (Real.hasDerivAt_sqrt ht.ne').const_mul 2
  have h2 := h1.inv (by positivity)
  have h3 : (fun s => 1 / (2 * Real.sqrt s)) = fun s => (2 * Real.sqrt s)⁻¹ := by funext s; rw [one_div]
  rw [h3, show (fun s => (2 * Real.sqrt s)⁻¹) = (fun s => 2 * Real.sqrt s)⁻¹ from rfl, h2.deriv]
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  nlinarith [hst]

/-- The density of `a = 1 + √t` with `k = 0`, `Λ = 0`, read off from Friedmann's first equation. -/
noncomputable def onePlusSqrtρ (Gn : ℝ) (t : ℝ) : ℝ :=
  3 / (8 * Real.pi * Gn) * (deriv onePlusSqrt t / onePlusSqrt t) ^ 2

/-- The pressure of `a = 1 + √t` with `k = 0`, `Λ = 0`, read off from Friedmann's second equation. -/
noncomputable def onePlusSqrtP (Gn : ℝ) (t : ℝ) : ℝ :=
  -(deriv (deriv onePlusSqrt) t / onePlusSqrt t) / (4 * Real.pi * Gn) - onePlusSqrtρ Gn t / 3

/-- **`a = 1 + √t` solves Friedmann's equations with `ρ > 0`, `p > 0`, `a' > 0`, `a'' < 0` on `(0, ∞)`**, and as `t ↓ 0`,
`a → 1` while `a' → ∞`: the expansion rate and the density diverge at a finite time with `a` bounded away from `0`. -/
theorem onePlusSqrt_friedmann {Gn : ℝ} (hG : 0 < Gn) :
    (∀ t > 0, FirstFriedmann onePlusSqrt (onePlusSqrtρ Gn) 0 0 Gn t ∧
      SecondFriedmann onePlusSqrt (onePlusSqrtρ Gn) (onePlusSqrtP Gn) 0 Gn t ∧
      0 < onePlusSqrtρ Gn t ∧ 0 < onePlusSqrtP Gn t ∧ 0 < deriv onePlusSqrt t ∧ deriv (deriv onePlusSqrt) t < 0) ∧
    Tendsto onePlusSqrt (𝓝[>] 0) (𝓝 1) ∧ Tendsto (deriv onePlusSqrt) (𝓝[>] 0) atTop := by
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have ha : 0 < onePlusSqrt t := by unfold onePlusSqrt; positivity
    have hd := deriv_onePlusSqrt ht
    have hdd := deriv2_onePlusSqrt ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold FirstFriedmann onePlusSqrtρ; field_simp; ring
    · unfold SecondFriedmann onePlusSqrtP onePlusSqrtρ; field_simp; ring
    · unfold onePlusSqrtρ; rw [hd]; positivity
    · unfold onePlusSqrtP onePlusSqrtρ
      rw [hd, hdd]
      unfold onePlusSqrt at ha ⊢
      -- `p = (2 + √t) / (32 π G a² t^{3/2}) > 0`
      have key : -(-(1 / (4 * t * Real.sqrt t)) / (1 + Real.sqrt t)) / (4 * Real.pi * Gn) -
          3 / (8 * Real.pi * Gn) * (1 / (2 * Real.sqrt t) / (1 + Real.sqrt t)) ^ 2 / 3 =
          (2 + Real.sqrt t) / (32 * Real.pi * Gn * (1 + Real.sqrt t) ^ 2 * t * Real.sqrt t) := by
        field_simp
        nlinarith [hst]
      rw [key]; positivity
    · rw [hd]; positivity
    · rw [hdd]; have : 0 < 1 / (4 * t * Real.sqrt t) := by positivity
      linarith
  · have : Tendsto onePlusSqrt (𝓝 0) (𝓝 1) := by
      have := ((Real.continuous_sqrt.const_add 1).tendsto 0)
      unfold onePlusSqrt
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  · have h1 : Tendsto (fun t => 2 * Real.sqrt t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((Real.continuous_sqrt.const_mul 2).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos two_pos (Real.sqrt_pos.2 ht)
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [deriv_onePlusSqrt ht]

/-- **The hypothesis `p ≤ ρ` cannot be dropped from `bigBang_singularity`**: for `a = 1 + √t`, which satisfies all its other
hypotheses on `(0, 2)` with `t₀ = 1`, `p > ρ` somewhere in `(0, 2)`. -/
theorem onePlusSqrt_not_dominant {Gn : ℝ} (hG : 0 < Gn) :
    ∃ t ∈ Ioo (0 : ℝ) 2, onePlusSqrtρ Gn t < onePlusSqrtP Gn t := by
  obtain ⟨hF, hlim, hinf⟩ := onePlusSqrt_friedmann hG
  by_contra hcon
  push Not at hcon
  have hC : ContDiffOn ℝ 2 onePlusSqrt (Ioo 0 2) := by
    intro t ht
    have : ContDiffAt ℝ 2 onePlusSqrt t := by
      unfold onePlusSqrt
      exact contDiffAt_const.add (Real.contDiffAt_sqrt ht.1.ne')
    exact this.contDiffWithinAt
  have h := bigBang_singularity (k := 0) hG hC (fun t ht => by unfold onePlusSqrt; positivity)
    (fun t ht => (hF t ht.1).1) (fun t ht => (hF t ht.1).2.1)
    (fun t ht => by have := hF t ht.1; linarith [this.2.2.1, this.2.2.2.1])
    hcon (t₀ := 1) ⟨one_pos, one_lt_two⟩ (hF 1 one_pos).2.2.2.2.1
  rcases h with h | ⟨M, hM⟩
  · have := tendsto_nhds_unique (hlim.mono_left le_rfl) h
    norm_num at this
  · obtain ⟨t, htM, ht⟩ := ((hinf.eventually_gt_atTop M).and (Ioc_mem_nhdsGT one_pos)).exists
    have := (hM t ht).1
    have h0 : 0 < deriv onePlusSqrt t := (hF t ht.1).2.2.2.2.1
    rw [abs_of_pos h0] at this
    linarith

end Cosmology
end Lightlike
