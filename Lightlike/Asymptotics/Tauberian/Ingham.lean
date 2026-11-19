import Lightlike.Asymptotics.Tauberian.Lower

/-!
# The logarithmic Ingham Tauberian theorem

**Theorem** (`ingham_log`). Let `ρ` be a measure on `[0, ∞)`, finite on compact sets, with
`∫ exp (-β x) dρ < ∞` for every `β > 0`, and suppose that its Laplace transform grows like `e^{a/β}`
in the logarithmic sense: `β log (∫ exp (-β x) dρ) → a > 0` as `β → 0⁺`. Then the counting function
`F X = ρ [0, X]` grows like `e^{2 √(a X)}`: `log F X / (2 √(a X)) → 1` as `X → ∞`.

The upper bound is the saddle estimate `F X ≤ e^{β X} L β`. The lower bound is `counting_lower`:
the main contribution to `L β` comes from `x` near `a / β²`.

## Source and differences

The statement is the logarithmic form of the Tauberian theorem of Ingham type that gives the Cardy
growth `log ρ(Δ) ~ 2π √(c Δ / 3)` from `log Z(β) ~ π² c / (3 β)`; it is *weaker* than Ingham's theorem
(it gives the asymptotics of `log F` only, not of `F`, and without a power correction). Source for the
context: Mukhametzhanov–Zhiboedov, *Modular invariance, tauberian theorems and microcanonical entropy*,
arXiv:1904.06359, Section 1 (eq. (1.8) and the sentence before it, which attributes the asymptotics
without error term to Ingham's tauberian theorem for large Laplace transforms). The comparison with
the exact statement of Ingham's theorem is pending: Ingham's paper has not been read.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

variable {ρ : Measure ℝ} [IsFiniteMeasureOnCompacts ρ]

/-- **Two-sided bounds for the Laplace transform** from the logarithmic hypothesis. -/
lemma laplace_bounds {a : ℝ} (ha : 0 < a)
    (hL : Tendsto (fun β : ℝ => β * Real.log (laplace ρ β)) (𝓝[>] 0) (𝓝 a)) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ a / 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ γ : ℝ, 0 < γ → γ < β₀ →
      Real.exp ((a - δ) / γ) ≤ laplace ρ γ ∧ laplace ρ γ ≤ Real.exp ((a + δ) / γ) := by
  obtain ⟨β₀, hβ₀, h⟩ := Metric.tendsto_nhdsWithin_nhds.1 hL δ hδ0
  refine ⟨β₀, hβ₀, fun γ hγ hγβ => ?_⟩
  have hd := h (show γ ∈ Ioi (0 : ℝ) from hγ) (by simpa [Real.dist_eq, abs_of_pos hγ] using hγβ)
  rw [Real.dist_eq, abs_lt] at hd
  have hlog : (a - δ) / γ < Real.log (laplace ρ γ) ∧ Real.log (laplace ρ γ) < (a + δ) / γ := by
    constructor
    · rw [div_lt_iff₀ hγ]; linarith [hd.1]
    · rw [lt_div_iff₀ hγ]; linarith [hd.2]
  have hLpos : 0 < laplace ρ γ := by
    rcases (laplace_nonneg ρ γ).eq_or_lt with h0 | h0
    · exfalso
      rw [← h0, Real.log_zero] at hlog
      have : 0 < (a - δ) / γ := div_pos (by linarith) hγ
      linarith [hlog.1]
    · exact h0
  constructor
  · calc Real.exp ((a - δ) / γ) ≤ Real.exp (Real.log (laplace ρ γ)) := Real.exp_le_exp.2 hlog.1.le
      _ = laplace ρ γ := Real.exp_log hLpos
  · calc laplace ρ γ = Real.exp (Real.log (laplace ρ γ)) := (Real.exp_log hLpos).symm
      _ ≤ Real.exp ((a + δ) / γ) := Real.exp_le_exp.2 hlog.2.le

variable (hρ : ρ (Iio 0) = 0)
  (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
include hρ hint

/-- **Upper bound**: `log F X ≤ (1 + ε) 2 √(a X)` for large `X`. -/
lemma log_counting_le {a : ℝ} (ha : 0 < a)
    (hL : Tendsto (fun β : ℝ => β * Real.log (laplace ρ β)) (𝓝[>] 0) (𝓝 a)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, Real.log (counting ρ X) ≤ (1 + ε) * (2 * Real.sqrt (a * X)) := by
  set δ : ℝ := min (a / 2) (ε * a) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδε : δ ≤ ε * a := min_le_right _ _
  obtain ⟨β₀, hβ₀, hb⟩ := laplace_bounds ha hL hδ0 hδa
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (a / β₀ ^ 2)] with X hX hXβ
  set q : ℝ := Real.sqrt (a * X) with hq
  set β : ℝ := Real.sqrt (a / X) with hβdef
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hβ2 : β ^ 2 = a / X := Real.sq_sqrt (by positivity)
  have hβq : β * X = q := by
    rw [hq, show a * X = (a / X) * X ^ 2 by field_simp, Real.sqrt_mul' _ (sq_nonneg X),
      Real.sqrt_sq hX.le]
  have hβlt : β < β₀ := by
    have : β ^ 2 < β₀ ^ 2 := by
      rw [hβ2, div_lt_iff₀ hX]
      rw [div_lt_iff₀ (by positivity)] at hXβ
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hβ₀.le this
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hinv : (a + δ) / β = (a + δ) * q / a := by
    have hβX2 : β ^ 2 * X = a := by rw [hβ2]; field_simp
    rw [← hβq, div_eq_div_iff hβ0.ne' ha.ne']
    linear_combination (-(a + δ)) * hβX2
  by_cases hF : counting ρ X = 0
  · rw [hF, Real.log_zero]
    positivity
  · have hFpos : 0 < counting ρ X := lt_of_le_of_ne (counting_nonneg X) (Ne.symm hF)
    have h1 := counting_mul_exp_le hint hβ0 hX.le
    have h2 := (hb β hβ0 hβlt).2
    have h3 : counting ρ X ≤ Real.exp ((a + δ) / β + β * X) := by
      have : counting ρ X ≤ laplace ρ β * Real.exp (β * X) := by
        have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (β * X)).le
        rwa [mul_assoc, ← Real.exp_add, show -β * X + β * X = 0 by ring, Real.exp_zero, mul_one] at this
      refine this.trans ?_
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have h4 := (Real.log_le_iff_le_exp hFpos).2 h3
    refine h4.trans ?_
    rw [hinv, hβq]
    have : (a + δ) * q / a + q ≤ (1 + ε) * (2 * q) := by
      rw [div_add' _ _ _ ha.ne', div_le_iff₀ ha]
      nlinarith [mul_nonneg hq0 ha.le, mul_nonneg hq0 hδ0.le, mul_nonneg hq0 (sub_nonneg.2 hδε)]
    exact this

/-- **Lower bound for fixed `η, δ`.** -/
lemma lower_eventually {a : ℝ} (ha : 0 < a)
    (hL : Tendsto (fun β : ℝ => β * Real.log (laplace ρ β)) (𝓝[>] 0) (𝓝 a)) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ0 : 0 < δ) (hδa : δ ≤ a / 2) (hδ : δ ≤ a * η ^ 2 / 36) :
    ∀ᶠ X in atTop, 0 < counting ρ X ∧
      ((2 - η) * a - δ) * Real.sqrt (X / ((1 + η) * a)) - Real.log 2 ≤ Real.log (counting ρ X) := by
  obtain ⟨β₀, hβ₀, hb⟩ := laplace_bounds ha hL hδ0 hδa
  set κ : ℝ := a * η ^ 2 / 12 with hκ
  have hκ0 : 0 < κ := by positivity
  set β₁ : ℝ := min (β₀ / (1 + η / 2)) (κ / Real.log 4) with hβ₁
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hβ₁0 : 0 < β₁ := lt_min (by positivity) (by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop ((1 + η) * a / β₁ ^ 2)]
    with X hX hXβ
  set β : ℝ := Real.sqrt ((1 + η) * a / X) with hβdef
  have hβ0 : 0 < β := Real.sqrt_pos.2 (by positivity)
  have hβ2 : β ^ 2 = (1 + η) * a / X := Real.sq_sqrt (by positivity)
  have hβlt : β < β₁ := by
    have : β ^ 2 < β₁ ^ 2 := by
      rw [hβ2, div_lt_iff₀ hX]
      rw [div_lt_iff₀ (by positivity)] at hXβ
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hβ₁0.le this
  have hβ0lt : β < β₀ / (1 + η / 2) := hβlt.trans_le (min_le_left _ _)
  have hβκ : β ≤ κ / Real.log 4 := hβlt.le.trans (min_le_right _ _)
  have hq : Real.log 4 ≤ κ / β := by
    rw [le_div_iff₀ hβ0]
    rwa [le_div_iff₀ hlog4, mul_comm] at hβκ
  have hLb : ∀ γ : ℝ, 0 < γ → γ ≤ β * (1 + η / 2) →
      Real.exp ((a - δ) / γ) ≤ laplace ρ γ ∧ laplace ρ γ ≤ Real.exp ((a + δ) / γ) := by
    intro γ hγ hγβ
    refine hb γ hγ ?_
    calc γ ≤ β * (1 + η / 2) := hγβ
      _ < β₀ := by rwa [lt_div_iff₀ (by positivity)] at hβ0lt
  have hlow := counting_lower hρ hint ha hη0 hη1 hδ0 hδ hβ0 hq hLb
  have hXeq : (1 + η) * a / β ^ 2 = X := by rw [hβ2]; field_simp
  rw [hXeq] at hlow
  have hpos : 0 < counting ρ X := lt_of_lt_of_le (by positivity) hlow
  refine ⟨hpos, ?_⟩
  have h1 : Real.log ((1 / 2) * Real.exp (((2 - η) * a - δ) / β)) ≤ Real.log (counting ρ X) :=
    Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, one_div, Real.log_inv] at h1
  have hinv : Real.sqrt (X / ((1 + η) * a)) = 1 / β := by
    rw [hβdef, one_div, ← Real.sqrt_inv, inv_div]
  rw [hinv]
  have : ((2 - η) * a - δ) * (1 / β) = ((2 - η) * a - δ) / β := by ring
  rw [this]
  linarith

/-- **The logarithmic Ingham Tauberian theorem.** If `β log L(β) → a > 0` as `β → 0⁺`, then
`log F X / (2 √(a X)) → 1` as `X → ∞`.

Why only the logarithm: the asymptotics of `F X` itself does not follow from a hypothesis on the Laplace
transform along the real axis, not even from `L(β) ~ C β^b e^{a/β}`. Bringmann–Jennings-Shaffer–Mahlburg
(arXiv:1910.03036), Section 3.2, give an increasing example with these real-axis asymptotics whose
partial sums violate the conclusion; Ingham's theorem (their Theorem 4.1) needs in addition a bound for
complex `β` in the sectors `|Im β| ≤ Δ Re β`. The logarithmic form needs only the real axis. -/
theorem ingham_log {a : ℝ} (ha : 0 < a)
    (hL : Tendsto (fun β : ℝ => β * Real.log (laplace ρ β)) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun X : ℝ => Real.log (counting ρ X) / (2 * Real.sqrt (a * X))) atTop (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set η : ℝ := ε' / 8 with hη
  set δ : ℝ := a * η ^ 2 / 36 with hδdef
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 / 8 := by rw [hη]; linarith
  have hδ0 : 0 < δ := by positivity
  have hδa : δ ≤ a / 2 := by
    rw [hδdef, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith [mul_pos ha hη0, mul_pos ha (pow_pos hη0 2)]
  have hup := log_counting_le hρ hint ha hL (show 0 < ε' / 2 by positivity)
  have hlo := lower_eventually hρ hint ha hL hη0 (by linarith) hδ0 hδa le_rfl
  -- the constant in the lower bound
  set sa : ℝ := Real.sqrt a with hsa
  have hsa0 : 0 < sa := Real.sqrt_pos.2 ha
  have hsa2 : sa ^ 2 = a := Real.sq_sqrt ha.le
  set s : ℝ := Real.sqrt (1 + η) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 + η := Real.sq_sqrt (by linarith)
  have hsle : s ≤ 1 + η / 2 := by nlinarith [sq_nonneg (s - (1 + η / 2))]
  have hs1 : 1 ≤ s := by nlinarith
  have hsq : Real.sqrt ((1 + η) * a) = s * sa := by
    rw [Real.sqrt_mul (by linarith)]
  set c : ℝ := ((2 - η) * a - δ) / (s * sa) with hc
  have hd : 0 < c - (1 - ε' / 2) * (2 * sa) := by
    rw [hc, sub_pos, lt_div_iff₀ (by positivity)]
    have h1 : 0 ≤ 1 - ε' / 2 := by linarith
    have hε8 : ε' = 8 * η := by rw [hη]; ring
    rw [hε8]
    have e : (1 - 8 * η / 2) * (2 * sa) * (s * sa) = (1 - 4 * η) * (2 * s) * a := by
      rw [← hsa2]; ring
    rw [e, hδdef]
    nlinarith [mul_pos ha hη0, mul_pos ha (pow_pos hη0 2), mul_nonneg ha.le (sub_nonneg.2 hs1),
      mul_nonneg (mul_nonneg ha.le hη0.le) (sub_nonneg.2 (show s ≤ 1 + η / 2 from hsle))]
  set d : ℝ := c - (1 - ε' / 2) * (2 * sa) with hddef
  have hsqrtX : ∀ᶠ X in atTop, Real.log 2 / d ≤ Real.sqrt X :=
    (tendsto_atTop.1 (Real.tendsto_sqrt_atTop) (Real.log 2 / d))
  filter_upwards [hup, hlo, hsqrtX, eventually_gt_atTop (0 : ℝ)] with X hX1 hX2 hX3 hX0
  obtain ⟨hpos, hlow⟩ := hX2
  have hq : Real.sqrt (a * X) = sa * Real.sqrt X := Real.sqrt_mul ha.le X
  have hq0 : 0 < Real.sqrt (a * X) := Real.sqrt_pos.2 (by positivity)
  have hsX : Real.sqrt (X / ((1 + η) * a)) = Real.sqrt X / (s * sa) := by
    rw [Real.sqrt_div hX0.le, hsq]
  rw [hsX] at hlow
  have hlow' : ((2 - η) * a - δ) * (Real.sqrt X / (s * sa)) = c * Real.sqrt X := by
    rw [hc]; ring
  rw [hlow'] at hlow
  have hX3' : Real.log 2 ≤ d * Real.sqrt X := by
    rw [div_le_iff₀ hd] at hX3; linarith
  have hlower : (1 - ε' / 2) * (2 * Real.sqrt (a * X)) ≤ Real.log (counting ρ X) := by
    rw [hq]
    have : d * Real.sqrt X = c * Real.sqrt X - (1 - ε' / 2) * (2 * (sa * Real.sqrt X)) := by
      rw [hddef]; ring
    linarith
  have h2q : 0 < 2 * Real.sqrt (a * X) := by positivity
  have hR1 : Real.log (counting ρ X) / (2 * Real.sqrt (a * X)) ≤ 1 + ε' / 2 :=
    (div_le_iff₀ h2q).2 hX1
  have hR2 : 1 - ε' / 2 ≤ Real.log (counting ρ X) / (2 * Real.sqrt (a * X)) :=
    (le_div_iff₀ h2q).2 hlower
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Lightlike.Tauberian
