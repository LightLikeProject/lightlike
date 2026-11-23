import Mathlib

/-!
# The logarithm of the chiral boson partition function: `β log Z(β) → π²/6`

The chiral free boson has one oscillator of energy `n` for each `n ≥ 1`, so its partition function is
`Z(β) = ∏_{n ≥ 1} (1 - e^{-βn})⁻¹`. This file treats the analytic half of the growth of its spectrum:

`bosonLogZ β = ∑_{n ≥ 1} (-log (1 - e^{-βn}))`, and `β · bosonLogZ β → π²/6` as `β → 0⁺`
(`tendsto_mul_bosonLogZ`).

The proof expands `-log (1 - q) = ∑_{j ≥ 1} q^j / j`, interchanges the two sums (all terms are
nonnegative; `bosonLogZ_eq`) to get `bosonLogZ β = ∑_j (1/j) · 1/(e^{βj} - 1)`, and applies dominated
convergence (Mathlib's `tendsto_tsum_of_dominated_convergence`) to `β · (1/j) · 1/(e^{βj} - 1) → 1/j²`,
with the bound `1/j²`; the sum is `π²/6` (Mathlib's `hasSum_zeta_two`).

The combinatorial half (the spectrum `∑ p(n) δ_n` has Laplace transform `Z`) is in a separate file.
No catalogue entry: supporting lemmas.
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.SP3Row

/-- `log Z(β) = ∑_{k ≥ 1} (-log (1 - e^{-βk}))` for the chiral boson, `Z(β) = ∏ (1 - e^{-βk})⁻¹`. -/
def bosonLogZ (β : ℝ) : ℝ := ∑' k : ℕ, -Real.log (1 - Real.exp (-(β * ((k : ℝ) + 1))))

/-- The slope of the exponential at `0`, from the right. -/
lemma tendsto_exp_sub_one_div : Tendsto (fun t : ℝ => (Real.exp t - 1) / t) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  simpa [div_eq_inv_mul] using h

/-- `t / (e^t - 1) → 1` as `t → 0⁺`. -/
lemma tendsto_div_exp_sub_one : Tendsto (fun t : ℝ => t / (Real.exp t - 1)) (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_exp_sub_one_div.inv₀ one_ne_zero
  simpa using h.congr' (by
    filter_upwards with t
    simp [inv_div])

/-- `β / (e^{βm} - 1) → 1/m` as `β → 0⁺`, for `m > 0`. -/
lemma tendsto_div_exp_mul {m : ℝ} (hm : 0 < m) :
    Tendsto (fun β : ℝ => β / (Real.exp (β * m) - 1)) (𝓝[>] 0) (𝓝 (1 / m)) := by
  have hmul : Tendsto (fun β : ℝ => β * m) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun β : ℝ => β * m) (𝓝 0) (𝓝 (0 * m)) := (continuous_id.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      exact mul_pos hβ hm
  have h := (tendsto_div_exp_sub_one.comp hmul).const_mul (1 / m)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  simp only [Function.comp]
  field_simp

/-- For `β > 0` and `m > 0`: `β / (e^{βm} - 1) ≤ 1/m`. -/
lemma div_exp_sub_one_le {β m : ℝ} (hβ : 0 < β) (hm : 0 < m) :
    β / (Real.exp (β * m) - 1) ≤ 1 / m := by
  have h1 : β * m + 1 ≤ Real.exp (β * m) := Real.add_one_le_exp _
  have hpos : 0 < Real.exp (β * m) - 1 := by nlinarith [mul_pos hβ hm]
  rw [div_le_div_iff₀ hpos hm]
  nlinarith

/-- The double series: for `β > 0`, `bosonLogZ β = ∑_j (1/(j+1)) · 1/(e^{β(j+1)} - 1)`. -/
lemma bosonLogZ_eq {β : ℝ} (hβ : 0 < β) :
    bosonLogZ β = ∑' j : ℕ, (1 / ((j : ℝ) + 1)) * (1 / (Real.exp (β * ((j : ℝ) + 1)) - 1)) := by
  set F : ℕ → ℕ → ℝ := fun j k =>
    Real.exp (-(β * ((j : ℝ) + 1) * ((k : ℝ) + 1))) / ((j : ℝ) + 1) with hF
  have hr : ∀ j : ℕ, Real.exp (-(β * ((j : ℝ) + 1))) < 1 := fun j => by
    rw [Real.exp_lt_one_iff]; nlinarith [mul_pos hβ (show (0 : ℝ) < (j : ℝ) + 1 by positivity)]
  have hexp : ∀ j k : ℕ, Real.exp (-(β * ((j : ℝ) + 1) * ((k : ℝ) + 1))) =
      Real.exp (-(β * ((j : ℝ) + 1))) ^ (k + 1) := fun j k => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- inner sums over `k`
  have hinner : ∀ j : ℕ, HasSum (fun k : ℕ => F j k)
      (Real.exp (-(β * ((j : ℝ) + 1))) * (1 - Real.exp (-(β * ((j : ℝ) + 1))))⁻¹ /
        ((j : ℝ) + 1)) := by
    intro j
    have hg := hasSum_geometric_of_lt_one (Real.exp_pos _).le (hr j)
    have h2 := (hg.mul_left (Real.exp (-(β * ((j : ℝ) + 1))))).div_const ((j : ℝ) + 1)
    have hfun : (fun k : ℕ => F j k) = fun k : ℕ =>
        Real.exp (-(β * ((j : ℝ) + 1))) * Real.exp (-(β * ((j : ℝ) + 1))) ^ k / ((j : ℝ) + 1) := by
      funext k
      simp only [hF, hexp, pow_succ]
      ring
    rw [hfun]
    exact h2
  have hval : ∀ j : ℕ, Real.exp (-(β * ((j : ℝ) + 1))) * (1 - Real.exp (-(β * ((j : ℝ) + 1))))⁻¹ /
        ((j : ℝ) + 1) = (1 / ((j : ℝ) + 1)) * (1 / (Real.exp (β * ((j : ℝ) + 1)) - 1)) := by
    intro j
    have hne : Real.exp (β * ((j : ℝ) + 1)) - 1 ≠ 0 := by
      have : 1 < Real.exp (β * ((j : ℝ) + 1)) := by
        rw [Real.one_lt_exp_iff]; exact mul_pos hβ (by positivity)
      linarith
    have hne2 : 1 - Real.exp (-(β * ((j : ℝ) + 1))) ≠ 0 := by linarith [hr j]
    rw [Real.exp_neg] at hne2 ⊢
    have hE : Real.exp (β * ((j : ℝ) + 1)) ≠ 0 := (Real.exp_pos _).ne'
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  -- summability of the outer sum
  have hs0 : Real.exp (-β) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hsum_outer : Summable fun j : ℕ => ∑' k : ℕ, F j k := by
    have hbd : ∀ j : ℕ, ∑' k : ℕ, F j k ≤ Real.exp (-β) ^ (j + 1) * (1 - Real.exp (-β))⁻¹ := by
      intro j
      rw [(hinner j).tsum_eq]
      have hrj : Real.exp (-(β * ((j : ℝ) + 1))) = Real.exp (-β) ^ (j + 1) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hrj]
      have hle : Real.exp (-β) ^ (j + 1) ≤ Real.exp (-β) :=
        pow_le_of_le_one (Real.exp_pos _).le hs0.le (Nat.succ_ne_zero j)
      have hpos : 0 < 1 - Real.exp (-β) ^ (j + 1) := by
        have := pow_lt_one₀ (Real.exp_pos (-β)).le hs0 (Nat.succ_ne_zero j); linarith
      have hinv : (1 - Real.exp (-β) ^ (j + 1))⁻¹ ≤ (1 - Real.exp (-β))⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      have hj : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      calc Real.exp (-β) ^ (j + 1) * (1 - Real.exp (-β) ^ (j + 1))⁻¹ / ((j : ℝ) + 1)
          ≤ Real.exp (-β) ^ (j + 1) * (1 - Real.exp (-β) ^ (j + 1))⁻¹ :=
            div_le_self (by positivity) hj
        _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)
    refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => ?_) hbd ?_
    · simp only [hF]; positivity
    · exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hs0).mul_right
        (Real.exp (-β) * (1 - Real.exp (-β))⁻¹)).congr (fun j => by ring)
  have hsumm : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg (fun p => by simp only [hF, Function.uncurry]; positivity)]
    exact ⟨fun j => (hinner j).summable, hsum_outer⟩
  -- the sum over `j` for fixed `k`
  have hk : ∀ k : ℕ, ∑' j : ℕ, F j k = -Real.log (1 - Real.exp (-(β * ((k : ℝ) + 1)))) := by
    intro k
    have hq : |Real.exp (-(β * ((k : ℝ) + 1)))| < 1 := by
      rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      nlinarith [mul_pos hβ (show (0 : ℝ) < (k : ℝ) + 1 by positivity)]
    have hF2 : (fun j : ℕ => F j k) = fun j : ℕ =>
        Real.exp (-(β * ((k : ℝ) + 1))) ^ (j + 1) / ((j : ℝ) + 1) := by
      funext j
      simp only [hF]
      rw [← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [hF2]
    exact (Real.hasSum_pow_div_log_of_abs_lt_one hq).tsum_eq
  unfold bosonLogZ
  calc ∑' k : ℕ, -Real.log (1 - Real.exp (-(β * ((k : ℝ) + 1))))
      = ∑' k : ℕ, ∑' j : ℕ, F j k := tsum_congr fun k => (hk k).symm
    _ = ∑' j : ℕ, ∑' k : ℕ, F j k := hsumm.tsum_comm
    _ = _ := tsum_congr fun j => by rw [(hinner j).tsum_eq, hval j]

/-- **`β log Z(β) → π²/6`** for the chiral boson: `β · bosonLogZ β → π²/6` as `β → 0⁺`. -/
theorem tendsto_mul_bosonLogZ :
    Tendsto (fun β : ℝ => β * bosonLogZ β) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2) (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using h
  have hz' : HasSum (fun n : ℕ => (1 / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) (π ^ 2 / 6) := by
    have hfun : (fun n : ℕ => (1 / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) =
        fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) ^ 2 := by
      funext n; push_cast; rw [one_div_mul_one_div, ← sq]
    rw [hfun]; exact hz
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun (β : ℝ) (j : ℕ) => (1 / ((j : ℝ) + 1)) * (β / (Real.exp (β * ((j : ℝ) + 1)) - 1)))
    (g := fun j : ℕ => (1 / ((j : ℝ) + 1)) * (1 / ((j : ℝ) + 1)))
    (bound := fun j : ℕ => (1 / ((j : ℝ) + 1)) * (1 / ((j : ℝ) + 1))) hz'.summable
    (fun j => (tendsto_div_exp_mul (by positivity)).const_mul _) (by
      filter_upwards [self_mem_nhdsWithin] with β hβ j
      have hβ' : 0 < β := hβ
      have hm : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hpos : 0 < Real.exp (β * ((j : ℝ) + 1)) - 1 := by
        have := Real.add_one_le_exp (β * ((j : ℝ) + 1))
        nlinarith [mul_pos hβ' hm]
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (div_exp_sub_one_le hβ' hm) (by positivity))
  rw [hz'.tsum_eq] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβ' : 0 < β := hβ
  rw [bosonLogZ_eq hβ', ← tsum_mul_left]
  exact tsum_congr fun j => by ring

end Lightlike.SP3Row
