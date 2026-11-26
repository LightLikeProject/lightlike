import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Entire power series: termwise differentiation (row G2-019, support for the Airy functions)

A real coefficient sequence `c : ℕ → ℝ` is *entire* if `|c n| rⁿ` is bounded for every `r ≥ 0`
(the radius of convergence of `∑ cₙ xⁿ` is infinite).  We prove, with no Airy-specific input:

* `Entire.summable_abs`: `∑ |cₙ| rⁿ` converges for every `r ≥ 0`;
* `Entire.deriv`: the coefficients `(n+1) c_{n+1}` of the derivative series are again entire;
* `Entire.hasDerivAt_eval`: `x ↦ ∑ cₙ xⁿ` has derivative `∑ (n+1) c_{n+1} xⁿ` at every `x`.

This is the analytic input needed to show that the Airy power series solve `y'' = x y`.
-/

noncomputable section

namespace Lightlike.Airy

/-- A coefficient sequence is *entire* when `|c n| * r ^ n` is bounded for every `r ≥ 0`. -/
def Entire (c : ℕ → ℝ) : Prop := ∀ r : ℝ, 0 ≤ r → ∃ D : ℝ, ∀ n, |c n| * r ^ n ≤ D

/-- The sum `∑ cₙ xⁿ` of the power series with coefficients `c`. -/
def evalSeries (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n, c n * x ^ n

/-- The coefficients of the termwise derivative: `(n+1) c_{n+1}`. -/
def dcoef (c : ℕ → ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) * c (n + 1)

/-- For an entire coefficient sequence, `∑ |cₙ| rⁿ` converges for `r ≥ 0`. -/
theorem Entire.summable_abs {c : ℕ → ℝ} (hc : Entire c) {r : ℝ} (hr : 0 ≤ r) :
    Summable fun n => |c n| * r ^ n := by
  obtain ⟨D, hD⟩ := hc (2 * r) (by positivity)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_two).mul_left D)
  have h2 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  calc |c n| * r ^ n = (|c n| * (2 * r) ^ n) * (1 / 2) ^ n := by
        rw [mul_pow]
        calc |c n| * r ^ n = |c n| * r ^ n * ((2 : ℝ) ^ n * (1 / 2) ^ n) := by rw [h2, mul_one]
          _ = _ := by ring
    _ ≤ D * (1 / 2) ^ n := by
        gcongr
        exact hD n

/-- The coefficients `(n+1) c_{n+1}` of the derivative of an entire series are entire. -/
theorem Entire.deriv {c : ℕ → ℝ} (hc : Entire c) : Entire (dcoef c) := by
  intro r hr
  obtain ⟨D, hD⟩ := hc (2 * r + 1) (by positivity)
  refine ⟨2 * D, fun n => ?_⟩
  have h1 : ((n : ℝ) + 1) * r ^ n ≤ 2 * (2 * r + 1) ^ n := by
    have hn : ((n : ℝ) + 1) ≤ 2 * 2 ^ n := by
      have := Nat.lt_two_pow_self (n := n + 1)
      have h' : ((n + 1 : ℕ) : ℝ) < ((2 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      rw [pow_succ] at h'
      linarith
    have hr' : r ^ n * 2 ^ n ≤ (2 * r + 1) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    have hpos : 0 ≤ r ^ n := by positivity
    calc ((n : ℝ) + 1) * r ^ n ≤ (2 * 2 ^ n) * r ^ n := by gcongr
      _ = 2 * (r ^ n * 2 ^ n) := by ring
      _ ≤ 2 * (2 * r + 1) ^ n := by gcongr
  have h2 : (2 * r + 1) ^ n ≤ (2 * r + 1) ^ (n + 1) :=
    pow_le_pow_right₀ (by linarith) (Nat.le_succ n)
  have hc1 : 0 ≤ |c (n + 1)| := abs_nonneg _
  have hdn : |dcoef c n| * r ^ n = ((n : ℝ) + 1) * r ^ n * |c (n + 1)| := by
    rw [dcoef, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]; ring
  rw [hdn]
  calc ((n : ℝ) + 1) * r ^ n * |c (n + 1)| ≤ (2 * (2 * r + 1) ^ n) * |c (n + 1)| := by gcongr
    _ ≤ (2 * (2 * r + 1) ^ (n + 1)) * |c (n + 1)| := by gcongr
    _ = 2 * (|c (n + 1)| * (2 * r + 1) ^ (n + 1)) := by ring
    _ ≤ 2 * D := by gcongr; exact hD (n + 1)

/-- **Termwise differentiation.** If `c` is entire, `x ↦ ∑ cₙ xⁿ` has derivative
`∑ (n+1) c_{n+1} xⁿ` at every point. -/
theorem Entire.hasDerivAt_eval {c : ℕ → ℝ} (hc : Entire c) (x : ℝ) :
    HasDerivAt (evalSeries c) (evalSeries (dcoef c) x) x := by
  set R : ℝ := |x| + 1 with hR
  have hR0 : 0 < R := by positivity
  have hdc := hc.deriv
  -- bound for the derivative terms
  set u : ℕ → ℝ := fun n => (n : ℝ) * |c n| * R ^ (n - 1) with hu
  have hu_s : Summable u := by
    rw [← summable_nat_add_iff 1]
    have := hdc.summable_abs hR0.le
    refine this.congr fun n => ?_
    simp only [hu, Nat.add_sub_cancel]
    rw [dcoef, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    push_cast
    ring
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      HasDerivAt (fun z : ℝ => c n * z ^ n) (c n * ((n : ℝ) * y ^ (n - 1))) y :=
    fun n y _ => (hasDerivAt_pow n y).const_mul (c n)
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-R) R →
      ‖c n * ((n : ℝ) * y ^ (n - 1))‖ ≤ u n := by
    intro n y hy
    have hy' : |y| ≤ R := (abs_lt.mpr hy).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    simp only [hu]
    have : |y| ^ (n - 1) ≤ R ^ (n - 1) := pow_le_pow_left₀ (abs_nonneg _) hy' _
    calc |c n| * ((n : ℝ) * |y| ^ (n - 1)) = (n : ℝ) * |c n| * |y| ^ (n - 1) := by ring
      _ ≤ (n : ℝ) * |c n| * R ^ (n - 1) := by gcongr
  have hx : x ∈ Set.Ioo (-R) R := by
    constructor <;> cases abs_cases x <;> linarith
  have h0 : (0 : ℝ) ∈ Set.Ioo (-R) R := by constructor <;> linarith
  have hsum0 : Summable fun n => c n * (0 : ℝ) ^ n := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp at hn
    simp [hn]
  have key := hasDerivAt_tsum_of_isPreconnected hu_s isOpen_Ioo isPreconnected_Ioo hg hg' h0 hsum0 hx
  -- identify the derivative series
  have hsx : Summable fun n => c n * ((n : ℝ) * x ^ (n - 1)) := by
    refine Summable.of_norm_bounded hu_s fun n => hg' n x hx
  have : (∑' n, c n * ((n : ℝ) * x ^ (n - 1))) = evalSeries (dcoef c) x := by
    rw [hsx.tsum_eq_zero_add]
    simp only [evalSeries, Nat.cast_zero, zero_mul, mul_zero, zero_add]
    refine tsum_congr fun n => ?_
    simp only [dcoef, Nat.add_sub_cancel]
    push_cast
    ring
  rw [this] at key
  exact key

end Lightlike.Airy
