import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Asymptotics of the central binomial coefficient and of the Catalan numbers (G2-036)

The number of plane trees with `n` edges is the Catalan number `catalan n`, and
`catalan n = centralBinom n / (n+1)`. From Stirling's formula (`Stirling.factorial_isEquivalent_stirling`)
we get `centralBinom n ~ 4ⁿ / √(π n)` and hence `catalan n ~ 4ⁿ / (√π · n^{3/2})`: growth rate `ρ⁻¹ = 4`
and polynomial correction `n^{-3/2} = n^{γ-2}` with `γ = 1/2` (the exponent of RN3).

Supporting lemmas; no catalogue entry (the catalogue statement is in the final file of
`Lightlike/Rows/G2_036/`).
-/

open Filter Asymptotics Real Nat
open scoped Topology

namespace Lightlike.PlaneTree

/-- The algebra behind Stirling for the central binomial coefficient. -/
theorem stirling_ratio_eq (n : ℕ) (hn : 1 ≤ n) :
    √(2 * ((2 * n : ℕ) : ℝ) * π) * (((2 * n : ℕ) : ℝ) / exp 1) ^ (2 * n) /
        (√(2 * (n : ℝ) * π) * ((n : ℝ) / exp 1) ^ n) ^ 2 = (4 : ℝ) ^ n / √(π * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpn : 0 < π * n := by positivity
  have hs : √(2 * ((2 * n : ℕ) : ℝ) * π) = 2 * √(π * n) := by
    rw [show 2 * ((2 * n : ℕ) : ℝ) * π = 2 ^ 2 * (π * n) by push_cast; ring,
      sqrt_mul (by positivity), sqrt_sq (by norm_num)]
  have hs2 : √(2 * (n : ℝ) * π) ^ 2 = 2 * n * π := sq_sqrt (by positivity)
  have hp : (((2 * n : ℕ) : ℝ) / exp 1) ^ (2 * n) = 4 ^ n * ((n : ℝ) / exp 1) ^ (2 * n) := by
    push_cast
    rw [mul_div_assoc, mul_pow, pow_mul (2 : ℝ) 2 n]
    norm_num
  have hq : (((n : ℝ) / exp 1) ^ n) ^ 2 = ((n : ℝ) / exp 1) ^ (2 * n) := by
    rw [← pow_mul, mul_comm]
  have hsq : 0 < √(π * n) := sqrt_pos.2 hpn
  have hsq2 : √(π * n) ^ 2 = π * n := sq_sqrt hpn.le
  rw [hs, hp, mul_pow, hs2, hq]
  have hE : 0 < ((n : ℝ) / exp 1) ^ (2 * n) := by positivity
  field_simp
  nlinarith [hsq2]

/-- **Central binomial asymptotics**: `C(2n, n) ~ 4ⁿ / √(π n)`. -/
theorem centralBinom_isEquivalent :
    (fun n : ℕ => (n.centralBinom : ℝ)) ~[atTop] fun n : ℕ => (4 : ℝ) ^ n / √(π * n) := by
  have h1 : (fun n : ℕ => ((2 * n)! : ℝ)) ~[atTop]
      fun n : ℕ => √(2 * ((2 * n : ℕ) : ℝ) * π) * (((2 * n : ℕ) : ℝ) / exp 1) ^ (2 * n) :=
    Stirling.factorial_isEquivalent_stirling.comp_tendsto
      (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
  have h2 : (fun n : ℕ => ((n ! : ℝ)) ^ 2) ~[atTop]
      fun n : ℕ => (√(2 * (n : ℝ) * π) * ((n : ℝ) / exp 1) ^ n) ^ 2 :=
    Stirling.factorial_isEquivalent_stirling.pow 2
  have h3 := h1.div h2
  have hcb : ∀ n : ℕ, (n.centralBinom : ℝ) = ((2 * n)! : ℝ) / ((n ! : ℝ)) ^ 2 := by
    intro n
    rw [Nat.centralBinom, Nat.cast_choose ℝ (by omega : n ≤ 2 * n)]
    rw [show 2 * n - n = n by omega, sq]
  refine (h3.congr_left (Eventually.of_forall (fun n => (hcb n).symm))).congr_right ?_
  exact eventually_atTop.2 ⟨1, fun n hn => stirling_ratio_eq n hn⟩

/-- `catalan n * (n + 1) = centralBinom n`, in `ℝ`. -/
theorem catalan_mul_succ (n : ℕ) : (catalan n : ℝ) * (n + 1) = n.centralBinom := by
  have h := Nat.div_mul_cancel (Nat.succ_dvd_centralBinom n)
  rw [← catalan_eq_centralBinom_div] at h
  exact_mod_cast h

/-- `n + 1 ~ n`. -/
theorem succ_isEquivalent : (fun n : ℕ => (n : ℝ) + 1) ~[atTop] fun n : ℕ => (n : ℝ) := by
  apply isEquivalent_of_tendsto_one
  have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at this
  refine this.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [field]

/-- **Catalan asymptotics**: `catalan n ~ 4ⁿ / (√π · n^{3/2})`. The number of plane trees with `n`
edges grows like `4ⁿ` times `n^{-3/2}`. -/
theorem catalan_isEquivalent :
    (fun n : ℕ => (catalan n : ℝ)) ~[atTop] fun n : ℕ => (4 : ℝ) ^ n / (√π * (n : ℝ) ^ (3 / 2 : ℝ)) := by
  have h1 : (fun n : ℕ => (n.centralBinom : ℝ) / ((n : ℝ) + 1)) ~[atTop]
      fun n : ℕ => (4 : ℝ) ^ n / √(π * n) / (n : ℝ) :=
    centralBinom_isEquivalent.div succ_isEquivalent
  have hc : (fun n : ℕ => (catalan n : ℝ)) = fun n : ℕ => (n.centralBinom : ℝ) / ((n : ℝ) + 1) := by
    funext n
    rw [eq_div_iff (by positivity)]
    exact catalan_mul_succ n
  rw [hc]
  refine h1.congr_right (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h32 : (n : ℝ) ^ (3 / 2 : ℝ) = n * √n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hn', rpow_one, ← sqrt_eq_rpow]
  show (4 : ℝ) ^ n / √(π * n) / (n : ℝ) = (4 : ℝ) ^ n / (√π * (n : ℝ) ^ (3 / 2 : ℝ))
  rw [h32, sqrt_mul pi_pos.le, div_div]
  congr 1
  ring

end Lightlike.PlaneTree
