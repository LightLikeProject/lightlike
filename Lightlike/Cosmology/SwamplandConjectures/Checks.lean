module

public import Lightlike.Cosmology.SwamplandConjectures.Defs

/-!
# Consequences of the de Sitter conjecture and trust checks (row G1-046, milestone CO23)

* `expPotential_gradNorm_div` : for `V = V₀ e^{-λφ} > 0`, `|∇V|/V = |λ|`.
* `expPotential_deSitter` : the exponential potential satisfies the de Sitter bound with
  `c = λ` (and with `c = |λ|`).
* `not_deSitter_of_critical` : a potential with a de Sitter critical point (`V > 0`, `dV = 0`)
  violates the bound for every `c > 0`; `quadPotential_not_deSitter` is the example
  `Λ + m²φ²/2`.
* `slowRoll_contradiction` : if the bound holds with `c > √2`, then `ε_V > 1` wherever
  `V > 0`, so the slow-roll condition `ε_V < 1` fails everywhere (`not_slowRoll_of_deSitter`).
* `slowRollEps_exp` : `ε_V = λ²/2` for the exponential potential, so `ε_V < 1` iff `λ² < 2`.
* `slowRollEps_quad` and `slowRollEps_quad_sqrt_two` : for `m²φ²/2`, `ε_V = 2/φ²`, equal to `1`
  at `φ = √2`.
-/

@[expose] public section

namespace Lightlike.Rows.G1_046

open Real

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A potential with a de Sitter critical point violates the de Sitter conjecture**, for every
`c > 0`: at a point with `V > 0` and `dV = 0` the gradient norm is `0 < c V`. -/
theorem not_deSitter_of_critical {V : E → ℝ} {φ : E} {c : ℝ} (hc : 0 < c) (hV : 0 < V φ)
    (hcrit : fderiv ℝ V φ = 0) : ¬ DeSitterConjecture c V := by
  intro h
  have h1 := h φ hV
  have h0 : gradNorm V φ = 0 := by simp [gradNorm, hcrit]
  rw [h0] at h1
  nlinarith

/-- **Slow roll contradicts the de Sitter conjecture for `c > √2`**: if `|∇V| ≥ c V` with
`c² > 2` and `V φ > 0`, then `ε_V(φ) > 1`. -/
theorem slowRoll_contradiction {V : E → ℝ} {c : ℝ} (h : DeSitterConjecture c V)
    (hc : Real.sqrt 2 < c) {φ : E} (hV : 0 < V φ) : 1 < slowRollEps V φ := by
  have hc0 : 0 < c := lt_trans (Real.sqrt_pos.mpr (by norm_num)) hc
  have hc2 : 2 < c ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have h1 : c ≤ gradNorm V φ / V φ := by
    rw [le_div_iff₀ hV]; exact h φ hV
  have h2 : c ^ 2 ≤ (gradNorm V φ / V φ) ^ 2 := pow_le_pow_left₀ hc0.le h1 2
  unfold slowRollEps
  linarith

/-- **Slow roll fails everywhere** under the de Sitter conjecture with `c > √2`: there is no point
with `V > 0` and `ε_V ≤ 1`. -/
theorem not_slowRoll_of_deSitter {V : E → ℝ} {c : ℝ} (h : DeSitterConjecture c V)
    (hc : Real.sqrt 2 < c) {φ : E} (hV : 0 < V φ) : ¬ slowRollEps V φ ≤ 1 :=
  not_le.mpr (slowRoll_contradiction h hc hV)

end General

/-- For `V = V₀ e^{-λφ}`, `|∇V| = |λ| V` wherever `V₀ ≥ 0`; in general, `|∇V|/V = |λ|` where
`V > 0`. -/
theorem expPotential_gradNorm_div {V₀ l φ : ℝ} (hV : 0 < expPotential V₀ l φ) :
    gradNorm (expPotential V₀ l) φ / expPotential V₀ l φ = |l| := by
  rw [gradNorm_real, (hasDerivAt_expPotential V₀ l φ).deriv, abs_mul, abs_neg,
    abs_of_pos hV]
  field_simp

/-- **The exponential potential satisfies the de Sitter conjecture with `c = λ`.** -/
theorem expPotential_deSitter (V₀ l : ℝ) : DeSitterConjecture l (expPotential V₀ l) := by
  intro φ hV
  have h := expPotential_gradNorm_div hV
  rw [div_eq_iff hV.ne'] at h
  rw [h]
  exact mul_le_mul_of_nonneg_right (le_abs_self l) hV.le

/-- The exponential potential satisfies the de Sitter conjecture with `c = |λ|` as well. -/
theorem expPotential_deSitter_abs (V₀ l : ℝ) : DeSitterConjecture |l| (expPotential V₀ l) := by
  intro φ hV
  have h := expPotential_gradNorm_div hV
  rw [div_eq_iff hV.ne'] at h
  rw [h]

/-- `ε_V = λ²/2` for the exponential potential, wherever `V > 0`. -/
theorem slowRollEps_exp {V₀ l φ : ℝ} (hV : 0 < expPotential V₀ l φ) :
    slowRollEps (expPotential V₀ l) φ = l ^ 2 / 2 := by
  unfold slowRollEps
  rw [expPotential_gradNorm_div hV, sq_abs]

/-- For the exponential potential, slow roll `ε_V < 1` holds iff `λ² < 2`. -/
theorem slowRollEps_exp_lt_one_iff {V₀ l φ : ℝ} (hV : 0 < expPotential V₀ l φ) :
    slowRollEps (expPotential V₀ l) φ < 1 ↔ l ^ 2 < 2 := by
  rw [slowRollEps_exp hV]
  constructor <;> intro h <;> linarith

/-- **Trust check**: the potential `Λ + m²φ²/2` with `Λ > 0` has a de Sitter critical point at
`φ = 0`, so it violates the de Sitter conjecture for every `c > 0`. -/
theorem quadPotential_not_deSitter {Λ m c : ℝ} (hΛ : 0 < Λ) (hc : 0 < c) :
    ¬ DeSitterConjecture c (quadPotential Λ m) := by
  refine not_deSitter_of_critical (φ := 0) hc ?_ ?_
  · simpa [quadPotential] using hΛ
  · rw [(hasDerivAt_quadPotential Λ m 0).hasFDerivAt.fderiv]
    simp

/-- For `V = m²φ²/2` (units `8πG = 1`), `ε_V = 2/φ²`. -/
theorem slowRollEps_quad {m φ : ℝ} (hm : m ≠ 0) (hφ : φ ≠ 0) :
    slowRollEps (quadPotential 0 m) φ = 2 / φ ^ 2 := by
  unfold slowRollEps
  rw [gradNorm_real, (hasDerivAt_quadPotential 0 m φ).deriv]
  have h1 : quadPotential 0 m φ = m ^ 2 * φ ^ 2 / 2 := by simp [quadPotential]
  rw [h1]
  rw [div_pow, sq_abs]
  field_simp

/-- **Trust check (CO9)**: for `V = m²φ²/2`, `ε_V = 1` at `φ = √2`. -/
theorem slowRollEps_quad_sqrt_two {m : ℝ} (hm : m ≠ 0) :
    slowRollEps (quadPotential 0 m) (Real.sqrt 2) = 1 := by
  rw [slowRollEps_quad hm (by positivity), Real.sq_sqrt (by norm_num)]
  norm_num

end Lightlike.Rows.G1_046
