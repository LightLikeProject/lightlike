import Mathlib

/-!
# Complex Stirling formula, midpoint form

For `w` in the slit plane `ℂ ∖ (−∞, 0]`,

`Γ(w + ½) = √(2π) · exp(w log w − w + μ(w))`   (`Gamma_half_add`),

with principal logarithms and an explicit remainder `μ(w) = Σₙ d(w + n)`, where
`f(w) = w log w − w` (`stirF`) and `d(w) = f(w + 1) − f(w) − log(w + ½)` (`stirD`). The midpoint
form is the natural one: `d` is the error of the midpoint rule for `∫_w^{w+1} log`, so
`‖d(w)‖ ≤ 3/(8‖w + ½‖²)` (`norm_stirD_le`), and on every sector `Re w ≥ −c‖w‖` with `c < 1`,
`‖μ(w)‖ ≤ 4/((1 − c)‖w‖)` once `‖w‖² ≥ 2/(1 − c)` (`norm_stirMu_le`).

The proof is by telescoping, with no contour integral: `μ(w) = d(w) + μ(w + 1)`, so
`√(2π) exp(f + μ)` satisfies the functional equation of `Γ(w + ½)`, and the ratio of the two is
`1`-periodic. Along `w + N` the ratio tends to `1`, by Euler's limit `GammaSeq_tendsto_Gamma` and
the real Stirling formula `Stirling.tendsto_stirlingSeq_sqrt_pi`.
-/

open Complex Filter Topology
open scoped Nat

namespace Lightlike.Asymptotics

/-- The Stirling exponent `f(w) = w log w − w` (principal logarithm). -/
noncomputable def stirF (w : ℂ) : ℂ := w * log w - w

/-- The midpoint defect `d(w) = f(w + 1) − f(w) − log(w + ½)`. -/
noncomputable def stirD (w : ℂ) : ℂ := stirF (w + 1) - stirF w - log (w + 1 / 2)

/-- The Stirling remainder `μ(w) = Σₙ d(w + n)`. -/
noncomputable def stirMu (w : ℂ) : ℂ := ∑' n : ℕ, stirD (w + n)

/-! ## Branch identities -/

/-- `arg y ≤ 0` when `y` lies in the open lower half-plane or on the closed positive axis. -/
lemma arg_nonpos_of {y : ℂ} (h : y.im < 0 ∨ (y.im = 0 ∧ 0 ≤ y.re)) : arg y ≤ 0 := by
  rcases h with h | ⟨h0, hr⟩
  · exact (arg_neg_iff.2 h).le
  · exact (arg_eq_zero_iff.2 ⟨hr, h0⟩).le

/-- `log (x y) = log x + log y` when `arg x ≥ 0 ≥ arg y`: the arguments then add up to a value
in `(−π, π]`. -/
lemma log_mul_of_arg {x y : ℂ} (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : 0 ≤ arg x) (hy : arg y ≤ 0) :
    log (x * y) = log x + log y := by
  rw [log_mul_eq_add_log_iff hx0 hy0]
  constructor
  · linarith [neg_pi_lt_arg y]
  · linarith [arg_le_pi x]

/-- For `v` in the slit plane, `log (v + ½) = log v + log (1 + 1/(2v))`. The imaginary parts of
`v` and of `1 + 1/(2v)` have opposite signs, so no branch cut is crossed. -/
lemma log_add_half {v : ℂ} (hv : v ∈ slitPlane) :
    log (v + 1 / 2) = log v + log (1 + (2 * v)⁻¹) := by
  have hv0 : v ≠ 0 := slitPlane_ne_zero hv
  have hprod : v + 1 / 2 = v * (1 + (2 * v)⁻¹) := by field_simp
  have him : (1 + (2 * v)⁻¹).im = -v.im / (2 * normSq v) := by
    simp [inv_im]; ring
  have hre : (1 + (2 * v)⁻¹).re = 1 + v.re / (2 * normSq v) := by
    simp [inv_re]; ring
  have hN : 0 < normSq v := normSq_pos.2 hv0
  rcases lt_trichotomy v.im 0 with hi | hi | hi
  · -- lower half-plane: swap the roles of the two factors
    have hy0 : (1 + (2 * v)⁻¹) ≠ 0 := by
      intro h; have h2 := congrArg Complex.im h
      rw [him, zero_im, div_eq_zero_iff] at h2
      rcases h2 with h2 | h2 <;> [linarith; linarith]
    rw [hprod, mul_comm, log_mul_of_arg hy0 hv0, add_comm]
    · rw [arg_nonneg_iff, him]; exact div_nonneg (by linarith) (by positivity)
    · exact arg_nonpos_of (Or.inl hi)
  · have hre0 : 0 < v.re := by
      rcases mem_slitPlane_iff.1 hv with h | h
      · exact h
      · exact absurd hi h
    have hy0 : (1 + (2 * v)⁻¹) ≠ 0 := by
      intro h; have := congrArg Complex.re h; rw [hre] at this
      simp at this; have : 0 < 1 + v.re / (2 * normSq v) := by positivity
      linarith
    rw [hprod, log_mul_of_arg hv0 hy0]
    · rw [arg_nonneg_iff]; exact hi.ge
    · refine arg_nonpos_of (Or.inr ⟨?_, ?_⟩)
      · rw [him, hi]; simp
      · rw [hre]; positivity
  · have hy0 : (1 + (2 * v)⁻¹) ≠ 0 := by
      intro h; have h2 := congrArg Complex.im h
      rw [him, zero_im, div_eq_zero_iff] at h2
      rcases h2 with h2 | h2 <;> [linarith; linarith]
    rw [hprod, log_mul_of_arg hv0 hy0]
    · rw [arg_nonneg_iff]; exact hi.le
    · refine arg_nonpos_of (Or.inl ?_)
      rw [him]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- For `w` in the slit plane with `‖w + ½‖ ≥ 1`, `log w = log (w + ½) + log (1 − 1/(2(w + ½)))`. -/
lemma log_sub_half {w : ℂ} (hw : w ∈ slitPlane) (hu : 1 ≤ ‖w + 1 / 2‖) :
    log w = log (w + 1 / 2) + log (1 - (2 * (w + 1 / 2))⁻¹) := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hu0 : w + 1 / 2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; linarith
  have hinv : 1 + (2 * w)⁻¹ = (1 - (2 * (w + 1 / 2))⁻¹)⁻¹ := by
    have h2 : 2 * w + 1 ≠ 0 := by
      intro h; apply hu0; linear_combination h / 2
    field_simp
    ring
  have hsmall : ‖(2 * (w + 1 / 2))⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, norm_mul, Complex.norm_two]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hre : 0 < (1 - (2 * (w + 1 / 2))⁻¹).re := by
    have := Complex.abs_re_le_norm (2 * (w + 1 / 2))⁻¹
    rw [sub_re, one_re]; linarith [le_abs_self ((2 * (w + 1 / 2))⁻¹).re]
  have hpi : arg (1 - (2 * (w + 1 / 2))⁻¹) ≠ Real.pi := by
    intro h
    have := arg_lt_pi_iff.2 (Or.inl hre.le)
    linarith
  have h1 := log_add_half hw
  rw [hinv, log_inv _ hpi] at h1
  linear_combination -h1

/-! ## The midpoint defect -/

/-- `logTaylor 3 z = z − z²/2`. -/
lemma logTaylor_three (z : ℂ) : logTaylor 3 z = z - z ^ 2 / 2 := by
  simp [logTaylor, Finset.sum_range_succ]
  ring

/-- Third-order Taylor bound for `log (1 + z)` on `‖z‖ ≤ ½`. -/
lemma norm_log_sub_taylor2_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖log (1 + z) - (z - z ^ 2 / 2)‖ ≤ 2 / 3 * ‖z‖ ^ 3 := by
  have h := norm_log_sub_logTaylor_le 2 (z := z) (by linarith)
  rw [logTaylor_three] at h
  refine h.trans ?_
  have h1 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h3 : 0 ≤ ‖z‖ ^ 3 := by positivity
  norm_num
  nlinarith

/-- **The midpoint defect is quadratically small**: `‖d(w)‖ ≤ 3/(8‖w + ½‖²)` for `w` in the slit
plane with `‖w + ½‖ ≥ 1`. With `u = w + ½` and `ε = 1/(2u)`,
`d(w) = −ε²/2 + u((1 + ε)R₊ − (1 − ε)R₋)`, where `R±` are the cubic Taylor remainders of
`log (1 ± ε)`. -/
theorem norm_stirD_le {w : ℂ} (hw : w ∈ slitPlane) (hu : 1 ≤ ‖w + 1 / 2‖) :
    ‖stirD w‖ ≤ 3 / 8 / ‖w + 1 / 2‖ ^ 2 := by
  set u := w + 1 / 2 with hu_def
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; linarith
  have huslit : u ∈ slitPlane := by
    rcases mem_slitPlane_iff.1 hw with h | h
    · exact mem_slitPlane_iff.2 (Or.inl (by rw [hu_def]; simp; linarith))
    · exact mem_slitPlane_iff.2 (Or.inr (by rw [hu_def]; simpa using h))
  set ε := (2 * u)⁻¹ with hε
  have hεu : ε * u = 1 / 2 := by rw [hε]; field_simp
  have hεn : ‖ε‖ * ‖u‖ = 1 / 2 := by rw [← norm_mul, hεu]; norm_num
  have hεs : ‖ε‖ ≤ 1 / 2 := by
    have : ‖ε‖ = 1 / 2 / ‖u‖ := by rw [eq_div_iff (by positivity)]; exact hεn
    rw [this, div_le_iff₀ (by positivity)]; linarith
  have hεn' : ‖-ε‖ ≤ 1 / 2 := by rwa [norm_neg]
  -- the two logarithms
  have hlog1 : log (w + 1) = log u + log (1 + ε) := by
    rw [show w + 1 = u + 1 / 2 by rw [hu_def]; ring]; exact log_add_half huslit
  have hlog0 : log w = log u + log (1 - ε) := log_sub_half hw hu
  have hRpb : ‖log (1 + ε) - (ε - ε ^ 2 / 2)‖ ≤ 2 / 3 * ‖ε‖ ^ 3 := norm_log_sub_taylor2_le hεs
  have hRmb : ‖log (1 - ε) - (-ε - ε ^ 2 / 2)‖ ≤ 2 / 3 * ‖ε‖ ^ 3 := by
    have := norm_log_sub_taylor2_le hεn'
    rwa [norm_neg, ← sub_eq_add_neg, neg_sq] at this
  set Rp := log (1 + ε) - (ε - ε ^ 2 / 2) with hRp
  set Rm := log (1 - ε) - (-ε - ε ^ 2 / 2) with hRm
  have hform : stirD w = -ε ^ 2 / 2 + u * ((1 + ε) * Rp - (1 - ε) * Rm) := by
    simp only [stirD, stirF]
    rw [show w + 1 / 2 = u from hu_def.symm, hlog1, hlog0, hRp, hRm]
    linear_combination (-(log (1 + ε) - log (1 - ε))) * hu_def +
      (2 - ε ^ 2 - log (1 + ε) - log (1 - ε)) * hεu
  rw [hform]
  have h1 : ‖1 + ε‖ ≤ 3 / 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have h2 : ‖1 - ε‖ ≤ 3 / 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hb : ‖-ε ^ 2 / 2 + u * ((1 + ε) * Rp - (1 - ε) * Rm)‖ ≤
      ‖ε‖ ^ 2 / 2 + ‖u‖ * (3 / 2 * (2 / 3 * ‖ε‖ ^ 3) + 3 / 2 * (2 / 3 * ‖ε‖ ^ 3)) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, norm_neg, norm_pow]; norm_num
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ?_ ?_))
        (norm_nonneg _)
      · rw [norm_mul]; exact mul_le_mul h1 hRpb (norm_nonneg _) (by norm_num)
      · rw [norm_mul]; exact mul_le_mul h2 hRmb (norm_nonneg _) (by norm_num)
  refine hb.trans (le_of_eq ?_)
  have hu' : ‖ε‖ = 1 / 2 / ‖u‖ := by rw [eq_div_iff (by positivity)]; exact hεn
  rw [hu']
  field_simp
  ring

/-! ## Sector and summation bounds -/

/-- **Sector bound**: if `Re w ≥ −c‖w‖` with `c ≥ 0`, then `‖w + t‖² ≥ (1 − c)(‖w‖ + t)²/2` for
real `t ≥ 0`. The gap is `(1 + c)(‖w‖ − t)²/2 ≥ 0`. -/
lemma sq_norm_add_ofReal_ge {w : ℂ} {c t : ℝ} (hc : 0 ≤ c) (hw : -c * ‖w‖ ≤ w.re)
    (ht : 0 ≤ t) : (1 - c) * (‖w‖ + t) ^ 2 / 2 ≤ ‖w + t‖ ^ 2 := by
  have h1 : ‖w + t‖ ^ 2 = ‖w‖ ^ 2 + 2 * t * w.re + t ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]; simp; ring
  rw [h1]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + c) (sq_nonneg (‖w‖ - t)),
    mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ 2 * t)]

/-- Telescoping bound `Σ_{n<N} 1/(a + n)² ≤ 1/(a − ½) − 1/(a + N − ½)` for `a > ½`, from
`1/x² ≤ 1/(x − ½) − 1/(x + ½)`. -/
lemma sum_range_inv_sq_le {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (a + n) ^ 2 ≤ 1 / (a - 1 / 2) - 1 / (a + N - 1 / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN := N.cast_nonneg (α := ℝ)
    have h1 : 0 < a + N - 1 / 2 := by linarith
    have key : 1 / (a + N) ^ 2 ≤ 1 / (a + N - 1 / 2) - 1 / (a + (N + 1 : ℕ) - 1 / 2) := by
      push_cast
      rw [div_sub_div _ _ h1.ne' (by linarith),
        div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos h1 (by linarith))]
      nlinarith
    linarith

/-- In the sector `Re w ≥ −c‖w‖` (`0 ≤ c < 1`) with `‖w‖² ≥ 2/(1 − c)`, every `w + n` lies in the
slit plane, `‖w + n + ½‖ ≥ 1`, and `‖w + n + ½‖² ≥ (1 − c)(‖w‖ + ½ + n)²/2`. -/
lemma sector_shift {w : ℂ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hw : -c * ‖w‖ ≤ w.re)
    (hR : 2 / (1 - c) ≤ ‖w‖ ^ 2) (n : ℕ) :
    w + n ∈ slitPlane ∧ (1 - c) * (‖w‖ + 1 / 2 + n) ^ 2 / 2 ≤ ‖w + n + 1 / 2‖ ^ 2 ∧
      1 ≤ ‖w + n + 1 / 2‖ := by
  have hR' : 2 ≤ ‖w‖ ^ 2 * (1 - c) := (div_le_iff₀ (by linarith)).1 hR
  have hpos : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · rw [← h] at hR'; norm_num at hR'
  have hn := n.cast_nonneg (α := ℝ)
  have hsq : (1 - c) * (‖w‖ + 1 / 2 + n) ^ 2 / 2 ≤ ‖w + n + 1 / 2‖ ^ 2 := by
    have h := sq_norm_add_ofReal_ge hc0 hw (t := (n : ℝ) + 1 / 2) (by positivity)
    have e : w + (((n : ℝ) + 1 / 2 : ℝ) : ℂ) = w + n + 1 / 2 := by push_cast; ring
    have e2 : ‖w‖ + ((n : ℝ) + 1 / 2) = ‖w‖ + 1 / 2 + n := by ring
    rw [e, e2] at h; exact h
  refine ⟨?_, hsq, ?_⟩
  · rw [mem_slitPlane_iff]
    by_cases him : w.im = 0
    · left
      have habs : |w.re| = ‖w‖ := abs_re_eq_norm.2 him
      have hre : 0 < w.re := by
        rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, hneg⟩
        · rw [h] at habs; linarith
        · rw [h] at habs; nlinarith
      simp; linarith
    · right; simpa using him
  · have h2 : 1 ≤ ‖w + n + 1 / 2‖ ^ 2 := by
      have : ‖w‖ ^ 2 ≤ (‖w‖ + 1 / 2 + n) ^ 2 := by nlinarith
      nlinarith
    nlinarith [norm_nonneg (w + n + 1 / 2)]

/-- **The Stirling remainder is `O(1/‖w‖)` on sectors**: if `Re w ≥ −c‖w‖` with `0 ≤ c < 1` and
`‖w‖² ≥ 2/(1 − c)`, the series `Σ d(w + n)` converges and `‖μ(w)‖ ≤ 3/(4(1 − c)‖w‖)`. -/
theorem norm_stirMu_le {w : ℂ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hw : -c * ‖w‖ ≤ w.re)
    (hR : 2 / (1 - c) ≤ ‖w‖ ^ 2) :
    Summable (fun n : ℕ => stirD (w + n)) ∧ ‖stirMu w‖ ≤ 3 / 4 / ((1 - c) * ‖w‖) := by
  have hR' : 2 ≤ ‖w‖ ^ 2 * (1 - c) := (div_le_iff₀ (by linarith)).1 hR
  have hpos : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · rw [← h] at hR'; norm_num at hR'
  have ha : (1 : ℝ) / 2 < ‖w‖ + 1 / 2 := by linarith
  have hg0 : ∀ n : ℕ, 0 ≤ 1 / (‖w‖ + 1 / 2 + n) ^ 2 := fun n => by positivity
  have hgS : ∀ N : ℕ, ∑ n ∈ Finset.range N, 1 / (‖w‖ + 1 / 2 + n) ^ 2 ≤ 1 / ‖w‖ := fun N => by
    refine (sum_range_inv_sq_le ha N).trans ?_
    have : 0 ≤ 1 / (‖w‖ + 1 / 2 + N - 1 / 2) := by
      have := N.cast_nonneg (α := ℝ); exact div_nonneg zero_le_one (by linarith)
    rw [show ‖w‖ + 1 / 2 - 1 / 2 = ‖w‖ by ring]; linarith
  have hsum : Summable (fun n : ℕ => 1 / (‖w‖ + 1 / 2 + n) ^ 2) := summable_of_sum_range_le hg0 hgS
  have htsum : ∑' n : ℕ, 1 / (‖w‖ + 1 / 2 + n) ^ 2 ≤ 1 / ‖w‖ := Real.tsum_le_of_sum_range_le hg0 hgS
  set K : ℝ := 3 / 4 / (1 - c) with hK
  have hK0 : 0 ≤ K := div_nonneg (by norm_num) (by linarith)
  have hb : ∀ n : ℕ, ‖stirD (w + n)‖ ≤ K * (1 / (‖w‖ + 1 / 2 + n) ^ 2) := fun n => by
    obtain ⟨hs, hsq, h1⟩ := sector_shift hc0 hc1 hw hR n
    refine (norm_stirD_le hs h1).trans ?_
    have hX : 0 < (‖w‖ + 1 / 2 + n) ^ 2 := by positivity
    calc 3 / 8 / ‖w + n + 1 / 2‖ ^ 2 ≤ 3 / 8 / ((1 - c) * (‖w‖ + 1 / 2 + n) ^ 2 / 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by have := mul_pos (by linarith : 0 < 1 - c) hX; positivity) hsq
      _ = K * (1 / (‖w‖ + 1 / 2 + n) ^ 2) := by
          rw [hK]; field_simp; ring
  refine ⟨(hsum.mul_left K).of_norm_bounded hb, ?_⟩
  refine (tsum_of_norm_bounded (hsum.mul_left K).hasSum hb).trans ?_
  rw [tsum_mul_left]
  calc K * ∑' n : ℕ, 1 / (‖w‖ + 1 / 2 + n) ^ 2 ≤ K * (1 / ‖w‖) :=
        mul_le_mul_of_nonneg_left htsum hK0
    _ = 3 / 4 / ((1 - c) * ‖w‖) := by rw [hK]; field_simp

/-- The series `Σ d(w + n)` converges for every `w`: some shift `w + N` lies in the sector
`Re ≥ 0` far from the origin. -/
theorem summable_stirD (w : ℂ) : Summable (fun n : ℕ => stirD (w + n)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖w‖ + 2 ≤ N := ⟨⌈‖w‖ + 2⌉₊, Nat.le_ceil _⟩
  have hre1 : -‖w‖ ≤ w.re := by linarith [neg_abs_le w.re, abs_re_le_norm w]
  have hre : 0 ≤ (w + N).re := by simp; linarith
  have hnorm : 2 ≤ ‖w + N‖ := by
    have := re_le_norm (w + N); simp at this ⊢; linarith
  have h := (norm_stirMu_le (w := w + N) (c := 0) le_rfl one_pos (by simpa using hre)
    (by norm_num; nlinarith)).1
  rw [← summable_nat_add_iff N]
  exact h.congr fun n => by congr 1; push_cast; ring

/-- **Shift identity** `μ(w) = d(w) + μ(w + 1)`. -/
theorem stirMu_eq_add (w : ℂ) : stirMu w = stirD w + stirMu (w + 1) := by
  rw [stirMu, (summable_stirD w).tsum_eq_zero_add, stirMu]
  congr 1
  · simp
  · exact tsum_congr fun n => by congr 1; push_cast; ring

/-! ## The functional equation -/

/-- `w + n + ½ ≠ 0` for `w` in the slit plane. -/
lemma add_nat_add_half_ne_zero {w : ℂ} (hw : w ∈ slitPlane) (n : ℕ) : w + n + 1 / 2 ≠ 0 := by
  intro h
  rcases mem_slitPlane_iff.1 hw with hr | hi
  · have := congrArg Complex.re h; simp at this; linarith [n.cast_nonneg (α := ℝ)]
  · have := congrArg Complex.im h; simp at this; exact hi this

/-- `f(w + 1) + μ(w + 1) = f(w) + μ(w) + log(w + ½)`. -/
lemma stirF_add_stirMu_succ (w : ℂ) :
    stirF (w + 1) + stirMu (w + 1) = stirF w + stirMu w + log (w + 1 / 2) := by
  rw [stirMu_eq_add w, stirD]; ring

/-- **Functional equation**: `exp(f + μ)` is multiplied by `w + ½` under `w ↦ w + 1`, like
`Γ(w + ½)`. -/
lemma exp_stir_succ {w : ℂ} (hw : w + 1 / 2 ≠ 0) :
    exp (stirF (w + 1) + stirMu (w + 1)) = (w + 1 / 2) * exp (stirF w + stirMu w) := by
  rw [stirF_add_stirMu_succ, exp_add, exp_log hw, mul_comm]

/-! ## The limit along `w + N` -/

/-- `Γ(s + n) = Γ(s) ∏_{j<n} (s + j)` when no `s + j` vanishes. -/
lemma Gamma_add_nat_eq_prod {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) (n : ℕ) :
    Gamma (s + n) = Gamma s * ∏ j ∈ Finset.range n, (s + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ, ← add_assoc,
      Gamma_add_one _ (hs n), mul_comm]

/-- Euler's limit in the form `Γ(s + N + 1)/(N^s N!) → 1`. -/
lemma tendsto_Gamma_add_nat_div {s : ℂ} (hs : ∀ j : ℕ, s + j ≠ 0) :
    Tendsto (fun N : ℕ => Gamma (s + N + 1) / ((N : ℂ) ^ s * N !)) atTop (𝓝 1) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero fun m h => hs m (by rw [h]; ring)
  have h := (tendsto_const_nhds (x := Gamma s)).div (GammaSeq_tendsto_Gamma s) hG
  rw [div_self hG] at h
  refine h.congr fun N => ?_
  rw [Pi.div_apply, Complex.GammaSeq, show s + N + 1 = s + ((N + 1 : ℕ) : ℂ) by push_cast; ring,
    Gamma_add_nat_eq_prod hs, div_div_eq_mul_div]

/-- The normalised factorial `q(N) = N!/(√(2π) e^{(N + ½) log N − N})`. -/
noncomputable def stirQ (N : ℕ) : ℝ :=
  N ! / (√(2 * Real.pi) * Real.exp ((N + 1 / 2) * Real.log N - N))

lemma stirQ_pos (N : ℕ) : 0 < stirQ N := by
  unfold stirQ; have := N.factorial_pos; positivity

/-- `q(N) = stirlingSeq N / √π` for `N ≥ 1`. -/
lemma stirQ_eq {N : ℕ} (hN : 1 ≤ N) : stirQ N = Stirling.stirlingSeq N / √Real.pi := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : √(N : ℝ) = Real.exp (Real.log N / 2) := by
    have h2 : Real.exp (Real.log N / 2) * Real.exp (Real.log N / 2) = N := by
      rw [← Real.exp_add, show Real.log N / 2 + Real.log N / 2 = Real.log N by ring,
        Real.exp_log hN0]
    conv_lhs => rw [← h2]
    exact Real.sqrt_mul_self (Real.exp_pos _).le
  have hpow : ((N : ℝ) / Real.exp 1) ^ N = Real.exp (N * Real.log N - N) := by
    rw [show (N * Real.log N - N : ℝ) = N * (Real.log N - 1) by ring, Real.exp_nat_mul,
      Real.exp_sub, Real.exp_log hN0]
  have h1 : Real.exp ((N + 1 / 2) * Real.log N - N) = √(N : ℝ) * ((N : ℝ) / Real.exp 1) ^ N := by
    rw [hs, hpow, ← Real.exp_add]; congr 1; ring
  rw [stirQ, Stirling.stirlingSeq, h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) N]
  ring

/-- `q(N) → 1`: the real Stirling formula. -/
lemma tendsto_stirQ : Tendsto stirQ atTop (𝓝 1) := by
  have h := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const √Real.pi
  rw [div_self (Real.sqrt_ne_zero'.2 Real.pi_pos)] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN using (stirQ_eq hN).symm

/-- `N! = q(N) √(2π) e^{(N + ½) log N − N}` in `ℂ`. -/
lemma factorial_eq_stirQ (N : ℕ) :
    ((N ! : ℕ) : ℂ) = stirQ N * ((√(2 * Real.pi) : ℝ) : ℂ) *
      exp ((N + 1 / 2) * log N - N) := by
  have hD : √(2 * Real.pi) * Real.exp ((N + 1 / 2) * Real.log N - N) ≠ 0 := by positivity
  have hR : (N ! : ℝ) = stirQ N * (√(2 * Real.pi) * Real.exp ((N + 1 / 2) * Real.log N - N)) := by
    rw [stirQ, div_mul_cancel₀ _ hD]
  have := congrArg (fun x : ℝ => (x : ℂ)) hR
  push_cast at this
  rw [this]; ring

/-- An algebraic rearrangement used in `tendsto_Gamma_div_stir`. -/
lemma stir_alg {G P q c e1 e2 e3 e4 N : ℂ} (hP : P ≠ 0) (hq : q ≠ 0) (hc : c ≠ 0)
    (he1 : e1 ≠ 0) (he2 : e2 ≠ 0) :
    P * G / (e1 * (q * c * e2)) * q * e3 * (N / P * e4) = G / c * (N * (e3 * e4 / (e1 * e2))) := by
  field_simp

/-- **Stirling along `w + N`**: `Γ(w + N + ½)/(√(2π) exp(f(w + N) + μ(w + N))) → 1`. -/
lemma tendsto_Gamma_div_stir {w : ℂ} (hw : w ∈ slitPlane) :
    Tendsto (fun N : ℕ => Gamma (w + N + 1 / 2) /
      (((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF (w + N) + stirMu (w + N)))) atTop (𝓝 1) := by
  have hs : ∀ j : ℕ, w + 1 / 2 + j ≠ 0 := fun j => by
    rw [show w + 1 / 2 + j = w + j + 1 / 2 by ring]; exact add_nat_add_half_ne_zero hw j
  have hA := tendsto_Gamma_add_nat_div hs
  have hQ : Tendsto (fun N : ℕ => ((stirQ N : ℝ) : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_stirQ.ofReal
  have hre1 : -‖w‖ ≤ w.re := by linarith [neg_abs_le w.re, abs_re_le_norm w]
  have hM : Tendsto (fun N : ℕ => exp (-stirMu (w + N))) atTop (𝓝 1) := by
    have h0 : Tendsto (fun N : ℕ => stirMu (w + N)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := (3 / 4 : ℝ))).div_atTop
        (tendsto_atTop_add_const_right _ (-‖w‖) tendsto_natCast_atTop_atTop))
      filter_upwards [eventually_ge_atTop ⌈‖w‖ + 2⌉₊] with N hN
      have hN' : ‖w‖ + 2 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
      have hre : 0 ≤ (w + N).re := by simp; linarith
      have hnorm : (N : ℝ) + -‖w‖ ≤ ‖w + N‖ := by
        have := re_le_norm (w + N); simp at this; linarith
      have h := (norm_stirMu_le (w := w + N) (c := 0) le_rfl one_pos (by simpa using hre)
        (by norm_num; nlinarith)).2
      refine h.trans ?_
      simp only [sub_zero, one_mul]
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hnorm
    have h0' := h0.neg
    rw [neg_zero] at h0'
    have h3 := (continuous_exp.tendsto 0).comp h0'
    rw [exp_zero] at h3
    exact h3
  have hZ : Tendsto (fun N : ℕ => (N : ℂ) / (w + N + 1 / 2) *
      exp (w - (w + N) * log (1 + w / N))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℂ) / (w + N + 1 / 2)) atTop (𝓝 1) := by
      have h := ((tendsto_const_div_atTop_nhds_zero_nat (w + 1 / 2 : ℂ)).const_add 1).inv₀
        (by norm_num)
      rw [add_zero, inv_one] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      have e : (1 + (w + 1 / 2) / N : ℂ) = (w + N + 1 / 2) / N := by
        rw [eq_div_iff hN0, add_mul, div_mul_cancel₀ _ hN0]; ring
      rw [e, inv_div]
    have h2 : Tendsto (fun N : ℕ => exp (w - (w + N) * log (1 + w / N))) atTop (𝓝 1) := by
      have hl : Tendsto (fun N : ℕ => (N : ℂ) * log (1 + w / N)) atTop (𝓝 w) := by
        refine tendsto_nat_mul_log_one_add_of_tendsto (tendsto_const_nhds.congr' ?_)
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        field_simp
      have hl2 : Tendsto (fun N : ℕ => w * log (1 + w / N)) atTop (𝓝 0) := by
        have h := (tendsto_const_div_atTop_nhds_zero_nat w).const_add 1
        rw [add_zero] at h
        have := ((continuousAt_clog (by simp : (1 : ℂ) ∈ slitPlane)).tendsto.comp h).const_mul w
        simpa using this
      have h3 := (tendsto_const_nhds (x := w)).sub (hl.add hl2)
      rw [add_zero, sub_self] at h3
      have := (continuous_exp.tendsto 0).comp h3
      rw [exp_zero] at this
      refine this.congr fun N => ?_
      simp only [Function.comp]; congr 1; ring
    simpa using h1.mul h2
  have hall := ((hA.mul hQ).mul hM).mul hZ
  rw [one_mul, one_mul, one_mul] at hall
  refine hall.congr' ?_
  filter_upwards [eventually_ge_atTop (⌈‖w‖⌉₊ + 1)] with N hN
  have hN1 : 1 ≤ N := by omega
  have hNw : ‖w‖ < N := by
    have := Nat.le_ceil ‖w‖
    have h' : ((⌈‖w‖⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h'; linarith
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hP : w + N + 1 / 2 ≠ 0 := add_nat_add_half_ne_zero hw N
  have hsmall : ‖w / N‖ < 1 := by
    rw [norm_div, Complex.norm_natCast, div_lt_one (Nat.cast_pos.2 (by omega))]; exact hNw
  have h1w : 1 + w / N ≠ 0 := by
    intro h; have : w / N = -1 := by linear_combination h
    rw [this, norm_neg, norm_one] at hsmall; exact lt_irrefl _ hsmall
  have hlog : log (w + N) = log N + log (1 + w / N) := by
    have e : w + (N : ℂ) = ((N : ℝ) : ℂ) * (1 + w / N) := by
      push_cast; field_simp; ring
    rw [e, log_ofReal_mul (Nat.cast_pos.2 (by omega)) h1w, natCast_log]
  have hGam : Gamma (w + 1 / 2 + N + 1) = (w + N + 1 / 2) * Gamma (w + N + 1 / 2) := by
    rw [show w + 1 / 2 + N + 1 = (w + N + 1 / 2) + 1 by ring, Gamma_add_one _ hP]
  have hq : ((stirQ N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (stirQ_pos N).ne'
  have hc : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < √(2 * Real.pi)).ne'
  rw [hGam, cpow_def_of_ne_zero hN0, factorial_eq_stirQ N,
    stir_alg hP hq hc (exp_ne_zero _) (exp_ne_zero _)]
  have hE : (N : ℂ) * (exp (-stirMu (w + N)) * exp (w - (w + N) * log (1 + w / N)) /
      (exp (log N * (w + 1 / 2)) * exp ((N + 1 / 2) * log N - N))) =
      (exp (stirF (w + N) + stirMu (w + N)))⁻¹ := by
    rw [← exp_add, ← exp_add, ← exp_sub, ← exp_neg]
    calc (N : ℂ) * exp (-stirMu (w + N) + (w - (w + N) * log (1 + w / N)) -
          (log N * (w + 1 / 2) + ((N + 1 / 2) * log N - N)))
        = exp (log N) * exp (-stirMu (w + N) + (w - (w + N) * log (1 + w / N)) -
          (log N * (w + 1 / 2) + ((N + 1 / 2) * log N - N))) := by rw [exp_log hN0]
      _ = exp (-(stirF (w + N) + stirMu (w + N))) := by
          rw [← exp_add]; congr 1; simp only [stirF]; rw [hlog]; ring
  rw [hE]; ring

/-- **Complex Stirling formula, midpoint form**: for `w` in the slit plane,
`Γ(w + ½) = √(2π) · exp(w log w − w + μ(w))`, with `μ(w) = Σₙ d(w + n)` bounded by
`3/(4(1 − c)‖w‖)` on the sector `Re w ≥ −c‖w‖` (`norm_stirMu_le`). -/
theorem Gamma_half_add {w : ℂ} (hw : w ∈ slitPlane) :
    Gamma (w + 1 / 2) = ((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF w + stirMu w) := by
  have hc : ((√(2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < √(2 * Real.pi)).ne'
  let R : ℕ → ℂ := fun N => Gamma (w + N + 1 / 2) /
    (((√(2 * Real.pi) : ℝ) : ℂ) * exp (stirF (w + N) + stirMu (w + N)))
  have hR : ∀ N, R N = R 0 := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [← ih]
      have hP := add_nat_add_half_ne_zero hw N
      simp only [R]
      rw [show w + ((N + 1 : ℕ) : ℂ) = (w + N) + 1 by push_cast; ring,
        show w + N + 1 + 1 / 2 = (w + N + 1 / 2) + 1 by ring, Gamma_add_one _ hP,
        exp_stir_succ hP, mul_left_comm, mul_div_mul_left _ _ hP]
  have h1 : Tendsto R atTop (𝓝 (R 0)) := (tendsto_const_nhds (x := R 0)).congr fun N => (hR N).symm
  have h0 : R 0 = 1 := tendsto_nhds_unique h1 (tendsto_Gamma_div_stir hw)
  simp only [R, Nat.cast_zero, add_zero] at h0
  rwa [div_eq_one_iff_eq (mul_ne_zero hc (exp_ne_zero _))] at h0

end Lightlike.Asymptotics
