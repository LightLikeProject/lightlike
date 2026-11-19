import Lightlike.FieldTheory.Borel.Contour
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The Borel transform as a vertical-line integral

The hypotheses of the Nevanlinna–Sokal theorem (Benedetti–Gurau–Keppler–Lettera, arXiv:2210.14776, Theorem 1,
eq. (2.4) with `β = 0`, p. 5; Sokal's theorem): `f` analytic in the disk `C_R = {Re z⁻¹ > 1/R}` with
`|f(z) - ∑_{k<q} a_k z^k| ≤ K q! ρ^{-q} |z|^q` for all `q` and `z ∈ C_R` (`SokalHyp`). Then (eq. (B.1), p. 24)
`|a_q| ≤ K q! ρ^{-q}` (`SokalHyp.norm_coeff_le`), so the Borel transform `B(t) = ∑ a_k t^k/k!` converges for `|t| < ρ`
(`SokalHyp.hasSum_borelT`), and (eqs. (B.4)-(B.5), p. 25) for `0 < x < ρ` the function `b₀(x)` of (B.3) is `B(x)`
(`SokalHyp.borelZero_eq_borelT`): along the line `Re w = (n+1)/x` the terms of the expansion of `f` give the partial
sums of `B(x)` by Hankel's formula, and the remainder is at most `(K/2) e √(n+1) (x/ρ)^{n+1}` by Stirling's bound.

## Main results

* `SokalHyp`: the hypotheses of the Nevanlinna–Sokal theorem.
* `SokalHyp.norm_coeff_le`: `|a_q| ≤ K q! ρ^{-q}`.
* `SokalHyp.borelZero_eq_borelT`: `b₀(x) = B(x)` for `0 < x < ρ`.
-/

open MeasureTheory Set Filter Complex Finset
open scoped Topology Real Nat

namespace Lightlike.FieldTheory.Borel

/-- **The hypotheses of the Nevanlinna–Sokal theorem** (Benedetti–Gurau–Keppler–Lettera, eq. (2.4) with `β = 0`):
`f` is analytic in `C_R = {Re z⁻¹ > 1/R}` and `|f(z) - ∑_{k<q} a_k z^k| ≤ K q! ρ^{-q} |z|^q` for all `q` and
`z ∈ C_R`. -/
structure SokalHyp (f : ℂ → ℂ) (a : ℕ → ℂ) (R K ρ : ℝ) : Prop where
  R_pos : 0 < R
  K_nonneg : 0 ≤ K
  ρ_pos : 0 < ρ
  analytic : DifferentiableOn ℂ f (diskC R)
  rem : ∀ q : ℕ, ∀ z ∈ diskC R, ‖f z - ∑ k ∈ range q, a k * z ^ k‖ ≤ K * q ! / ρ ^ q * ‖z‖ ^ q

variable {f : ℂ → ℂ} {a : ℕ → ℂ} {R K ρ : ℝ}

lemma ofReal_mem_diskC {t : ℝ} (ht : 0 < t) (htR : t < R) : (t : ℂ) ∈ diskC R := by
  show 1 / R < ((t : ℂ)⁻¹).re
  rw [← ofReal_inv, ofReal_re, ← one_div]
  exact one_div_lt_one_div_of_lt ht htR

/-- **The coefficient bound** (Benedetti–Gurau–Keppler–Lettera, eq. (B.1)): `|a_q| ≤ K q! ρ^{-q}`. -/
theorem SokalHyp.norm_coeff_le (h : SokalHyp f a R K ρ) (q : ℕ) : ‖a q‖ ≤ K * q ! / ρ ^ q := by
  have key : ∀ t : ℝ, 0 < t → t < R → ‖a q‖ ≤ K * q ! / ρ ^ q + K * (q + 1) ! / ρ ^ (q + 1) * t := by
    intro t ht htR
    have hz := ofReal_mem_diskC ht htR
    have h1 := h.rem q _ hz
    have h2 := h.rem (q + 1) _ hz
    rw [Complex.norm_real, Real.norm_of_nonneg ht.le] at h1 h2
    have e : a q * (t : ℂ) ^ q = (f t - ∑ k ∈ range q, a k * (t : ℂ) ^ k) -
        (f t - ∑ k ∈ range (q + 1), a k * (t : ℂ) ^ k) := by rw [sum_range_succ]; ring
    have hn : ‖a q‖ * t ^ q ≤ K * q ! / ρ ^ q * t ^ q + K * (q + 1) ! / ρ ^ (q + 1) * t ^ (q + 1) := by
      calc ‖a q‖ * t ^ q = ‖a q * (t : ℂ) ^ q‖ := by
            rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
        _ ≤ ‖f t - ∑ k ∈ range q, a k * (t : ℂ) ^ k‖ + ‖f t - ∑ k ∈ range (q + 1), a k * (t : ℂ) ^ k‖ := by
            rw [e]; exact norm_sub_le _ _
        _ ≤ _ := add_le_add h1 h2
    have htq : 0 < t ^ q := pow_pos ht q
    rw [show K * (q + 1) ! / ρ ^ (q + 1) * t ^ (q + 1) = K * (q + 1) ! / ρ ^ (q + 1) * t * t ^ q by ring,
      ← add_mul] at hn
    exact le_of_mul_le_mul_right hn htq
  have hlim : Tendsto (fun t : ℝ => K * q ! / ρ ^ q + K * (q + 1) ! / ρ ^ (q + 1) * t) (𝓝[>] 0)
      (𝓝 (K * q ! / ρ ^ q)) := by
    have hc : Continuous fun t : ℝ => K * q ! / ρ ^ q + K * (q + 1) ! / ρ ^ (q + 1) * t := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT h.R_pos] with t ht using key t ht.1 ht.2

/-- **The Borel transform** `B(t) = ∑_k a_k t^k/k!`. -/
noncomputable def borelT (a : ℕ → ℂ) (t : ℂ) : ℂ := ∑' k, a k * t ^ k / (k ! : ℂ)

lemma SokalHyp.norm_term_le (h : SokalHyp f a R K ρ) (t : ℂ) (k : ℕ) :
    ‖a k * t ^ k / (k ! : ℂ)‖ ≤ K * (‖t‖ / ρ) ^ k := by
  have hk : (0 : ℝ) < k ! := by positivity
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow]
  calc ‖a k‖ * ‖t‖ ^ k / k ! ≤ K * k ! / ρ ^ k * ‖t‖ ^ k / k ! := by
        gcongr; exact h.norm_coeff_le k
    _ = K * (‖t‖ ^ k / ρ ^ k) := by field_simp

/-- **The Borel transform converges** for `|t| < ρ` (Benedetti–Gurau–Keppler–Lettera, p. 25). -/
theorem SokalHyp.hasSum_borelT (h : SokalHyp f a R K ρ) {t : ℂ} (ht : ‖t‖ < ρ) :
    HasSum (fun k => a k * t ^ k / (k ! : ℂ)) (borelT a t) := by
  have hr : ‖t‖ / ρ < 1 := (div_lt_one h.ρ_pos).2 ht
  have hs : Summable fun k : ℕ => K * (‖t‖ / ρ) ^ k :=
    (summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) h.ρ_pos.le) hr).mul_left K
  exact (Summable.of_norm_bounded hs (h.norm_term_le t)).hasSum

/-- Hankel's formula with the line parametrized as `w = c + iy`: `∫ e^{x(c+iy)} (c+iy)^{-(k+1)} dy = 2π x^k/k!`. -/
lemma hankel_vertical_y {k : ℕ} (hk : 1 ≤ k) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1) = 2 * π * ((x ^ k / k ! : ℝ) : ℂ) := by
  have h := hankel_vertical hk hx hc
  have e := Measure.integral_comp_mul_left
    (fun y : ℝ => cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1)) (2 * π)
  have hv : (fun ξ : ℝ => cexp (x * vline c ξ) / vline c ξ ^ (k + 1)) =
      fun ξ : ℝ => (fun y : ℝ => cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1)) (2 * π * ξ) := by
    funext ξ; simp only [vline]; push_cast; ring_nf
  rw [hv, e, abs_of_pos (by positivity)] at h
  have h2 : ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1) =
      (2 * π : ℝ) • ((2 * π)⁻¹ : ℝ) • ∫ y : ℝ, cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1) := by
    rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  rw [h2, h, Complex.real_smul]
  push_cast
  ring

lemma integral_inv_sq_add {c : ℝ} (hc : 0 < c) : ∫ y : ℝ, (c ^ 2 + y ^ 2)⁻¹ = π / c := by
  have e : (fun y : ℝ => (c ^ 2 + y ^ 2)⁻¹) = fun y => (c ^ 2)⁻¹ * (1 + (c⁻¹ * y) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [e, integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.2 hc)]
  field_simp

lemma norm_cexp_mul_vertical (x c y : ℝ) : ‖cexp (x * ((c : ℂ) + y * I))‖ = Real.exp (x * c) := by
  rw [Complex.norm_exp]; simp

lemma pow_le_norm_vertical {c : ℝ} (hc : 0 ≤ c) (y : ℝ) (n : ℕ) :
    c ^ n * ‖(c : ℂ) + y * I‖ ^ 2 ≤ ‖(c : ℂ) + y * I‖ ^ (n + 2) := by
  have h : c ≤ ‖(c : ℂ) + y * I‖ := by
    have := Complex.abs_re_le_norm ((c : ℂ) + y * I)
    simpa [abs_of_nonneg hc] using this
  rw [pow_add]
  gcongr

/-- **The remainder of `b₀`** (Benedetti–Gurau–Keppler–Lettera, eqs. (B.4)-(B.5)): along the line `Re w = c`,
`|b₀(x) - ∑_{k ≤ n} a_k x^k/k!| ≤ (K/2) e^{xc} (n+1)!/(ρc)^{n+1}`. -/
theorem SokalHyp.norm_borelZero_sub_sum_le (h : SokalHyp f a R K ρ) {x c : ℝ} (hx : 0 < x) (hc : 1 / R < c)
    (n : ℕ) : ‖borelZero f (a 0) x c - ∑ k ∈ range (n + 1), a k * (x : ℂ) ^ k / (k ! : ℂ)‖ ≤
      K / 2 * Real.exp (x * c) * (n + 1) ! / (ρ * c) ^ (n + 1) := by
  have hR := h.R_pos
  have hρ := h.ρ_pos
  have hc0 : 0 < c := (one_div_pos.2 hR).trans hc
  have hwre : ∀ y : ℝ, 1 / R < ((c : ℂ) + y * I).re := fun y => by simpa using hc
  have hw0 : ∀ y : ℝ, (c : ℂ) + y * I ≠ 0 := fun y => ne_zero_of_re_gt hR (hwre y)
  have hwn : ∀ y : ℝ, 0 < ‖(c : ℂ) + y * I‖ := fun y => norm_pos_iff.2 (hw0 y)
  have hcont : Continuous fun y : ℝ => (c : ℂ) + y * I := by fun_prop
  -- the bound `|f(z) - a₀| ≤ (K/ρ)|z|` (`q = 1`)
  have hM : ∀ z ∈ diskC R, ‖f z - a 0‖ ≤ K * 1 ! / ρ ^ 1 * ‖z‖ := fun z hz => by
    simpa using h.rem 1 z hz
  -- the integrand and its pieces
  set G : ℝ → ℂ := fun y => borelIntegrand f (a 0) x ((c : ℂ) + y * I)
  set T : ℕ → ℝ → ℂ := fun k y => a (k + 1) * (cexp (x * ((c : ℂ) + y * I)) / ((c : ℂ) + y * I) ^ (k + 1 + 1))
  set E : ℝ → ℂ := fun y => cexp (x * ((c : ℂ) + y * I)) *
    (f ((c : ℂ) + y * I)⁻¹ - ∑ j ∈ range (n + 1), a j * ((c : ℂ) + y * I)⁻¹ ^ j) / ((c : ℂ) + y * I)
  have hsplit : ∀ y, G y = (∑ k ∈ range n, T k y) + E y := by
    intro y
    have e1 : f ((c : ℂ) + y * I)⁻¹ - a 0 = (f ((c : ℂ) + y * I)⁻¹ -
        ∑ j ∈ range (n + 1), a j * ((c : ℂ) + y * I)⁻¹ ^ j) +
        ∑ k ∈ range n, a (k + 1) * ((c : ℂ) + y * I)⁻¹ ^ (k + 1) := by
      rw [sum_range_succ', pow_zero, mul_one]; ring
    simp only [G, E, T, borelIntegrand]
    rw [e1, mul_add, add_div, add_comm, Finset.mul_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have := hw0 y
    rw [inv_pow]
    field_simp
    ring
  have hG : Integrable G := by
    refine integrable_vertical_of_bound (F := borelIntegrand f (a 0) x) (C := Real.exp (x * c) * (K * 1 ! / ρ ^ 1))
      hc0 (((differentiableOn_borelIntegrand hR h.analytic x).continuousOn).comp_continuous hcont hwre)
      fun y => ?_
    have := norm_borelIntegrand_le hR hM x (hwre y)
    simpa using this
  have hT : ∀ k ∈ range n, Integrable (T k) := by
    intro k _
    refine integrable_vertical_of_bound (F := fun w => a (k + 1) * (cexp (x * w) / w ^ (k + 1 + 1)))
      (C := ‖a (k + 1)‖ * Real.exp (x * c) / c ^ k) hc0
      (continuous_const.mul ((by fun_prop : Continuous fun y : ℝ => cexp (x * ((c : ℂ) + y * I))).div
        (hcont.pow _) fun y => pow_ne_zero _ (hw0 y))) fun y => ?_
    rw [norm_mul, norm_div, norm_pow, norm_cexp_mul_vertical, ← mul_div_assoc, div_div]
    have hck : 0 < c ^ k := pow_pos hc0 k
    have hw := hwn y
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_norm_vertical hc0.le y k)
  have hE : Integrable E := by
    refine (hG.sub (integrable_finsetSum _ hT)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y]; ring
  -- the terms give the partial sums
  have hTint : ∀ k ∈ range n, ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y, T k y = a (k + 1) * (x : ℂ) ^ (k + 1) / ((k + 1) ! : ℂ) := by
    intro k _
    simp only [T]
    rw [integral_const_mul, hankel_vertical_y (by omega) hx hc0]
    have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
    push_cast
    field_simp
  have hb0 : borelZero f (a 0) x c - ∑ k ∈ range (n + 1), a k * (x : ℂ) ^ k / (k ! : ℂ) =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ y, E y := by
    unfold borelZero
    have e2 : ∫ y : ℝ, borelIntegrand f (a 0) x ((c : ℂ) + y * I) = (∑ k ∈ range n, ∫ y, T k y) + ∫ y, E y := by
      show ∫ y, G y = _
      simp_rw [hsplit]
      rw [integral_add (integrable_finsetSum _ hT) hE, integral_finsetSum _ hT]
    rw [e2, mul_add, Finset.mul_sum, Finset.sum_congr rfl hTint, sum_range_succ' _ n]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    ring
  rw [hb0]
  -- the bound on the remainder
  set C' : ℝ := Real.exp (x * c) * (K * (n + 1) ! / ρ ^ (n + 1)) / c ^ n
  have hEb : ∀ y : ℝ, ‖E y‖ ≤ C' * (c ^ 2 + y ^ 2)⁻¹ := by
    intro y
    have hz := inv_mem_diskC (hwre y)
    have hr := h.rem (n + 1) _ hz
    rw [norm_inv] at hr
    simp only [E]
    rw [norm_div, norm_mul, norm_cexp_mul_vertical, ← sq_norm_add_mul_I]
    have hp := pow_le_norm_vertical hc0.le y n
    have hcn : 0 < c ^ n := pow_pos hc0 n
    have hw := hwn y
    have hK := h.K_nonneg
    calc Real.exp (x * c) * ‖f ((c : ℂ) + y * I)⁻¹ - ∑ j ∈ range (n + 1), a j * ((c : ℂ) + y * I)⁻¹ ^ j‖ /
          ‖(c : ℂ) + y * I‖ ≤ Real.exp (x * c) * (K * (n + 1) ! / ρ ^ (n + 1) * ‖(c : ℂ) + y * I‖⁻¹ ^ (n + 1)) /
          ‖(c : ℂ) + y * I‖ := by gcongr
      _ = Real.exp (x * c) * (K * (n + 1) ! / ρ ^ (n + 1)) / ‖(c : ℂ) + y * I‖ ^ (n + 2) := by
          rw [inv_pow]; field_simp; ring
      _ ≤ Real.exp (x * c) * (K * (n + 1) ! / ρ ^ (n + 1)) / (c ^ n * ‖(c : ℂ) + y * I‖ ^ 2) := by
          gcongr
      _ = C' * (‖(c : ℂ) + y * I‖ ^ 2)⁻¹ := by simp only [C']; field_simp
  have hC'0 : 0 ≤ C' := by have := h.K_nonneg; positivity
  calc ‖((2 * π : ℝ) : ℂ)⁻¹ * ∫ y, E y‖ = (2 * π)⁻¹ * ‖∫ y, E y‖ := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ (2 * π)⁻¹ * ∫ y : ℝ, C' * (c ^ 2 + y ^ 2)⁻¹ := by
        gcongr
        exact norm_integral_le_of_norm_le ((integrable_inv_sq_add hc0).const_mul C')
          (Filter.Eventually.of_forall hEb)
    _ = K / 2 * Real.exp (x * c) * (n + 1) ! / (ρ * c) ^ (n + 1) := by
        rw [integral_const_mul, integral_inv_sq_add hc0]
        simp only [C']
        field_simp
        ring

/-- **Stirling's upper bound**: `(k+1)! ≤ e √(k+1) ((k+1)/e)^{k+1}`. -/
lemma factorial_succ_le_stirling (k : ℕ) :
    ((k + 1) ! : ℝ) ≤ Real.exp 1 * √((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp_apply, Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hpos : 0 < √(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) := by positivity
  rw [div_le_iff₀ hpos, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
  have h2 : (0 : ℝ) < √2 := by positivity
  calc ((k + 1) ! : ℝ) ≤ Real.exp 1 / √2 * (√2 * √((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1)) := h
    _ = _ := by field_simp

lemma remainder_le_geometric {K x ρ : ℝ} (hK : 0 ≤ K) (hx : 0 < x) (hρ : 0 < ρ) (n : ℕ) :
    K / 2 * Real.exp (x * (((n + 1 : ℕ) : ℝ) / x)) * (n + 1) ! / (ρ * (((n + 1 : ℕ) : ℝ) / x)) ^ (n + 1) ≤
      K / 2 * Real.exp 1 * ((n + 1 : ℕ) : ℝ) * (x / ρ) ^ (n + 1) := by
  set m : ℝ := ((n + 1 : ℕ) : ℝ)
  have hm : 1 ≤ m := by simp [m]
  have hm0 : 0 < m := by linarith
  have hxm : x * (m / x) = m := by field_simp
  rw [hxm, show m = ((n + 1 : ℕ) : ℝ) * 1 by simp [m], Real.exp_nat_mul, mul_one]
  have hf := factorial_succ_le_stirling n
  have hsq : √m ≤ m := (Real.sqrt_le_left hm0.le).2 (by nlinarith)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  calc K / 2 * Real.exp 1 ^ (n + 1) * (n + 1) ! / (ρ * (m / x)) ^ (n + 1)
      ≤ K / 2 * Real.exp 1 ^ (n + 1) * (Real.exp 1 * √m * (m / Real.exp 1) ^ (n + 1)) / (ρ * (m / x)) ^ (n + 1) := by
        gcongr
    _ = K / 2 * Real.exp 1 * √m * (x / ρ) ^ (n + 1) := by
        rw [div_pow, mul_pow, div_pow, div_pow]
        field_simp
    _ ≤ K / 2 * Real.exp 1 * m * (x / ρ) ^ (n + 1) := by
        have : 0 ≤ (x / ρ) ^ (n + 1) := by positivity
        gcongr

/-- **`b₀` is the Borel transform** on `(0, ρ)` (Benedetti–Gurau–Keppler–Lettera, p. 25: "for `0 < x < ρ`,
`b₀(x) = B(t)|_{t = x}`"), for every line `Re w = c`, `c > 1/R`. -/
theorem SokalHyp.borelZero_eq_borelT (h : SokalHyp f a R K ρ) {x c : ℝ} (hx : 0 < x) (hxρ : x < ρ)
    (hc : 1 / R < c) : borelZero f (a 0) x c = borelT a x := by
  have hR := h.R_pos
  have hρ := h.ρ_pos
  have hK := h.K_nonneg
  have hM : ∀ z ∈ diskC R, ‖f z - a 0‖ ≤ K * 1 ! / ρ ^ 1 * ‖z‖ := fun z hz => by simpa using h.rem 1 z hz
  have hM0 : 0 ≤ K * 1 ! / ρ ^ 1 := by positivity
  have hS : Tendsto (fun n => ∑ k ∈ range (n + 1), a k * (x : ℂ) ^ k / (k ! : ℂ)) atTop (𝓝 (borelT a x)) :=
    ((h.hasSum_borelT (by rwa [Complex.norm_real, Real.norm_of_nonneg hx.le])).tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
  have hr0 : 0 ≤ x / ρ := div_nonneg hx.le hρ.le
  have hr1 : x / ρ < 1 := (div_lt_one hρ).2 hxρ
  have hδ : Tendsto (fun n : ℕ => K / 2 * Real.exp 1 * ((n + 1 : ℕ) : ℝ) * (x / ρ) ^ (n + 1)) atTop (𝓝 0) := by
    have h1 := ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)).const_mul
      (K / 2 * Real.exp 1)
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply]; ring
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖borelZero f (a 0) x c - ∑ k ∈ range (n + 1), a k * (x : ℂ) ^ k / (k ! : ℂ)‖ ≤
        K / 2 * Real.exp 1 * ((n + 1 : ℕ) : ℝ) * (x / ρ) ^ (n + 1) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (x / R)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hc' : 1 / R < ((n + 1 : ℕ) : ℝ) / x := by
      rw [div_lt_div_iff₀ hR hx, one_mul]
      have : x / R < ((n + 1 : ℕ) : ℝ) := hN.trans_le (by exact_mod_cast Nat.le_succ_of_le hn)
      rwa [div_lt_iff₀ hR] at this
    rw [borelZero_indep hR h.analytic hM hM0 x hc hc']
    exact (h.norm_borelZero_sub_sum_le hx hc' n).trans (remainder_le_geometric hK hx hρ n)
  have hlim : Tendsto (fun n => ∑ k ∈ range (n + 1), a k * (x : ℂ) ^ k / (k ! : ℂ)) atTop
      (𝓝 (borelZero f (a 0) x c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm' ?_ hδ
    filter_upwards [hbound] with n hn
    rw [norm_norm, norm_sub_rev]; exact hn
  exact tendsto_nhds_unique hlim hS

end Lightlike.FieldTheory.Borel
