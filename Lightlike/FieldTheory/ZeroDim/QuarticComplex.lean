import Lightlike.FieldTheory.ZeroDim.Quartic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The quartic partition function for complex coupling

The partition function of the zero-dimensional `λφ⁴` theory, `Z(λ) = ∫ e^{-λφ⁴ - φ²/2} dφ` (Rivasseau–Wang, *Loop
vertex expansion for Φ^{2k} theory in zero dimension*, arXiv:1003.1037, Theorem IV.1 with `k = 2`, p. 17, in the
form of (III-38), p. 9), for complex `λ`. Its Taylor coefficients at `0` are `a_n = (-1)^n √(2π) (4n - 1)!!/n!`, and:

* `differentiableOn_quarticZ`: `Z` is analytic in the half-plane `Re λ > 0`, the domain `D_{k-1} = D_1` of the
  source's proof of Theorem IV.1, which contains the disk `C_R = {Re λ⁻¹ > 1/R}` of Nevanlinna's theorem (Theorem III.2
  with `k = 1`, p. 9);
* `norm_quarticZ_sub_le`: for `Re λ ≥ 0`, the Taylor remainder `R_N Z = Z - ∑_{n ≤ N} a_n λ^n` of (III-34) has
  `|R_N Z(λ)| ≤ √(2π) (4N + 3)!!/(N + 1)! |λ|^{N+1}`;
* `quarticZ_nevanlinna`: the hypotheses of Theorem III.2 with `k = 1`: `Z` analytic in `C_R` and
  `|R_N Z(λ)| ≤ A B^N N! |λ|^{N+1}` uniformly in `C_R`, with `A = 16 √(2π)`, `B = 32`.

The remainder bound comes from the Taylor bound `|e^{-z} - ∑_{m<M} (-z)^m/m!| ≤ |z|^M/M!` for `Re z ≥ 0`
(`norm_cexpNegRem_le`), applied to `z = λφ⁴` under the Gaussian integral.

## Main results

* `quarticZ_nevanlinna`: `Z` satisfies the hypotheses of the Nevanlinna (Watson–Sokal) theorem in every `C_R`.

## References

* V. Rivasseau, Z. Wang, arXiv:1003.1037, Theorem III.2 and (III-34), (III-35), p. 9; (III-38), p. 9;
  Theorem IV.1, p. 17.
-/

open MeasureTheory Finset Complex
open scoped Nat

namespace Lightlike.FieldTheory

/-- The Taylor remainder of `e^{-z}` for complex `z`. -/
noncomputable def cexpNegRem (M : ℕ) (z : ℂ) : ℂ := cexp (-z) - ∑ m ∈ range M, (-z) ^ m / (m ! : ℂ)

lemma hasDerivAt_cexpNegRem (M : ℕ) (z : ℂ) : HasDerivAt (cexpNegRem (M + 1)) (-cexpNegRem M z) z := by
  unfold cexpNegRem
  have h1 : HasDerivAt (fun w : ℂ => cexp (-w)) (-cexp (-z)) z := by
    simpa using (hasDerivAt_neg z).cexp
  have h2 : HasDerivAt (fun w : ℂ => ∑ m ∈ range (M + 1), (-w) ^ m / (m ! : ℂ))
      (-∑ m ∈ range M, (-z) ^ m / (m ! : ℂ)) z := by
    have hterm : ∀ m ∈ range (M + 1), HasDerivAt (fun w : ℂ => (-w) ^ m / (m ! : ℂ))
        ((m : ℂ) * (-z) ^ (m - 1) * (-1) / (m ! : ℂ)) z := by
      intro m _
      have := ((hasDerivAt_neg z).pow m).div_const (m ! : ℂ)
      convert this using 1
    have hs := HasDerivAt.sum hterm
    convert hs using 1
    · ext w; simp [Finset.sum_apply]
    · rw [Finset.sum_range_succ', ← Finset.sum_neg_distrib]
      simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      have : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      field_simp
  have := h1.sub h2
  convert this using 1
  ring

lemma cexpNegRem_succ_zero (M : ℕ) : cexpNegRem (M + 1) 0 = 0 := by
  unfold cexpNegRem
  rw [Finset.sum_range_succ']
  simp

lemma continuous_cexpNegRem (M : ℕ) : Continuous (cexpNegRem M) := by
  unfold cexpNegRem; fun_prop

/-- **The Taylor bound for `e^{-z}` in the closed right half-plane**: for `Re z ≥ 0`,
`|e^{-z} - ∑_{m<M} (-z)^m/m!| ≤ |z|^M/M!`. -/
theorem norm_cexpNegRem_le (M : ℕ) {z : ℂ} (hz : 0 ≤ z.re) : ‖cexpNegRem M z‖ ≤ ‖z‖ ^ M / (M ! : ℝ) := by
  induction M generalizing z with
  | zero =>
    simp only [cexpNegRem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, Complex.norm_exp, neg_re]
    exact Real.exp_le_one_iff.2 (by linarith)
  | succ M ih =>
    -- along the segment `t ↦ t z`, `t ∈ [0, 1]`
    set g : ℝ → ℂ := fun t => cexpNegRem (M + 1) ((t : ℂ) * z)
    have hg : ∀ t : ℝ, HasDerivAt g (-cexpNegRem M ((t : ℂ) * z) * z) t := fun t => by
      have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
        simpa using (hasDerivAt_id t).ofReal_comp.mul_const z
      exact (hasDerivAt_cexpNegRem M ((t : ℂ) * z)).comp t hl
    have hc : Continuous fun t : ℝ => -cexpNegRem M ((t : ℂ) * z) * z :=
      ((continuous_cexpNegRem M).comp (continuous_ofReal.mul continuous_const)).neg.mul continuous_const
    have hFTC : cexpNegRem (M + 1) z = ∫ t in (0 : ℝ)..1, -cexpNegRem M ((t : ℂ) * z) * z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) (hc.intervalIntegrable _ _)]
      simp [g, cexpNegRem_succ_zero]
    rw [hFTC]
    have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖-cexpNegRem M ((t : ℂ) * z) * z‖ ≤ ‖z‖ ^ (M + 1) * t ^ M / (M ! : ℝ) := by
      intro t ht
      have hre : 0 ≤ ((t : ℂ) * z).re := by
        rw [re_ofReal_mul]; exact mul_nonneg ht.1 hz
      rw [norm_mul, norm_neg]
      calc ‖cexpNegRem M ((t : ℂ) * z)‖ * ‖z‖ ≤ ‖(t : ℂ) * z‖ ^ M / (M ! : ℝ) * ‖z‖ :=
            mul_le_mul_of_nonneg_right (ih hre) (norm_nonneg _)
        _ = ‖z‖ ^ (M + 1) * t ^ M / (M ! : ℝ) := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; ring
    calc ‖∫ t in (0 : ℝ)..1, -cexpNegRem M ((t : ℂ) * z) * z‖
        ≤ ∫ t in (0 : ℝ)..1, ‖z‖ ^ (M + 1) * t ^ M / (M ! : ℝ) :=
          intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Filter.Eventually.of_forall fun t ht => hb t ⟨ht.1.le, ht.2⟩)
            ((by fun_prop : Continuous fun t : ℝ => ‖z‖ ^ (M + 1) * t ^ M / (M ! : ℝ)).intervalIntegrable _ _)
      _ = ‖z‖ ^ (M + 1) / ((M + 1) ! : ℝ) := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
          push_cast
          have : (M ! : ℝ) ≠ 0 := by positivity
          field_simp
          ring

/-- The integrand `e^{-λφ⁴ - φ²/2}` of the quartic partition function. -/
noncomputable def quarticIntegrand (z : ℂ) (x : ℝ) : ℂ := cexp (-(z * ((x ^ 4 : ℝ) : ℂ)) - ((x ^ 2 / 2 : ℝ) : ℂ))

/-- **The quartic partition function** `Z(λ) = ∫ e^{-λφ⁴ - φ²/2} dφ` for complex `λ`. -/
noncomputable def quarticZ (z : ℂ) : ℂ := ∫ x : ℝ, quarticIntegrand z x

/-- The Taylor coefficients `a_n = (-1)^n √(2π) (4n - 1)!!/n!` of `Z` at `0`. -/
noncomputable def quarticCoeff (n : ℕ) : ℂ := ((-1 : ℝ) ^ n * √(2 * Real.pi) * ((4 * n - 1)‼ : ℕ) / (n ! : ℝ) : ℝ)

lemma norm_quarticIntegrand (z : ℂ) (x : ℝ) :
    ‖quarticIntegrand z x‖ = Real.exp (-(z.re * x ^ 4) - x ^ 2 / 2) := by
  rw [quarticIntegrand, Complex.norm_exp]
  simp only [sub_re, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

lemma continuous_quarticIntegrand (z : ℂ) : Continuous (quarticIntegrand z) := by
  unfold quarticIntegrand; fun_prop

lemma integrable_gauss : Integrable fun x : ℝ => Real.exp (-(x ^ 2 / 2)) := by
  have := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only; ring_nf

/-- **`Z` is analytic in the right half-plane** `Re λ > 0`. -/
theorem differentiableOn_quarticZ : DifferentiableOn ℂ quarticZ {z | 0 < z.re} := by
  intro z₀ hz₀
  have hs : {z : ℂ | 0 < z.re} ∈ nhds z₀ := (isOpen_lt continuous_const continuous_re).mem_nhds hz₀
  have hle : ∀ z : ℂ, 0 ≤ z.re → ∀ x : ℝ, Real.exp (-(z.re * x ^ 4) - x ^ 2 / 2) ≤ Real.exp (-(x ^ 2 / 2)) :=
    fun z hz x => Real.exp_le_exp.2 (by nlinarith [mul_nonneg hz (by positivity : (0 : ℝ) ≤ x ^ 4)])
  have hint : Integrable (quarticIntegrand z₀) := by
    refine integrable_gauss.mono' (continuous_quarticIntegrand z₀).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_quarticIntegrand]; exact hle z₀ hz₀.le x
  have hbound : Integrable fun x : ℝ => x ^ (2 * 2) * Real.exp (-(x ^ 2 / 2)) := integrable_pow_mul_gauss 2
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := quarticIntegrand)
    (F' := fun z x => -((x ^ 4 : ℝ) : ℂ) * quarticIntegrand z x) hs
    (Filter.Eventually.of_forall fun z => (continuous_quarticIntegrand z).aestronglyMeasurable) hint
    ((continuous_ofReal.comp (by fun_prop : Continuous fun x : ℝ => x ^ 4)).neg.mul
      (continuous_quarticIntegrand z₀)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hz => ?_) hbound (Filter.Eventually.of_forall fun x z _ => ?_)
  · exact h.2.differentiableAt.differentiableWithinAt
  · rw [norm_mul, norm_neg, norm_quarticIntegrand, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hle z (le_of_lt hz) x) (by positivity)
  · have h1 : HasDerivAt (fun w : ℂ => -(w * ((x ^ 4 : ℝ) : ℂ)) - ((x ^ 2 / 2 : ℝ) : ℂ)) (-((x ^ 4 : ℝ) : ℂ)) z := by
      have h0 := ((hasDerivAt_id z).mul_const ((x ^ 4 : ℝ) : ℂ)).neg.sub_const ((x ^ 2 / 2 : ℝ) : ℂ)
      rw [one_mul] at h0
      exact h0
    have h2 := h1.cexp
    unfold quarticIntegrand
    convert h2 using 1
    ring

/-- `(4N + 3)!! ≤ 16^{N+1} ((N + 1)!)²`. -/
lemma doubleFactorial_le (N : ℕ) : (4 * N + 3)‼ ≤ 16 ^ (N + 1) * ((N + 1) !) ^ 2 := by
  induction N with
  | zero => decide
  | succ N ih =>
    have h1 : (4 * (N + 1) + 3)‼ = (4 * N + 7) * ((4 * N + 5) * (4 * N + 3)‼) := by
      rw [show 4 * (N + 1) + 3 = 4 * N + 5 + 2 by ring, Nat.doubleFactorial_add_two,
        show 4 * N + 5 = 4 * N + 3 + 2 by ring, Nat.doubleFactorial_add_two]
    rw [h1, Nat.factorial_succ (N + 1), pow_succ 16 (N + 1)]
    have h2 : (4 * N + 7) * (4 * N + 5) ≤ 16 * (N + 1 + 1) ^ 2 := by nlinarith
    calc (4 * N + 7) * ((4 * N + 5) * (4 * N + 3)‼) = ((4 * N + 7) * (4 * N + 5)) * (4 * N + 3)‼ := by ring
      _ ≤ (16 * (N + 1 + 1) ^ 2) * (16 ^ (N + 1) * ((N + 1) !) ^ 2) := Nat.mul_le_mul h2 ih
      _ = 16 ^ (N + 1) * 16 * ((N + 1 + 1) * (N + 1) !) ^ 2 := by ring

/-- **The Taylor remainder of `Z`** for `Re λ ≥ 0` (Rivasseau–Wang (III-34)):
`|Z(λ) - ∑_{n<M} a_n λ^n| ≤ √(2π) (4M - 1)!!/M! |λ|^M`. -/
theorem norm_quarticZ_sub_le (M : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖quarticZ z - ∑ n ∈ range M, quarticCoeff n * z ^ n‖ ≤
      √(2 * Real.pi) * (((4 * M - 1)‼ : ℕ) / (M ! : ℝ)) * ‖z‖ ^ M := by
  set G : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2))
  have hsplit : ∀ x : ℝ, cexp (-(z * ((x ^ 4 : ℝ) : ℂ)) - ((x ^ 2 / 2 : ℝ) : ℂ)) =
      (∑ m ∈ range M, (-z) ^ m / (m ! : ℂ) * ((x ^ (2 * (2 * m)) * G x : ℝ) : ℂ)) +
        (G x : ℂ) * cexpNegRem M (z * ((x ^ 4 : ℝ) : ℂ)) := by
    intro x
    have e0 : cexp (-(z * ((x ^ 4 : ℝ) : ℂ)) - ((x ^ 2 / 2 : ℝ) : ℂ)) =
        (G x : ℂ) * cexp (-(z * ((x ^ 4 : ℝ) : ℂ))) := by
      rw [show (G x : ℂ) = cexp (-((x ^ 2 / 2 : ℝ) : ℂ)) by simp [G, ofReal_exp], ← Complex.exp_add]
      congr 1; ring
    rw [e0]
    unfold cexpNegRem
    rw [mul_sub, Finset.mul_sum]
    have e : ∀ m ∈ range M, (G x : ℂ) * ((-(z * ((x ^ 4 : ℝ) : ℂ))) ^ m / (m ! : ℂ)) =
        (-z) ^ m / (m ! : ℂ) * ((x ^ (2 * (2 * m)) * G x : ℝ) : ℂ) := fun m _ => by
      push_cast
      rw [show 2 * (2 * m) = 4 * m by ring, pow_mul, ← neg_mul, mul_pow]
      ring
    rw [Finset.sum_congr rfl e]
    ring
  have hI : ∀ m : ℕ, Integrable fun x : ℝ => (-z) ^ m / (m ! : ℂ) * ((x ^ (2 * (2 * m)) * G x : ℝ) : ℂ) :=
    fun m => ((integrable_pow_mul_gauss (2 * m)).ofReal (𝕜 := ℂ)).const_mul _
  have hRb : ∀ x : ℝ, ‖(G x : ℂ) * cexpNegRem M (z * ((x ^ 4 : ℝ) : ℂ))‖ ≤
      ‖z‖ ^ M / (M ! : ℝ) * (x ^ (2 * (2 * M)) * G x) := by
    intro x
    have hre : 0 ≤ (z * ((x ^ 4 : ℝ) : ℂ)).re := by
      rw [re_mul_ofReal]; exact mul_nonneg hz (by positivity)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc G x * ‖cexpNegRem M (z * ((x ^ 4 : ℝ) : ℂ))‖ ≤ G x * (‖z * ((x ^ 4 : ℝ) : ℂ)‖ ^ M / (M ! : ℝ)) :=
          mul_le_mul_of_nonneg_left (norm_cexpNegRem_le M hre) (Real.exp_pos _).le
      _ = ‖z‖ ^ M / (M ! : ℝ) * (x ^ (2 * (2 * M)) * G x) := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow,
            show 2 * (2 * M) = 4 * M by ring, pow_mul]
          ring
  have hR : Integrable fun x : ℝ => (G x : ℂ) * cexpNegRem M (z * ((x ^ 4 : ℝ) : ℂ)) := by
    refine ((integrable_pow_mul_gauss (2 * M)).const_mul (‖z‖ ^ M / (M ! : ℝ))).mono'
      ((continuous_ofReal.comp (by fun_prop : Continuous G)).mul ((continuous_cexpNegRem M).comp
        (continuous_const.mul (continuous_ofReal.comp (by fun_prop))))).aestronglyMeasurable
      (Filter.Eventually.of_forall hRb)
  have hmom : ∀ m ∈ range M, ∫ x : ℝ, (-z) ^ m / (m ! : ℂ) * ((x ^ (2 * (2 * m)) * G x : ℝ) : ℂ) =
      quarticCoeff m * z ^ m := by
    intro m _
    rw [integral_const_mul, integral_complex_ofReal, integral_pow_mul_gauss, show 2 * (2 * m) - 1 = 4 * m - 1 by omega,
      quarticCoeff, neg_pow z]
    push_cast
    have : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    field_simp
  unfold quarticZ quarticIntegrand
  simp_rw [hsplit]
  rw [integral_add (integrable_finsetSum _ fun m _ => hI m) hR, integral_finsetSum _ fun m _ => hI m,
    Finset.sum_congr rfl hmom, add_sub_cancel_left]
  calc ‖∫ x : ℝ, (G x : ℂ) * cexpNegRem M (z * ((x ^ 4 : ℝ) : ℂ))‖
      ≤ ∫ x : ℝ, ‖z‖ ^ M / (M ! : ℝ) * (x ^ (2 * (2 * M)) * G x) :=
        norm_integral_le_of_norm_le ((integrable_pow_mul_gauss (2 * M)).const_mul _)
          (Filter.Eventually.of_forall hRb)
    _ = √(2 * Real.pi) * (((4 * M - 1)‼ : ℕ) / (M ! : ℝ)) * ‖z‖ ^ M := by
        rw [integral_const_mul, integral_pow_mul_gauss, show 2 * (2 * M) - 1 = 4 * M - 1 by omega]
        ring

/-- The disk `C_R = {λ : Re λ⁻¹ > 1/R}` of Nevanlinna's theorem (Rivasseau–Wang, Theorem III.2 with `k = 1`). -/
def diskC (R : ℝ) : Set ℂ := {z | 1 / R < (z⁻¹).re}

lemma re_pos_of_mem_diskC {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ diskC R) : 0 < z.re := by
  have h : 0 < (z⁻¹).re := lt_trans (by positivity) hz
  rw [inv_re] at h
  by_contra hle
  have : z.re / normSq z ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.1 hle) (normSq_nonneg z)
  linarith

/-- **The quartic partition function satisfies the hypotheses of Nevanlinna's theorem** (Rivasseau–Wang,
Theorem IV.1 with `k = 2`, the hypotheses of Theorem III.2 with `k = 1`): for every `R > 0`, `Z` is analytic in `C_R`
and, uniformly in `C_R`, `|R_N Z(λ)| ≤ A B^N N! |λ|^{N+1}` with `A = 16 √(2π)`, `B = 32`. -/
theorem quarticZ_nevanlinna {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ quarticZ (diskC R) ∧
      ∀ N : ℕ, ∀ z ∈ diskC R, ‖quarticZ z - ∑ n ∈ range (N + 1), quarticCoeff n * z ^ n‖ ≤
        16 * √(2 * Real.pi) * 32 ^ N * (N ! : ℝ) * ‖z‖ ^ (N + 1) := by
  refine ⟨differentiableOn_quarticZ.mono fun z hz => re_pos_of_mem_diskC hR hz, fun N z hz => ?_⟩
  refine (norm_quarticZ_sub_le (N + 1) (re_pos_of_mem_diskC hR hz).le).trans ?_
  rw [show 4 * (N + 1) - 1 = 4 * N + 3 by omega]
  have hd : ((4 * N + 3)‼ : ℝ) ≤ 16 ^ (N + 1) * ((N + 1) ! : ℝ) ^ 2 := by exact_mod_cast doubleFactorial_le N
  have hN' : N + 1 ≤ 2 ^ N := Nat.lt_two_pow_self
  have hN : ((N + 1 : ℕ) : ℝ) ≤ 2 ^ N := by exact_mod_cast hN'
  have hf : (0 : ℝ) < ((N + 1) ! : ℝ) := by positivity
  have hq : ((4 * N + 3)‼ : ℝ) / ((N + 1) ! : ℝ) ≤ 16 * 32 ^ N * (N ! : ℝ) := by
    rw [div_le_iff₀ hf]
    calc ((4 * N + 3)‼ : ℝ) ≤ 16 ^ (N + 1) * ((N + 1) ! : ℝ) ^ 2 := hd
      _ = 16 * 16 ^ N * ((N + 1 : ℕ) : ℝ) * (N ! : ℝ) * ((N + 1) ! : ℝ) := by
          rw [Nat.factorial_succ N]; push_cast; ring
      _ ≤ 16 * 16 ^ N * 2 ^ N * (N ! : ℝ) * ((N + 1) ! : ℝ) := by gcongr
      _ = 16 * 32 ^ N * (N ! : ℝ) * ((N + 1) ! : ℝ) := by
          rw [show (32 : ℝ) = 16 * 2 by norm_num, mul_pow]; ring
  calc √(2 * Real.pi) * (((4 * N + 3)‼ : ℕ) / ((N + 1) ! : ℝ)) * ‖z‖ ^ (N + 1)
      ≤ √(2 * Real.pi) * (16 * 32 ^ N * (N ! : ℝ)) * ‖z‖ ^ (N + 1) := by gcongr
    _ = 16 * √(2 * Real.pi) * 32 ^ N * (N ! : ℝ) * ‖z‖ ^ (N + 1) := by ring

end Lightlike.FieldTheory
