import Mathlib

/-!
# Uniqueness for the Cauchy problem `v_{ab} = c v` on a triangle

In null coordinates `a = t - x`, `b = t + x` of 1+1 Minkowski space, the Klein–Gordon equation
`(-∂ₜ² + ∂ₓ² - m²) u = 0` becomes `∂ₐ(∂_b v) = c v`, with `c = -m²/4` and `w = ∂_b v`
(see the next file). The Cauchy surface `t = T` is the line `a + b = 2T`. This file proves the
analytic core of the uniqueness of the retarded Green operator in the 1+1 case
(Bär–Ginoux–Pfäffle `bgp-2007` for the general statement): if `v` and `w` vanish on the line
`a + b = 2T`, then `v` vanishes on `a + b ≥ 2T`. This is the finite-speed-of-propagation
statement: `v a b` only depends on the data on the segment of the line `a + b = 2T`
between `a' = 2T - b` and `a' = a`, i.e. on the domain of dependence of `(a, b)`.

The proof is a Picard iteration on the triangle `{x ≤ a, y ≤ b, x + y ≥ 2T}`, with the bound
`|v x y| ≤ M |c|ⁿ (x + y - 2T)^(2n) / (2n)!`.

This is a supporting lemma; no catalogue entry.
-/

open Set MeasureTheory intervalIntegral

namespace Lightlike.GreenOperators

/-- The integral of `(s + d)^k / k!` from `A` to `B` when `A + d = 0`. -/
lemma integral_pow_shift_div_factorial (k : ℕ) (A B d : ℝ) (h : A + d = 0) :
    ∫ s in A..B, (s + d) ^ k / (k.factorial : ℝ) = (B + d) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  have h1 := intervalIntegral.integral_comp_add_right (fun s : ℝ => s ^ k) d (a := A) (b := B)
  rw [intervalIntegral.integral_div, h1, integral_pow, h, Nat.factorial_succ]
  push_cast
  simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  field_simp

/-- One step of the Picard iteration on the triangle. -/
lemma triangle_step (c T : ℝ) (v w : ℝ → ℝ → ℝ)
    (hvw : ∀ a b, HasDerivAt (fun b' => v a b') (w a b) b)
    (hwa : ∀ a b, HasDerivAt (fun a' => w a' b) (c * v a b) a)
    (hv0 : ∀ a, v a (2 * T - a) = 0) (hw0 : ∀ a, w a (2 * T - a) = 0)
    (hcv : Continuous (Function.uncurry v)) (hcw : Continuous (Function.uncurry w))
    (a b K : ℝ) (k : ℕ)
    (hbd : ∀ x y, x ≤ a → y ≤ b → 2 * T ≤ x + y →
      |v x y| ≤ K * ((x + y - 2 * T) ^ k / (k.factorial : ℝ))) :
    ∀ x y, x ≤ a → y ≤ b → 2 * T ≤ x + y →
      |v x y| ≤ |c| * K * ((x + y - 2 * T) ^ (k + 1 + 1) / ((k + 1 + 1).factorial : ℝ)) := by
  have hvc : ∀ b, Continuous fun a' => v a' b := fun b =>
    hcv.comp (Continuous.prodMk continuous_id continuous_const)
  have hwc : ∀ a, Continuous fun b' => w a b' := fun a =>
    hcw.comp (Continuous.prodMk continuous_const continuous_id)
  have hw : ∀ x y, w x y = c * ∫ s in (2 * T - y)..x, v s y := by
    intro x y
    have h := integral_eq_sub_of_hasDerivAt (a := 2 * T - y) (b := x)
      (f := fun a' => w a' y) (f' := fun a' => c * v a' y)
      (fun s _ => hwa s y) (((hvc y).const_smul c).intervalIntegrable _ _)
    have h0 := hw0 (2 * T - y)
    rw [show 2 * T - (2 * T - y) = y by ring] at h0
    rw [intervalIntegral.integral_const_mul, h0] at h
    simpa using h.symm
  have hv : ∀ x y, v x y = ∫ s in (2 * T - x)..y, w x s := by
    intro x y
    have h := integral_eq_sub_of_hasDerivAt (a := 2 * T - x) (b := y)
      (f := fun b' => v x b') (f' := fun b' => w x b')
      (fun s _ => hvw x s) ((hwc x).intervalIntegrable _ _)
    rw [hv0 x] at h
    simpa using h.symm
  have hwb : ∀ x y, x ≤ a → y ≤ b → 2 * T ≤ x + y →
      |w x y| ≤ |c| * K * ((x + y - 2 * T) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    intro x y hx hy hxy
    rw [hw, abs_mul]
    have h1 : |∫ s in (2 * T - y)..x, v s y| ≤
        ∫ s in (2 * T - y)..x, K * ((s + (y - 2 * T)) ^ k / (k.factorial : ℝ)) := by
      have := intervalIntegral.norm_integral_le_of_norm_le (a := 2 * T - y) (b := x)
        (f := fun s => v s y) (g := fun s => K * ((s + (y - 2 * T)) ^ k / (k.factorial : ℝ)))
        (by linarith)
        (ae_of_all volume fun s hs => by
          rw [Real.norm_eq_abs]
          have h2 := hbd s y (hs.2.trans hx) hy (by linarith [hs.1])
          rw [show s + (y - 2 * T) = s + y - 2 * T by ring]
          exact h2)
        ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _)
      rw [Real.norm_eq_abs] at this
      exact this
    rw [intervalIntegral.integral_const_mul,
      integral_pow_shift_div_factorial k _ _ _ (by ring)] at h1
    calc |c| * |∫ s in (2 * T - y)..x, v s y|
        ≤ |c| * (K * ((x + (y - 2 * T)) ^ (k + 1) / ((k + 1).factorial : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := by rw [show x + (y - 2 * T) = x + y - 2 * T by ring]; ring
  intro x y hx hy hxy
  rw [hv]
  have := intervalIntegral.norm_integral_le_of_norm_le (a := 2 * T - x) (b := y)
    (f := fun s => w x s)
    (g := fun s => |c| * K * ((s + (x - 2 * T)) ^ (k + 1) / ((k + 1).factorial : ℝ)))
    (by linarith)
    (ae_of_all volume fun s hs => by
      rw [Real.norm_eq_abs]
      have h2 := hwb x s hx (hs.2.trans hy) (by linarith [hs.1])
      rw [show s + (x - 2 * T) = x + s - 2 * T by ring]
      exact h2)
    ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _)
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    integral_pow_shift_div_factorial (k + 1) _ _ _ (by ring)] at this
  rw [show y + (x - 2 * T) = x + y - 2 * T by ring] at this
  exact this

/-- **Uniqueness for the Cauchy problem** `∂ₐ(∂_b v) = c v` on the half-plane `a + b ≥ 2T`:
if `v`, `w = ∂_b v` are continuous, `∂ₐ w = c v`, and `v`, `w` vanish on the line `a + b = 2T`,
then `v` vanishes for `a + b ≥ 2T`. -/
theorem triangle_unique (c T : ℝ) (v w : ℝ → ℝ → ℝ)
    (hvw : ∀ a b, HasDerivAt (fun b' => v a b') (w a b) b)
    (hwa : ∀ a b, HasDerivAt (fun a' => w a' b) (c * v a b) a)
    (hv0 : ∀ a, v a (2 * T - a) = 0) (hw0 : ∀ a, w a (2 * T - a) = 0)
    (hcv : Continuous (Function.uncurry v)) (hcw : Continuous (Function.uncurry w))
    {a b : ℝ} (hab : 2 * T ≤ a + b) : v a b = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 2 * T - b) (b := a)).prod
    (isCompact_Icc (a := 2 * T - a) (b := b)) |>.exists_bound_of_continuousOn
    (f := Function.uncurry v) hcv.continuousOn
  have hM' : ∀ x y, x ≤ a → y ≤ b → 2 * T ≤ x + y → |v x y| ≤ |M| := by
    intro x y hx hy hxy
    have := hM (x, y) ⟨⟨by linarith, hx⟩, ⟨by linarith, hy⟩⟩
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have key : ∀ n : ℕ, ∀ x y, x ≤ a → y ≤ b → 2 * T ≤ x + y →
      |v x y| ≤ |M| * |c| ^ n * ((x + y - 2 * T) ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    intro n
    induction n with
    | zero =>
      intro x y hx hy hxy
      simpa using hM' x y hx hy hxy
    | succ n ih =>
      intro x y hx hy hxy
      have := triangle_step c T v w hvw hwa hv0 hw0 hcv hcw a b (|M| * |c| ^ n) (2 * n) ih
        x y hx hy hxy
      calc |v x y| ≤ _ := this
        _ = _ := by rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ]; ring
  set s := a + b - 2 * T with hs
  have hle : ∀ n : ℕ, |v a b| ≤ |M| * ((|c| * s ^ 2) ^ n / (n.factorial : ℝ)) := by
    intro n
    have h1 := key n a b le_rfl le_rfl hab
    have hnn : 0 ≤ (|c| * s ^ 2) ^ n := by positivity
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hf2 : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have h2 : (|c| * s ^ 2) ^ n / ((2 * n).factorial : ℝ) ≤ (|c| * s ^ 2) ^ n / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hnn hf hf2
    have heq : |M| * |c| ^ n * ((a + b - 2 * T) ^ (2 * n) / ((2 * n).factorial : ℝ)) =
        |M| * ((|c| * s ^ 2) ^ n / ((2 * n).factorial : ℝ)) := by
      rw [mul_pow, ← pow_mul, hs]; ring
    calc |v a b| ≤ _ := h1
      _ = _ := heq
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hT := (FloorSemiring.tendsto_pow_div_factorial_atTop (|c| * s ^ 2)).const_mul |M|
  have := ge_of_tendsto' hT hle
  simpa using this

end Lightlike.GreenOperators
