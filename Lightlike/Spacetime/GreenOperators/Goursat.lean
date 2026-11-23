import Mathlib

/-!
# Uniqueness for the characteristic (Goursat) problem `v_{ab} = c v`

In null coordinates `a = t - x`, `b = t + x` of 1+1 Minkowski space the Klein–Gordon operator
`-∂ₜ² + ∂ₓ² - m²` is `-4 (∂ₐ∂_b + m²/4)`, so a solution of the Klein–Gordon equation satisfies
`∂ₐ(∂_b v) = c v` with `c = -m²/4`. This file proves the analytic core of the uniqueness of the
retarded and advanced Green operators in the 1+1 Minkowski case (Bär–Ginoux–Pfäffle, *Wave
Equations on Lorentzian Manifolds and Quantization*, Theorem 3.1.1 for the general statement):
a function that vanishes on the two characteristic edges `a = 0` and `b = 0` of a quadrant and
satisfies `∂ₐ(∂_b v) = c v` vanishes on the quadrant. The proof is a Picard iteration of the
double-integral equation, with the factorial bound `|v a b| ≤ M (|c| a b)ⁿ / n!`.

This is a supporting lemma; no catalogue entry.
-/

open Set MeasureTheory intervalIntegral

namespace Lightlike.GreenOperators

/-- One step of the Picard iteration: if `|v| ≤ φ(a) ψ(b)` on `[0, A] × [0, B]`, then
`|v a b| ≤ |c| (∫₀ᵃ φ) (∫₀ᵇ ψ)` there. Here `v` vanishes on the edges `a = 0`, `b = 0`,
`w = ∂_b v` and `∂ₐ w = c v`. -/
lemma goursat_step (c : ℝ) (v w : ℝ → ℝ → ℝ)
    (hvw : ∀ a b, HasDerivAt (fun b' => v a b') (w a b) b)
    (hwa : ∀ a b, HasDerivAt (fun a' => w a' b) (c * v a b) a)
    (hv0a : ∀ b, v 0 b = 0) (hv0b : ∀ a, v a 0 = 0)
    (hcv : Continuous (Function.uncurry v)) (hcw : Continuous (Function.uncurry w))
    (A B : ℝ) (φ ψ : ℝ → ℝ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hbd : ∀ a ∈ Icc 0 A, ∀ b ∈ Icc 0 B, |v a b| ≤ φ a * ψ b)
    {a b : ℝ} (ha : a ∈ Icc 0 A) (hb : b ∈ Icc 0 B) :
    |v a b| ≤ |c| * (∫ x in (0:ℝ)..a, φ x) * (∫ y in (0:ℝ)..b, ψ y) := by
  have hvc : ∀ b, Continuous fun a' => v a' b := fun b =>
    hcv.comp (Continuous.prodMk continuous_id continuous_const)
  have hwc : ∀ a, Continuous fun b' => w a b' := fun a =>
    hcw.comp (Continuous.prodMk continuous_const continuous_id)
  have hvc' : ∀ a, Continuous fun b' => v a b' := fun a =>
    hcv.comp (Continuous.prodMk continuous_const continuous_id)
  -- `w 0 b = 0`
  have hw0 : ∀ b, w 0 b = 0 := by
    intro b
    have h : HasDerivAt (fun b' => v 0 b') 0 b := by
      simp only [hv0a]; exact hasDerivAt_const _ _
    exact (hvw 0 b).unique h
  -- `w a b = c ∫₀ᵃ v`
  have hw : ∀ a b, w a b = c * ∫ x in (0:ℝ)..a, v x b := by
    intro a b
    have h := integral_eq_sub_of_hasDerivAt (a := 0) (b := a)
      (f := fun a' => w a' b) (f' := fun a' => c * v a' b)
      (fun x _ => hwa x b) (((hvc b).const_smul c).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul, hw0] at h
    simpa using h.symm
  have hv : ∀ a b, v a b = ∫ y in (0:ℝ)..b, w a y := by
    intro a b
    have h := integral_eq_sub_of_hasDerivAt (a := 0) (b := b)
      (f := fun b' => v a b') (f' := fun b' => w a b')
      (fun x _ => hvw a x) ((hwc a).intervalIntegrable _ _)
    rw [hv0b] at h
    simpa using h.symm
  obtain ⟨ha0, haA⟩ := ha
  obtain ⟨hb0, hbB⟩ := hb
  -- bound on `w`
  have hwb : ∀ y ∈ Icc (0:ℝ) b, |w a y| ≤ |c| * (∫ x in (0:ℝ)..a, φ x) * ψ y := by
    intro y hy
    rw [hw, abs_mul]
    have : |∫ x in (0:ℝ)..a, v x y| ≤ ∫ x in (0:ℝ)..a, φ x * ψ y := by
      have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := a) (f := fun x => v x y)
        (g := fun x => φ x * ψ y) ha0
        (ae_of_all volume fun x hx => by
          rw [Real.norm_eq_abs]
          exact hbd x ⟨hx.1.le, hx.2.trans haA⟩ y ⟨hy.1, hy.2.trans hbB⟩)
        ((hφ.mul continuous_const).intervalIntegrable _ _)
      simpa [Real.norm_eq_abs] using this
    rw [intervalIntegral.integral_mul_const] at this
    calc |c| * |∫ x in (0:ℝ)..a, v x y| ≤ |c| * ((∫ x in (0:ℝ)..a, φ x) * ψ y) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  rw [hv a b]
  have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := b) (f := fun y => w a y)
    (g := fun y => |c| * (∫ x in (0:ℝ)..a, φ x) * ψ y) hb0
    (ae_of_all volume fun y hy => by rw [Real.norm_eq_abs]; exact hwb y ⟨hy.1.le, hy.2⟩)
    ((continuous_const.mul hψ).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at this
  simpa [Real.norm_eq_abs, mul_assoc] using this

/-- **Uniqueness for the Goursat problem** `∂ₐ(∂_b v) = c v`: a function that is continuous, has
continuous `b`-derivative `w` with `∂ₐ w = c v`, and vanishes on the two edges `a = 0`, `b = 0`
of the quadrant, vanishes on the quadrant `a, b ≥ 0`. -/
theorem goursat_unique (c : ℝ) (v w : ℝ → ℝ → ℝ)
    (hvw : ∀ a b, HasDerivAt (fun b' => v a b') (w a b) b)
    (hwa : ∀ a b, HasDerivAt (fun a' => w a' b) (c * v a b) a)
    (hv0a : ∀ b, v 0 b = 0) (hv0b : ∀ a, v a 0 = 0)
    (hcv : Continuous (Function.uncurry v)) (hcw : Continuous (Function.uncurry w))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : v a b = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := a)).prod
    (isCompact_Icc (a := (0:ℝ)) (b := b)) |>.exists_bound_of_continuousOn
    (f := Function.uncurry v) hcv.continuousOn
  have hM' : ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b, |v x y| ≤ |M| := fun x hx y hy => by
    have := hM (x, y) ⟨hx, hy⟩
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have key : ∀ n : ℕ, ∀ x ∈ Icc (0:ℝ) a, ∀ y ∈ Icc (0:ℝ) b,
      |v x y| ≤ |M| * |c| ^ n * (x ^ n / n.factorial) * (y ^ n / n.factorial) := by
    intro n
    induction n with
    | zero => intro x hx y hy; simpa using hM' x hx y hy
    | succ n ih =>
      intro x hx y hy
      have hint : ∀ t : ℝ, ∫ s in (0:ℝ)..t, (s ^ n / (n.factorial : ℝ)) =
          t ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        intro t
        rw [intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
        push_cast
        field_simp
        simp
      have := goursat_step c v w hvw hwa hv0a hv0b hcv hcw a b
        (fun s => |M| * |c| ^ n * (s ^ n / n.factorial)) (fun s => s ^ n / n.factorial)
        (by fun_prop) (by fun_prop) ih hx hy
      rw [intervalIntegral.integral_const_mul, hint, hint] at this
      calc |v x y| ≤ _ := this
        _ = _ := by rw [pow_succ]; ring
  have hle : ∀ n : ℕ, |v a b| ≤ |M| * ((|c| * a * b) ^ n / n.factorial) := by
    intro n
    have h1 := key n a ⟨ha, le_rfl⟩ b ⟨hb, le_rfl⟩
    have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hf1 : (1:ℝ) ≤ n.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero n)
    have heq : |M| * |c| ^ n * (a ^ n / n.factorial) * (b ^ n / n.factorial) =
        |M| * ((|c| * a * b) ^ n / n.factorial) * (1 / n.factorial) := by
      rw [mul_pow, mul_pow]; field_simp
    have hnn : 0 ≤ |M| * ((|c| * a * b) ^ n / n.factorial) := by positivity
    have h2 : |M| * ((|c| * a * b) ^ n / n.factorial) * (1 / n.factorial) ≤
        |M| * ((|c| * a * b) ^ n / n.factorial) :=
      mul_le_of_le_one_right hnn ((div_le_one hf).2 hf1)
    exact h1.trans (heq.le.trans h2)
  have hT := (FloorSemiring.tendsto_pow_div_factorial_atTop (|c| * a * b)).const_mul |M|
  have := ge_of_tendsto' hT hle
  simpa using this

end Lightlike.GreenOperators
