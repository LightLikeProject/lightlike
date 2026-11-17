import Mathlib

/-!
# Second-order expansions at `η = 0`: sums, products, finite sums

`Exp2 f a0 a1 a2` says that `f η = a0 + a1 η + a2 η² + O(η³)` as `η → 0`. The class contains the polynomials
(`Exp2.poly`) and is closed under sums (`Exp2.add`, `Exp2.sum`), constant multiples (`Exp2.const_mul`) and products with
convolved coefficients (`Exp2.mul`). It lets the first two `η`-derivatives of an explicit function, such as the curvature
density of `1 + η h`, be computed without differentiating: each ingredient is expanded and the coefficients combined.

## Main results

* `Exp2`, `Exp2.poly`, `Exp2.const`, `Exp2.add`, `Exp2.neg`, `Exp2.sub`, `Exp2.const_mul`, `Exp2.mul`, `Exp2.sum`,
  `Exp2.congr`, `Exp2.congr_fun`.

**Limits.** Real functions of one real variable at `0`, order two only; no statement about differentiability.
-/

open Asymptotics Filter Topology Finset

namespace Lightlike.Regge.Conv3

/-- `f` has the expansion `a0 + a1 η + a2 η²` at `η = 0` with a cubic remainder. -/
def Exp2 (f : ℝ → ℝ) (a0 a1 a2 : ℝ) : Prop :=
  (fun η => f η - (a0 + a1 * η + a2 * η ^ 2)) =O[𝓝 0] fun η => η ^ 3

/-- A polynomial of degree four expands with its first three coefficients. -/
theorem Exp2.poly (a0 a1 a2 a3 a4 : ℝ) : Exp2 (fun η => a0 + a1 * η + a2 * η ^ 2 + a3 * η ^ 3 + a4 * η ^ 4) a0 a1 a2 := by
  have h3 : (fun η : ℝ => η ^ 3) =O[𝓝 0] fun η : ℝ => η ^ 3 := isBigO_refl _ _
  have h4 : (fun η : ℝ => η ^ 4) =O[𝓝 0] fun η : ℝ => η ^ 3 := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    simp only [norm_pow, one_mul, Real.norm_eq_abs]
    have : |x| ^ 4 = |x| * |x| ^ 3 := by ring
    rw [this]
    exact mul_le_of_le_one_left (by positivity) hx.le
  unfold Exp2
  have := (h3.const_mul_left a3).add (h4.const_mul_left a4)
  refine this.congr_left fun η => ?_
  ring

/-- Sums add the coefficients. -/
theorem Exp2.add {f g : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : Exp2 f a0 a1 a2) (hg : Exp2 g b0 b1 b2) :
    Exp2 (fun η => f η + g η) (a0 + b0) (a1 + b1) (a2 + b2) := by
  unfold Exp2 at *
  refine (hf.add hg).congr_left fun η => ?_
  ring

/-- Negation negates the coefficients. -/
theorem Exp2.neg {f : ℝ → ℝ} {a0 a1 a2 : ℝ} (hf : Exp2 f a0 a1 a2) :
    Exp2 (fun η => -f η) (-a0) (-a1) (-a2) := by
  unfold Exp2 at *
  refine hf.neg_left.congr_left fun η => ?_
  ring

/-- Differences subtract the coefficients. -/
theorem Exp2.sub {f g : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : Exp2 f a0 a1 a2) (hg : Exp2 g b0 b1 b2) :
    Exp2 (fun η => f η - g η) (a0 - b0) (a1 - b1) (a2 - b2) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

/-- A constant multiple scales the coefficients. -/
theorem Exp2.const_mul {f : ℝ → ℝ} {a0 a1 a2 : ℝ} (c : ℝ) (hf : Exp2 f a0 a1 a2) :
    Exp2 (fun η => c * f η) (c * a0) (c * a1) (c * a2) := by
  unfold Exp2 at *
  refine (hf.const_mul_left c).congr_left fun η => ?_
  ring

/-- A constant has the expansion `(c, 0, 0)`. -/
theorem Exp2.const (c : ℝ) : Exp2 (fun _ => c) c 0 0 := by
  have := Exp2.poly c 0 0 0 0
  simpa using this

/-- A polynomial of degree two is bounded near `0`. -/
theorem isBigO_one_poly (c0 c1 c2 : ℝ) : (fun η : ℝ => c0 + c1 * η + c2 * η ^ 2) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have hc : Continuous fun η : ℝ => c0 + c1 * η + c2 * η ^ 2 := by fun_prop
  exact (hc.tendsto 0).isBigO_one ℝ

/-- `η³` is bounded near `0`. -/
theorem isBigO_cube_one : (fun η : ℝ => η ^ 3) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have hc : Continuous fun η : ℝ => η ^ 3 := by fun_prop
  exact (hc.tendsto 0).isBigO_one ℝ

/-- Products: the coefficients convolve. -/
theorem Exp2.mul {f g : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : Exp2 f a0 a1 a2) (hg : Exp2 g b0 b1 b2) :
    Exp2 (fun η => f η * g η) (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0) := by
  have hp := Exp2.poly (a0 * b0) (a0 * b1 + a1 * b0) (a0 * b2 + a1 * b1 + a2 * b0)
    (a1 * b2 + a2 * b1) (a2 * b2)
  unfold Exp2 at hf hg hp ⊢
  have hE1 : (fun η => f η - (a0 + a1 * η + a2 * η ^ 2)) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := hf.trans isBigO_cube_one
  have t1 := (isBigO_one_poly a0 a1 a2).mul hg
  have t2 := (isBigO_one_poly b0 b1 b2).mul hf
  have t3 := hE1.mul hg
  simp only [one_mul] at t1 t2 t3
  have := ((hp.add t1).add t2).add t3
  refine this.congr_left fun η => ?_
  ring

/-- Finite sums add the coefficients. -/
theorem Exp2.sum {ι : Type*} (t : Finset ι) {f : ι → ℝ → ℝ} {a0 a1 a2 : ι → ℝ}
    (h : ∀ i ∈ t, Exp2 (f i) (a0 i) (a1 i) (a2 i)) :
    Exp2 (fun η => ∑ i ∈ t, f i η) (∑ i ∈ t, a0 i) (∑ i ∈ t, a1 i) (∑ i ∈ t, a2 i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Exp2.const 0
  | insert j t hj ih =>
    have h1 := h j (mem_insert_self j t)
    have h2 := ih fun i hi => h i (mem_insert_of_mem hi)
    simpa [sum_insert hj] using h1.add h2

/-- A function equal to one with an expansion has that expansion. -/
theorem Exp2.congr_fun {f g : ℝ → ℝ} {a0 a1 a2 : ℝ} (hf : Exp2 f a0 a1 a2) (h : ∀ η, f η = g η) :
    Exp2 g a0 a1 a2 := by
  have : f = g := funext h
  subst this; exact hf

/-- Rewriting the coefficients of an expansion. -/
theorem Exp2.congr {f : ℝ → ℝ} {a0 a1 a2 b0 b1 b2 : ℝ} (hf : Exp2 f a0 a1 a2) (h0 : a0 = b0) (h1 : a1 = b1)
    (h2 : a2 = b2) : Exp2 f b0 b1 b2 := by
  subst h0 h1 h2; exact hf

end Lightlike.Regge.Conv3
