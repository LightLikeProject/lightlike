import Lightlike.OperatorAlgebras.QuasiFreeState.Functional
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Trust check: a covariance that violates the bound gives no positive functional

The bound `ω(a, b)² ≤ η(a, a) η(b, b)` of `IsCovariance` cannot be dropped.  For the smallest violation, `η = 0`
(so the "state" would be `W(φ) ↦ 1`) on a symplectic space with `ω(x, y) = 1`, the quasi-free functional is not
positive: on `a = W(x) + W(y) - 2 W(0)` it gives `ω_η(a* a) = 2 cos(½) - 2 < 0`
(`qfFunctional_twNormSq_zero_neg`).  The positive result `qfFunctional_twNormSq_nonneg` therefore needs its
hypothesis `IsCovariance`.
-/

open scoped ComplexOrder ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : LinearMap.BilinForm ℝ V}

/-- `η = 0` does not satisfy the covariance bound as soon as `ω(x, y) ≠ 0`. -/
lemma not_isCovariance_zero {x y : V} (hxy : ω x y ≠ 0) :
    ¬ IsCovariance ω (0 : LinearMap.BilinForm ℝ V) := by
  intro h
  have := h.sq_le x y
  simp at this
  exact hxy this

omit [AddCommGroup V] [Module ℝ V] in
/-- The quadratic form of a kernel on a combination of three Weyl elements, expanded. -/
lemma quad_three (K : V → V → ℂ) (a b c : V) (p q r : ℂ) :
    (Finsupp.single a p + Finsupp.single b q + Finsupp.single c r : V →₀ ℂ).sum
      (fun φ s => (Finsupp.single a p + Finsupp.single b q + Finsupp.single c r : V →₀ ℂ).sum
        fun ψ t => star s * K φ ψ * t) =
    star p * K a a * p + star p * K a b * q + star p * K a c * r +
    (star q * K b a * p + star q * K b b * q + star q * K b c * r) +
    (star r * K c a * p + star r * K c b * q + star r * K c c * r) := by
  have h1 : ∀ (g : V → ℂ → ℂ), (∀ φ, g φ 0 = 0) → (∀ φ s t, g φ (s + t) = g φ s + g φ t) →
      ∀ (u v w : V →₀ ℂ), (u + v + w).sum g = u.sum g + v.sum g + w.sum g := by
    intro g h0 hadd u v w
    rw [Finsupp.sum_add_index' h0 hadd, Finsupp.sum_add_index' h0 hadd]
  have h2 : ∀ (g : V → ℂ → ℂ), (∀ φ, g φ 0 = 0) → ∀ (u : V) (s : ℂ), (Finsupp.single u s).sum g = g u s :=
    fun g h0 u s => Finsupp.sum_single_index (h0 u)
  have hz : ∀ (φ : V) (s : ℂ), (Finsupp.sum (Finsupp.single a p + Finsupp.single b q + Finsupp.single c r : V →₀ ℂ)
        fun ψ t => star s * K φ ψ * t) = star s * (K φ a * p + K φ b * q + K φ c * r) := by
    intro φ s
    rw [h1 _ (fun ψ => by simp) (fun ψ s t => by ring), h2 _ (fun ψ => by simp), h2 _ (fun ψ => by simp),
      h2 _ (fun ψ => by simp)]
    ring
  simp only [hz]
  rw [h1 _ (fun ψ => by simp) (fun ψ s t => by simp only [star_add]; ring), h2 _ (fun ψ => by simp),
    h2 _ (fun ψ => by simp), h2 _ (fun ψ => by simp)]
  ring

/-- **Trust check (violation of the bound).**  If `ω(x, y) = 1` (antisymmetric `ω`), the quasi-free functional with
covariance `η = 0` is negative on `a* a` for `a = W(x) + W(y) - 2 W(0)`: it is not a positive functional. -/
theorem qfFunctional_twNormSq_zero_neg (hω : ∀ a b, ω a b = -ω b a) {x y : V} (hxy : ω x y = 1) :
    ¬ 0 ≤ qfFunctional (0 : LinearMap.BilinForm ℝ V)
      (twNormSq ω (Finsupp.single 0 (-2) + Finsupp.single x 1 + Finsupp.single y 1)) := by
  have hyx : ω y x = -1 := by rw [hω y x, hxy]
  have hxx : ω x x = 0 := by have := hω x x; linarith
  have hyy : ω y y = 0 := by have := hω y y; linarith
  have h3 := quad_three (fun φ ψ => qfKer ω (0 : LinearMap.BilinForm ℝ V) φ ψ) 0 x y (-2) 1 1
  beta_reduce at h3
  rw [qfFunctional_twNormSq, h3]
  have hcos : Complex.exp (Complex.I * ((1 / 2 : ℝ) : ℂ)) + Complex.exp (Complex.I * ((-1 / 2 : ℝ) : ℂ)) =
      ((2 * Real.cos (1 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    have e1 : Complex.I * ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) * Complex.I := by ring
    have e2 : Complex.I * ((-1 / 2 : ℝ) : ℂ) = -((1 / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1, e2]
    push_cast
    ring
  have key : (star (-2 : ℂ) * qfKer ω 0 0 0 * (-2) + star (-2 : ℂ) * qfKer ω 0 0 x * 1 +
      star (-2 : ℂ) * qfKer ω 0 0 y * 1 +
      (star (1 : ℂ) * qfKer ω 0 x 0 * (-2) + star (1 : ℂ) * qfKer ω 0 x x * 1 + star (1 : ℂ) * qfKer ω 0 x y * 1) +
      (star (1 : ℂ) * qfKer ω 0 y 0 * (-2) + star (1 : ℂ) * qfKer ω 0 y x * 1 +
        star (1 : ℂ) * qfKer ω 0 y y * 1)) = ((2 * Real.cos (1 / 2) - 2 : ℝ) : ℂ) := by
    simp only [qfKer, Matrix.of_apply, map_zero, LinearMap.zero_apply, hxy, hyx, hxx, hyy]
    simp only [zero_div, neg_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, Real.exp_zero,
      Complex.ofReal_one, star_one, star_neg, mul_one, one_mul, star_ofNat]
    push_cast at hcos ⊢
    linear_combination hcos
  rw [key]
  rw [Complex.zero_le_real]
  have : Real.cos (1 / 2) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 1 / 2) le_rfl (by linarith [Real.pi_gt_three])
      (by norm_num)
    simpa using this
  linarith

end Lightlike.OperatorAlgebras.QuasiFreeState
