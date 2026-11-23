import Mathlib

/-!
# The Abel-transform kernel in hyperbolic coordinates

For `0 < t < s` the kernel `2 log((√(cosh t - 1) + √(cosh s - 1)) / √(cosh s - cosh t))` of
`AbelKernel.lean` equals `log (tanh ((s+t)/4) / tanh ((s-t)/4))`.  This is the form whose Fourier
transform is computed from `∫ sin (ρt) / sinh t = (π/2) tanh (πρ/2)`.
-/

namespace Lightlike.Lorentz.SL2RPlancherel

/-- `cosh (2x) - 1 = 2 sinh x ^ 2`, so for `x > 0` its square root is `√2 sinh x`. -/
lemma sqrt_cosh_two_mul_sub_one {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.cosh (2 * x) - 1) = Real.sqrt 2 * Real.sinh x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
  have h : Real.cosh (2 * x) - 1 = 2 * Real.sinh x ^ 2 := by
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq x]
  rw [h, Real.sqrt_mul (by norm_num), Real.sqrt_sq hs.le]

/-- The kernel of the Abel-transform norm in the variables `p = (s+t)/4`, `q = (s-t)/4`. -/
lemma abelKernel_tanh_aux {p q : ℝ} (hq : 0 < q) (hqp : q < p) :
    2 * Real.log (Real.sqrt (Real.cosh (2 * (p - q)) - 1) +
        Real.sqrt (Real.cosh (2 * (p + q)) - 1)) -
      2 * Real.log (Real.sqrt (Real.cosh (2 * (p + q)) - Real.cosh (2 * (p - q)))) =
      Real.log (Real.tanh p / Real.tanh q) := by
  have hp : 0 < p := hq.trans hqp
  have hpq : 0 < p - q := by linarith
  have hsp : 0 < Real.sinh p := Real.sinh_pos_iff.2 hp
  have hsq : 0 < Real.sinh q := Real.sinh_pos_iff.2 hq
  have hcp : 0 < Real.cosh p := Real.cosh_pos p
  have hcq : 0 < Real.cosh q := Real.cosh_pos q
  have e1 := sqrt_cosh_two_mul_sub_one hpq
  have e2 := sqrt_cosh_two_mul_sub_one (by linarith : 0 < p + q)
  have hsum : Real.sinh (p - q) + Real.sinh (p + q) = 2 * Real.sinh p * Real.cosh q := by
    rw [Real.sinh_sub, Real.sinh_add]; ring
  have hdiff : Real.cosh (2 * (p + q)) - Real.cosh (2 * (p - q)) =
      8 * Real.sinh p * Real.cosh p * Real.sinh q * Real.cosh q := by
    have a1 : 2 * (p + q) = 2 * p + 2 * q := by ring
    have a2 : 2 * (p - q) = 2 * p - 2 * q := by ring
    rw [a1, a2, Real.cosh_add, Real.cosh_sub, Real.sinh_two_mul, Real.sinh_two_mul]
    ring
  have hx : Real.sqrt (Real.cosh (2 * (p - q)) - 1) + Real.sqrt (Real.cosh (2 * (p + q)) - 1) =
      Real.sqrt 2 * (2 * Real.sinh p * Real.cosh q) := by
    rw [e1, e2, ← hsum]; ring
  have hy : 0 < 8 * Real.sinh p * Real.cosh p * Real.sinh q * Real.cosh q := by positivity
  have hx0 : 0 < Real.sqrt 2 * (2 * Real.sinh p * Real.cosh q) := by positivity
  rw [hx, hdiff, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hsy : 0 < Real.sqrt (8 * Real.sinh p * Real.cosh p * Real.sinh q * Real.cosh q) :=
    Real.sqrt_pos.2 hy
  have l : ∀ z : ℝ, 2 * Real.log z = Real.log (z ^ 2) := fun z => by
    rw [Real.log_pow]; norm_num
  rw [l, l, ← Real.log_div (by positivity) (by positivity)]
  congr 1
  rw [Real.sq_sqrt hy.le, mul_pow, Real.sq_sqrt (by norm_num)]
  field_simp
  ring

/-- For `0 < t < s`: `2 log (√(cosh t - 1) + √(cosh s - 1)) - 2 log √(cosh s - cosh t)
= log (tanh ((s+t)/4) / tanh ((s-t)/4))`. -/
theorem abelKernel_eq_log_tanh {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    2 * Real.log (Real.sqrt (Real.cosh t - 1) + Real.sqrt (Real.cosh s - 1)) -
        2 * Real.log (Real.sqrt (Real.cosh s - Real.cosh t)) =
      Real.log (Real.tanh ((s + t) / 4) / Real.tanh ((s - t) / 4)) := by
  have := abelKernel_tanh_aux (p := (s + t) / 4) (q := (s - t) / 4) (by linarith) (by linarith)
  have a1 : 2 * ((s + t) / 4 - (s - t) / 4) = t := by ring
  have a2 : 2 * ((s + t) / 4 + (s - t) / 4) = s := by ring
  rw [a1, a2] at this
  exact this

end Lightlike.Lorentz.SL2RPlancherel
