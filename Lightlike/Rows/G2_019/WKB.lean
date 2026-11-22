import Mathlib

/-!
# Liouville–Green (WKB) solutions of the Airy equation (row G2-019)

For `x > 0` the functions `x^{-1/4} exp(± (2/3) x^{3/2})` are the leading WKB (Liouville–Green)
forms of the Airy solutions: they solve exactly the perturbed equation
`ψ'' = (x + 5/(16 x²)) ψ`, so they solve `ψ'' = x ψ` up to a relative error `5/(16 x³) → 0`.
-/

noncomputable section

namespace Lightlike.Airy

/-- The WKB amplitude `x^{-1/4} exp(s · (2/3) x^{3/2})` (`s = ±1`). -/
def wkbAmp (s x : ℝ) : ℝ := x ^ (-(1/4) : ℝ) * Real.exp (s * (2/3) * x ^ (3/2 : ℝ))

/-- Logarithmic derivative `-1/(4x) + s √x` of the WKB amplitude. -/
def wkbLog (s x : ℝ) : ℝ := -1 / (4 * x) + s * x ^ (1/2 : ℝ)

/-- The derivative of the WKB amplitude. -/
def wkbDeriv (s x : ℝ) : ℝ := wkbLog s x * wkbAmp s x

theorem wkbAmp_hasDerivAt (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wkbAmp s) (wkbDeriv s x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-(1/4) : ℝ)) ((-(1/4) : ℝ) * x ^ ((-(1/4) : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h2 : HasDerivAt (fun y : ℝ => y ^ (3/2 : ℝ)) ((3/2 : ℝ) * x ^ ((3/2 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h3 := ((h2.const_mul (s * (2/3))).exp)
  have h4 := h1.mul h3
  refine h4.congr_deriv ?_
  have e1 : x ^ ((-(1/4) : ℝ) - 1) = x ^ (-(1/4) : ℝ) / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  have e2 : x ^ ((3/2 : ℝ) - 1) = x ^ (1/2 : ℝ) := by norm_num
  rw [e1, e2]
  unfold wkbDeriv wkbLog wkbAmp
  field_simp

theorem wkbLog_hasDerivAt (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wkbLog s) (1 / (4 * x ^ 2) + s / (2 * x ^ (1/2 : ℝ))) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (1/2 : ℝ)) ((1/2 : ℝ) * x ^ ((1/2 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  have h0 : HasDerivAt (fun y : ℝ => 4 * y) 4 x := by
    simpa using (hasDerivAt_id x).const_mul 4
  have h5 : HasDerivAt (fun y : ℝ => -1 / (4 * y)) ((0 * (4 * x) - (-1) * 4) / (4 * x) ^ 2) x :=
    (hasDerivAt_const x (-1 : ℝ)).div h0 (by positivity)
  have h6 := h5.add (h1.const_mul s)
  refine h6.congr_deriv ?_
  have hr : 0 < x ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hx _
  have e3 : x ^ ((1/2 : ℝ) - 1) = 1 / x ^ (1/2 : ℝ) := by
    have : x ^ ((1/2 : ℝ) - 1) * x ^ (1/2 : ℝ) = 1 := by
      rw [← Real.rpow_add hx]; norm_num
    field_simp
    linarith
  rw [e3]
  field_simp
  ring_nf

/-- `x^{1/2} * x^{1/2} = x`. -/
theorem rpow_half_mul_self {x : ℝ} (hx : 0 < x) : x ^ (1/2 : ℝ) * x ^ (1/2 : ℝ) = x := by
  rw [← Real.rpow_add hx]; norm_num

/-- Exact equation of the WKB amplitudes: for `s² = 1` and `x > 0`,
`ψ'' = (x + 5/(16 x²)) ψ`. -/
theorem wkbDeriv_hasDerivAt {s : ℝ} (hs : s ^ 2 = 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (wkbDeriv s) ((x + 5 / (16 * x ^ 2)) * wkbAmp s x) x := by
  have h := (wkbLog_hasDerivAt s hx).mul (wkbAmp_hasDerivAt s hx)
  have h' : HasDerivAt (wkbDeriv s) _ x := h
  refine h'.congr_deriv ?_
  have hr : 0 < x ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hrr := rpow_half_mul_self hx
  unfold wkbDeriv
  unfold wkbLog
  generalize x ^ (1/2 : ℝ) = r at *
  subst hrr
  field_simp
  have : s ^ 2 = 1 := hs
  ring_nf
  simp only [hs]
  ring

/-- Product of the two WKB amplitudes: `x^{-1/4} x^{-1/4} = 1 / x^{1/2}`. -/
theorem wkbAmp_mul {x : ℝ} (hx : 0 < x) :
    wkbAmp (-1) x * wkbAmp 1 x * x ^ (1/2 : ℝ) = 1 := by
  have hr : 0 < x ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hx _
  have h : x ^ (-(1/4) : ℝ) * x ^ (-(1/4) : ℝ) * x ^ (1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num
  have h2 : Real.exp ((-1) * (2/3) * x ^ (3/2 : ℝ)) * Real.exp (1 * (2/3) * x ^ (3/2 : ℝ)) = 1 := by
    rw [← Real.exp_add]; simp
  unfold wkbAmp
  calc _ = (x ^ (-(1/4) : ℝ) * x ^ (-(1/4) : ℝ) * x ^ (1/2 : ℝ)) *
        (Real.exp ((-1) * (2/3) * x ^ (3/2 : ℝ)) * Real.exp (1 * (2/3) * x ^ (3/2 : ℝ))) := by ring
    _ = 1 := by rw [h, h2]; norm_num

/-- Wronskian of the two WKB solutions: `ψ₋ ψ₊' − ψ₋' ψ₊ = 2`, matching the normalisation
`Ai ∼ ψ₋/(2√π)`, `Bi ∼ ψ₊/√π` (whose Wronskian is `1/π`). -/
theorem wkb_wronskian {x : ℝ} (hx : 0 < x) :
    wkbAmp (-1) x * wkbDeriv 1 x - wkbDeriv (-1) x * wkbAmp 1 x = 2 := by
  have h := wkbAmp_mul hx
  unfold wkbDeriv wkbLog at *
  calc _ = (wkbAmp (-1) x * wkbAmp 1 x * x ^ (1/2 : ℝ)) * 2 := by ring
    _ = 2 := by rw [h]; ring

end Lightlike.Airy
