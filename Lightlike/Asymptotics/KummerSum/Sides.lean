import Lightlike.Asymptotics.KummerSum.Contour
import Lightlike.Asymptotics.Stirling

/-!
# Kummer's kernel on the vertical sides of the contour

The contour of the saddle-point argument runs up the line `Re z = −½`, across the horizontal line
`Im z = N/2` through the saddle, and down the line `Re z = m + ½` (`N = m + 1`).  On the vertical
sides the kernel is exponentially smaller than at the saddle (`2^N`):

  `‖f(−½ + iy)‖ ≤ (q_N² / N) · exp(N/2 + 3/(2N))`  for `|y| ≤ N/2`, `m ≥ 1`
  (`norm_kummerKernel_left_le`),

and the same on `Re z = m + ½` (`norm_kummerKernel_right_le`), since `f(m − w) = −(−1)^m f(w)`
(`kummerKernel_sub`).  The proof: Euler's reflection formula turns `π/sin(πz)` into
`−Γ(z+1) Γ(−z)`, and on `Re z = −½` the factors `Γ(−z)` and `Γ(z+1)` are complex conjugate, so
`‖f(z)‖ = m!² / ‖Γ(m − z + 1)‖²`; the complex Stirling formula (`Gamma_half_add`) for
`Γ(N + ½ − iy)` and the real one for `m!` (`factorial_eq_stirQ`) give the bound, the loss
`exp(2y²/N) ≤ exp(N/2)` coming from `|arg(N − iy)| ≤ |y|/N`.
-/

open Complex
open scoped Real Nat

namespace Lightlike.Asymptotics

/-- `T(m − w) = T(w)`. -/
lemma kummerT_sub (m : ℕ) (w : ℂ) : kummerT m (m - w) = kummerT m w := by
  unfold kummerT
  rw [show (m : ℂ) - w + 1 = (m : ℂ) - w + 1 from rfl, show (m : ℂ) - ((m : ℂ) - w) + 1 = w + 1 by ring]
  ring

/-- **Symmetry of the kernel**: `f(m − w) = −(−1)^m f(w)`. -/
theorem kummerKernel_sub (m : ℕ) (w : ℂ) :
    kummerKernel m (m - w) = -(-1) ^ m * kummerKernel m w := by
  unfold kummerKernel
  rw [kummerT_sub]
  have hs : Complex.sin (π * ((m : ℂ) - w)) = -(-1) ^ m * Complex.sin (π * w) := by
    rw [mul_sub, Complex.sin_sub, show (π : ℂ) * m = ((m * π : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_sin, ← ofReal_cos, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    push_cast; ring
  have hinv : (-(-1 : ℂ) ^ m)⁻¹ = -(-1) ^ m := by rw [inv_neg, ← inv_pow, inv_neg, inv_one]
  rw [hs, div_eq_mul_inv, mul_inv, hinv, div_eq_mul_inv]
  ring

/-- On `Re z = −½`: `‖f(z)‖ = m!² / ‖Γ(m − z + 1)‖²`. -/
lemma norm_kummerKernel_left (m : ℕ) (y : ℝ) :
    ‖kummerKernel m (-1 / 2 + y * I)‖ =
      ((m ! : ℝ)) ^ 2 / ‖Complex.Gamma ((m : ℂ) + 3 / 2 - y * I)‖ ^ 2 := by
  set z : ℂ := -1 / 2 + y * I with hz
  have hz1 : z + 1 = 1 / 2 + y * I := by rw [hz]; ring
  have hmz : (m : ℂ) - z + 1 = (m : ℂ) + 3 / 2 - y * I := by rw [hz]; ring
  have hnz : -z = (starRingEnd ℂ) (z + 1) := by
    rw [hz1, hz]; apply Complex.ext <;> simp; norm_num
  -- Euler's reflection: `Γ(z+1) Γ(−z) = π / sin(π(z+1)) = −π / sin(πz)`
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (z + 1)
  rw [show 1 - (z + 1) = -z by ring, show (π : ℂ) * (z + 1) = π * z + π by ring,
    Complex.sin_add_pi] at hrefl
  have hG1 : Complex.Gamma (z + 1) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have := congrArg Complex.re hn
    rw [hz1] at this; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h; rw [h, neg_zero, div_zero] at hrefl
    exact mul_ne_zero hG1 (Complex.Gamma_ne_zero fun n hn => by
      have := congrArg Complex.re hn; rw [hz] at this; simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hrefl
  have hK : kummerKernel m z =
      -((m ! : ℂ) ^ 2 * Complex.Gamma (-z) /
        (Complex.Gamma (z + 1) * Complex.Gamma ((m : ℂ) - z + 1) ^ 2)) := by
    unfold kummerKernel kummerT
    have hπs : (π : ℂ) / Complex.sin (π * z) = -(Complex.Gamma (z + 1) * Complex.Gamma (-z)) := by
      rw [hrefl, div_neg, neg_neg]
    rw [mul_div_right_comm, hπs]
    field_simp
  rw [hK, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hnz, Complex.Gamma_conj, Complex.norm_conj,
    hmz, Complex.norm_natCast]
  field_simp [norm_ne_zero_iff.2 hG1]

/-- `|arg w| ≤ |Im w| / Re w` for `Re w > 0`. -/
lemma abs_arg_le_of_re_pos {w : ℂ} (hw : 0 < w.re) : |arg w| ≤ |w.im| / w.re := by
  have hb := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have ht := Complex.tan_arg w
  rcases le_total 0 (arg w) with h | h
  · rw [abs_of_nonneg h]
    have := Real.le_tan h (by rw [abs_lt] at hb; exact hb.2)
    rw [ht] at this
    calc arg w ≤ w.im / w.re := this
      _ ≤ |w.im| / w.re := by gcongr; exact le_abs_self _
  · rw [abs_of_nonpos h]
    have := Real.le_tan (neg_nonneg.2 h) (by rw [abs_lt] at hb; linarith [hb.1])
    rw [Real.tan_neg, ht] at this
    calc -arg w ≤ -(w.im / w.re) := this
      _ = -w.im / w.re := by ring
      _ ≤ |w.im| / w.re := by gcongr; exact neg_le_abs _

/-- **Lower bound for `‖Γ(N + ½ − iy)‖`** for `N ≥ 2`: `≥ √(2π) exp(N log N − N − y²/N − 3/(4N))`. -/
lemma norm_Gamma_half_add_ge {N : ℝ} (hN : 2 ≤ N) (y : ℝ) :
    √(2 * π) * Real.exp (N * Real.log N - N - y ^ 2 / N - 3 / (4 * N)) ≤
      ‖Complex.Gamma ((N : ℂ) - y * I + 1 / 2)‖ := by
  set w : ℂ := (N : ℂ) - y * I with hw
  have hN0 : 0 < N := by linarith
  have hwre : w.re = N := by simp [hw]
  have hwim : w.im = -y := by simp [hw]
  have hws : w ∈ slitPlane := by rw [mem_slitPlane_iff]; left; rw [hwre]; exact hN0
  have hwN : N ≤ ‖w‖ := by have := re_le_norm w; rwa [hwre] at this
  rw [Gamma_half_add hws, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_exp]
  gcongr
  -- the real part of the exponent
  have hmu := (norm_stirMu_le (c := 0) le_rfl (by norm_num) (by rw [hwre]; simp [hN0.le])
    (by norm_num; nlinarith)).2
  have hmu' : -(3 / (4 * N)) ≤ (stirMu w).re := by
    have h1 := neg_abs_le (stirMu w).re
    have h2 := abs_re_le_norm (stirMu w)
    have h3 : 3 / 4 / ((1 - 0) * ‖w‖) ≤ 3 / (4 * N) := by
      rw [sub_zero, one_mul, div_div]; gcongr
    linarith
  have hre : (stirF w).re = N * Real.log ‖w‖ + y * arg w - N := by
    simp only [stirF, sub_re, mul_re, log_re, log_im, hwre, hwim]; ring
  have harg : -(y ^ 2 / N) ≤ y * arg w := by
    have ha := abs_arg_le_of_re_pos (w := w) (by rw [hwre]; exact hN0)
    rw [hwim, hwre, abs_neg] at ha
    have : |y * arg w| ≤ y ^ 2 / N := by
      rw [abs_mul]
      calc |y| * |arg w| ≤ |y| * (|y| / N) := by gcongr
        _ = y ^ 2 / N := by rw [← sq_abs]; ring
    linarith [neg_abs_le (y * arg w)]
  have hlog : Real.log N ≤ Real.log ‖w‖ := Real.log_le_log hN0 hwN
  rw [add_re, hre]
  nlinarith

/-- `m!² = q_N² · 2π · exp(2((N + ½) log N − N)) / N²`, `N = m + 1`. -/
lemma factorial_sq_eq (m : ℕ) :
    ((m ! : ℝ)) ^ 2 = stirQ (m + 1) ^ 2 * (2 * π) *
      Real.exp (2 * (((m + 1 : ℕ) + 1 / 2) * Real.log (m + 1 : ℕ) - (m + 1 : ℕ))) /
        ((m + 1 : ℕ) : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hq : ((m + 1) ! : ℝ) = stirQ (m + 1) * (√(2 * π) *
      Real.exp (((m + 1 : ℕ) + 1 / 2) * Real.log (m + 1 : ℕ) - (m + 1 : ℕ))) := by
    rw [stirQ, div_mul_cancel₀]; positivity
  rw [Nat.factorial_succ, Nat.cast_mul] at hq
  have hm : (m ! : ℝ) = stirQ (m + 1) * (√(2 * π) *
      Real.exp (((m + 1 : ℕ) + 1 / 2) * Real.log (m + 1 : ℕ) - (m + 1 : ℕ))) / (m + 1 : ℕ) := by
    rw [eq_div_iff hN.ne', ← hq]; push_cast; ring
  rw [hm, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq (Real.exp _),
    ← Real.exp_add]
  ring_nf

/-- **The left side**: `‖f(−½ + iy)‖ ≤ (q_N²/N) exp(N/2 + 3/(2N))` for `|y| ≤ N/2`, `m ≥ 1`. -/
theorem norm_kummerKernel_left_le {m : ℕ} (hm : 1 ≤ m) {y : ℝ} (hy : |y| ≤ ((m + 1 : ℕ) : ℝ) / 2) :
    ‖kummerKernel m (-1 / 2 + y * I)‖ ≤
      stirQ (m + 1) ^ 2 / ((m + 1 : ℕ) : ℝ) *
        Real.exp (((m + 1 : ℕ) : ℝ) / 2 + 3 / (2 * ((m + 1 : ℕ) : ℝ))) := by
  set N : ℝ := ((m + 1 : ℕ) : ℝ) with hNdef
  have hN2 : 2 ≤ N := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hNdef]; push_cast; linarith
  have hN0 : 0 < N := by linarith
  have hG := norm_Gamma_half_add_ge hN2 y
  have harg : (m : ℂ) + 3 / 2 - y * I = (N : ℂ) - y * I + 1 / 2 := by
    rw [hNdef]; push_cast; ring
  rw [norm_kummerKernel_left, harg, factorial_sq_eq, ← hNdef]
  set E := N * Real.log N - N - y ^ 2 / N - 3 / (4 * N)
  have hGpos : 0 < √(2 * π) * Real.exp E := by positivity
  have hG2 : 2 * π * Real.exp (2 * E) ≤ ‖Complex.Gamma ((N : ℂ) - y * I + 1 / 2)‖ ^ 2 := by
    have := pow_le_pow_left₀ hGpos.le hG 2
    rw [mul_pow, Real.sq_sqrt (by positivity), sq (Real.exp E), ← Real.exp_add] at this
    rw [show 2 * E = E + E by ring]; exact this
  have hGp : 0 < ‖Complex.Gamma ((N : ℂ) - y * I + 1 / 2)‖ ^ 2 :=
    lt_of_lt_of_le (by positivity) hG2
  rw [div_div, div_le_iff₀ (by positivity)]
  have hy2 : y ^ 2 ≤ N ^ 2 / 4 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2; rw [div_pow] at this; linarith
  have hexp : Real.exp (2 * ((N + 1 / 2) * Real.log N - N)) ≤
      N * Real.exp (N / 2 + 3 / (2 * N)) * Real.exp (2 * E) := by
    rw [← Real.exp_log hN0, ← Real.exp_add, ← Real.exp_add, Real.exp_log hN0]
    apply Real.exp_le_exp.2
    simp only [E]
    have : 2 * y ^ 2 / N ≤ N / 2 := by rw [div_le_div_iff₀ hN0 (by norm_num)]; nlinarith
    field_simp
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ N by linarith)]
  have hq := sq_nonneg (stirQ (m + 1))
  calc stirQ (m + 1) ^ 2 * (2 * π) * Real.exp (2 * ((N + 1 / 2) * Real.log N - N))
      ≤ stirQ (m + 1) ^ 2 * (2 * π) * (N * Real.exp (N / 2 + 3 / (2 * N)) * Real.exp (2 * E)) := by
        gcongr
    _ = stirQ (m + 1) ^ 2 * Real.exp (N / 2 + 3 / (2 * N)) * N * (2 * π * Real.exp (2 * E)) := by
        ring
    _ ≤ stirQ (m + 1) ^ 2 * Real.exp (N / 2 + 3 / (2 * N)) * N *
          ‖Complex.Gamma ((N : ℂ) - y * I + 1 / 2)‖ ^ 2 := by gcongr
    _ = _ := by field_simp

/-- **The right side**: the same bound on `Re z = m + ½`, by `f(m − w) = −(−1)^m f(w)`. -/
theorem norm_kummerKernel_right_le {m : ℕ} (hm : 1 ≤ m) {y : ℝ}
    (hy : |y| ≤ ((m + 1 : ℕ) : ℝ) / 2) :
    ‖kummerKernel m ((m : ℂ) + 1 / 2 + y * I)‖ ≤
      stirQ (m + 1) ^ 2 / ((m + 1 : ℕ) : ℝ) *
        Real.exp (((m + 1 : ℕ) : ℝ) / 2 + 3 / (2 * ((m + 1 : ℕ) : ℝ))) := by
  have e : (m : ℂ) + 1 / 2 + y * I = m - (-1 / 2 + ((-y : ℝ) : ℂ) * I) := by push_cast; ring
  rw [e, kummerKernel_sub, norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_kummerKernel_left_le hm (by rwa [abs_neg])

end Lightlike.Asymptotics
