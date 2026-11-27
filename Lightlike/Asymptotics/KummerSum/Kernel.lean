import Lightlike.Asymptotics.KummerSum.Contour
import Lightlike.Asymptotics.KummerSum.Phase
import Lightlike.Asymptotics.Stirling

/-!
# Kummer's kernel in Stirling form

On the open upper half-plane, with `N = m + 1` and `α = (z + ½)/N`, the complex Stirling formula
(`Gamma_half_add`) for `Γ(z + 1) = Γ(w₁ + ½)` and `Γ(m − z + 1) = Γ(w₂ + ½)`, `w₁ = z + ½ = N α`,
`w₂ = m − z + ½ = N (1 − α)`, and the real one for `m! = N!/N` (`factorial_eq_stirQ`) give

  `f(z) = −(q_N² / N) · exp(N ψ(α)) · exp(−2 (μ(w₁) + μ(w₂))) / (1 + exp(2πi w₁))`

(`kummerKernel_eq`), with `ψ = kummerPhase`, `q_N = stirQ N → 1` and the Stirling remainder `μ`.
The phase `N ψ(α)` collects `iπ w₁` from `1/sin(π z)` and `−2 (w₁ log w₁ − w₁ + w₂ log w₂ − w₂)`
from the two Gamma functions; the `N log N` terms cancel against `m!²`.
-/

open Complex
open scoped Real Nat

namespace Lightlike.Asymptotics

/-- The slowly varying factor `exp(−2 (μ(w₁) + μ(w₂))) / (1 + exp(2πi w₁))` of Kummer's kernel. -/
noncomputable def kummerAmp (m : ℕ) (z : ℂ) : ℂ :=
  exp (-2 * (stirMu (z + 1 / 2) + stirMu (m - z + 1 / 2))) / (1 + exp (2 * π * I * (z + 1 / 2)))

lemma sin_pi_mul_eq (z : ℂ) :
    Complex.sin (π * z) = -(exp (π * (z + 1 / 2) * I) + (exp (π * (z + 1 / 2) * I))⁻¹) / 2 := by
  have h : (π : ℂ) * z = π * (z + 1 / 2) - π / 2 := by ring
  rw [h, Complex.sin_sub_pi_div_two, Complex.cos, ← exp_neg]
  ring_nf

/-- **Kummer's kernel in Stirling form.** -/
theorem kummerKernel_eq (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    kummerKernel m z = -((stirQ (m + 1) : ℂ) ^ 2 / (m + 1)) *
      exp ((m + 1 : ℂ) * kummerPhase ((z + 1 / 2) / (m + 1))) * kummerAmp m z := by
  set N : ℕ := m + 1 with hNdef
  have hNr : (0 : ℝ) < N := by positivity
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNr.ne'
  have hN1 : ((m : ℂ) + 1) = N := by simp [hNdef]
  rw [hN1]
  set w₁ := z + 1 / 2 with hw₁
  set w₂ := (m : ℂ) - z + 1 / 2 with hw₂
  set α := w₁ / N with hα
  have hw1im : 0 < w₁.im := by simp [hw₁, hz]
  have hw2im : w₂.im < 0 := by simp [hw₂, hz]
  have hw1s : w₁ ∈ slitPlane := mem_slitPlane_of_im_pos hw1im
  have hw2s : w₂ ∈ slitPlane := by rw [mem_slitPlane_iff]; right; exact hw2im.ne
  have hα0 : α ≠ 0 := by
    rw [hα]; exact div_ne_zero (fun h => by rw [h] at hw1im; simp at hw1im) hNc
  have hα1 : 1 - α ≠ 0 := by
    intro h
    have : w₁ = N := by
      rw [hα, sub_eq_zero, eq_comm, div_eq_one_iff_eq hNc] at h; exact h
    rw [this] at hw1im; simp at hw1im
  have e1 : w₁ = (N : ℝ) * α := by rw [hα]; push_cast; field_simp
  have e2 : w₂ = (N : ℝ) * (1 - α) := by
    rw [hα, hw₂, hw₁]; push_cast; field_simp; rw [hNdef]; push_cast; ring
  -- Stirling for the two Gamma functions
  have hΓ1 : Complex.Gamma (z + 1) = ((√(2 * π) : ℝ) : ℂ) * exp (stirF w₁ + stirMu w₁) := by
    rw [← Gamma_half_add hw1s, hw₁]; ring_nf
  have hΓ2 : Complex.Gamma ((m : ℂ) - z + 1) =
      ((√(2 * π) : ℝ) : ℂ) * exp (stirF w₂ + stirMu w₂) := by
    rw [← Gamma_half_add hw2s, hw₂]; ring_nf
  -- the `N log N` terms
  have hlogN : log (N : ℂ) = (Real.log N : ℂ) := by
    rw [← ofReal_natCast, ofReal_log hNr.le]
  have hF : stirF w₁ + stirF w₂ = N * log N - N + N * (xlog α + xlog (1 - α)) := by
    rw [stirF, stirF, e1, e2, log_ofReal_mul hNr hα0, log_ofReal_mul hNr hα1, xlog, xlog, hlogN]
    push_cast
    ring
  -- the factorial
  have hfac : ((m ! : ℕ) : ℂ) * N = stirQ N * ((√(2 * π) : ℝ) : ℂ) *
      (exp (N * log N - N) * exp (log N / 2)) := by
    have := factorial_eq_stirQ N
    rw [hNdef, Nat.factorial_succ, Nat.cast_mul] at this
    rw [← exp_add, show (N : ℂ) * log N - N + log N / 2 = (N + 1 / 2) * log N - N by ring,
      ← this, hNdef]
    push_cast; ring
  have hR : exp (log (N : ℂ) / 2) ^ 2 = N := by
    rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * (log N / 2) = log N by push_cast; ring, exp_log hNc]
  have hs : (((√(2 * π) : ℝ) : ℂ)) ^ 2 = 2 * π := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  -- the sine
  have hU := sin_pi_mul_eq z
  set U := exp (π * w₁ * I) with hUdef
  have hU0 : U ≠ 0 := exp_ne_zero _
  have hU2 : exp (2 * π * I * w₁) = U ^ 2 := by
    rw [hUdef, ← exp_nat_mul]; congr 1; push_cast; ring
  have hsin0 : Complex.sin (π * z) ≠ 0 := by
    apply sin_pi_mul_ne_zero
    intro n hn; rw [hn] at hz; simp at hz
  have hden : 1 + U ^ 2 ≠ 0 := by
    intro h
    apply hsin0
    rw [hU]
    field_simp
    linear_combination -h
  -- assemble
  have hphase : exp ((N : ℂ) * kummerPhase α) =
      U * (exp (N * (xlog α + xlog (1 - α))))⁻¹ ^ 2 := by
    rw [kummerPhase, hUdef, ← exp_neg, ← exp_nat_mul, ← exp_add]
    congr 1
    rw [hα]; push_cast; field_simp; ring
  have hamp : kummerAmp m z =
      (exp (stirMu w₁ + stirMu w₂))⁻¹ ^ 2 / (1 + U ^ 2) := by
    rw [kummerAmp, ← hw₁, ← hw₂, hU2, ← exp_neg, ← exp_nat_mul]
    congr 2; rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [kummerKernel, kummerT, hΓ1, hΓ2, hphase, hamp, hU]
  set P := exp ((N : ℂ) * log N - N)
  set R := exp (log (N : ℂ) / 2)
  set X := exp ((N : ℂ) * (xlog α + xlog (1 - α)))
  set Y := exp (stirMu w₁ + stirMu w₂)
  have hAB : exp (stirF w₁ + stirMu w₁) * exp (stirF w₂ + stirMu w₂) = P * X * Y := by
    rw [← exp_add, ← exp_add, ← exp_add]; congr 1; linear_combination hF
  have hm : ((m ! : ℕ) : ℂ) = stirQ N * ((√(2 * π) : ℝ) : ℂ) * (P * R) / N := by
    rw [← hfac]; field_simp
  rw [hm]
  have hP : P ≠ 0 := exp_ne_zero _
  have hX : X ≠ 0 := exp_ne_zero _
  have hY : Y ≠ 0 := exp_ne_zero _
  have hS : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < √(2 * π)).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : ((√(2 * π) : ℝ) : ℂ) * exp (stirF w₁ + stirMu w₁) *
      (((√(2 * π) : ℝ) : ℂ) * exp (stirF w₂ + stirMu w₂)) = 2 * π * (P * X * Y) := by
    rw [← hAB, ← hs]; ring
  have hinv : (((√(2 * π) : ℝ) : ℂ) * exp (stirF w₁ + stirMu w₁))⁻¹ *
      (((√(2 * π) : ℝ) : ℂ) * exp (stirF w₂ + stirMu w₂))⁻¹ = (2 * π * (P * X * Y))⁻¹ := by
    rw [← mul_inv, key]
  rw [mul_assoc (stirQ N * ((√(2 * π) : ℝ) : ℂ) * (P * R) / N), hinv]
  field_simp
  rw [hR, hs]
  field_simp
  rw [add_comm (U ^ 2) 1, mul_div_assoc, div_self hden, mul_one]

end Lightlike.Asymptotics
