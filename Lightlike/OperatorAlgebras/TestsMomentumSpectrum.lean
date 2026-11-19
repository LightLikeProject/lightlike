import Lightlike.OperatorAlgebras.MomentumSpectrum

/-!
# Checks for the spectrum of the momentum extensions

Non-vacuity and a negative control: `θ` itself is in the spectrum of `P_θ` (the eigenvalue `n = 0`), and `θ + π` is not (it lies halfway
between two eigenvalues); for the periodic extension `P_0` the spectrum contains `2π`.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

/-- `θ` is an eigenvalue of `P_θ`, so the spectrum is not empty. -/
theorem theta_mem_spectrum (θ : ℝ) : (θ : ℂ) ∈ LinearPMap.spectrum (momentumTheta θ) := by
  rw [spectrum_momentumTheta]
  exact ⟨0, by simp⟩

/-- Negative control: `θ + π` is in the resolvent set of `P_θ`. -/
theorem theta_add_pi_not_mem_spectrum (θ : ℝ) : (θ : ℂ) + Real.pi ∉ LinearPMap.spectrum (momentumTheta θ) := by
  rw [spectrum_momentumTheta]
  rintro ⟨n, hn⟩
  have h : (Real.pi : ℂ) = 2 * Real.pi * n := by linear_combination hn
  have h' : Real.pi = 2 * Real.pi * n := by exact_mod_cast h
  have h2 : Real.pi * 1 = Real.pi * (2 * n) := by linarith [h']
  have hn2 : (1 : ℝ) = 2 * n := mul_left_cancel₀ Real.pi_pos.ne' h2
  have : (1 : ℤ) = 2 * n := by exact_mod_cast hn2
  omega

/-- For the periodic extension, `2π` is an eigenvalue. -/
theorem two_pi_mem_spectrum_zero : (2 * Real.pi : ℂ) ∈ LinearPMap.spectrum (momentumTheta 0) := by
  rw [spectrum_momentumTheta]
  exact ⟨1, by simp⟩

end Lightlike.OperatorAlgebras
