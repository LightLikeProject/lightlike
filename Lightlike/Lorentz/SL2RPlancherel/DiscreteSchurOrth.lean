module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurKfinal

/-!
# Orthogonality of the matrix coefficients of distinct `K`-weight pairs

For `(j, l) ≠ (j', l')` the functions `⟨e_j, D_n(g) e_l⟩` and `⟨e_{j'}, D_n(g) e_{l'}⟩` on `SL(2,ℝ)` are orthogonal
in `L²(haarR)` (`integral_mcoef_orth`): the left and right rotation invariance of `haarR` multiplies the integral of the
product by the nontrivial phase `e^{-2i(j-j')α} e^{-2i(l-l')θ}`.
-/

@[expose] public section

open MeasureTheory Set Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Orthogonality of the matrix coefficients of distinct `K`-weight pairs.** -/
theorem integral_mcoef_orth {n : ℕ} (hn : 2 ≤ n) {j l j' l' : ℕ} (h : j ≠ j' ∨ l ≠ l') :
    ∫ g, mcoef n (kClass hn j) (kClass hn l) g * (starRingEnd ℂ) (mcoef n (kClass hn j') (kClass hn l') g)
      ∂haarR = 0 := by
  set P : SL2R → ℂ := fun g => mcoef n (kClass hn j) (kClass hn l) g *
    (starRingEnd ℂ) (mcoef n (kClass hn j') (kClass hn l') g) with hP
  -- the transformation of `P` under `g ↦ k_α g k_θ`
  have hrot : ∀ α θ g, P (rot α * g * rot θ) =
      Complex.exp (-(2 * ((j : ℂ) - j') * (α : ℂ) * Complex.I)) *
        Complex.exp (-(2 * ((l : ℂ) - l') * (θ : ℂ) * Complex.I)) * P g := by
    intro α θ g
    simp only [hP]
    rw [mcoef_rot hn j l α θ g, mcoef_rot hn j' l' α θ g]
    simp only [map_mul, ← Complex.exp_conj]
    have e1 : (starRingEnd ℂ) (-(((n + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I)) =
        ((n + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I := by
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]; ring
    have e2 : (starRingEnd ℂ) (-(((n + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) =
        ((n + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I := by
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [e1, e2]
    have f1 : Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        Complex.exp (((n + 2 * j' : ℕ) : ℂ) * (α : ℂ) * Complex.I) =
        Complex.exp (-(2 * ((j : ℂ) - j') * (α : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have f2 : Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) *
        Complex.exp (((n + 2 * l' : ℕ) : ℂ) * (θ : ℂ) * Complex.I) =
        Complex.exp (-(2 * ((l : ℂ) - l') * (θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← f1, ← f2]
    ring
  -- the integral is invariant under `g ↦ k_α g k_θ`
  have hinv : ∀ α θ, ∫ g, P (rot α * g * rot θ) ∂haarR = ∫ g, P g ∂haarR := by
    intro α θ
    have h1 : ∫ g, P (rot α * g * rot θ) ∂haarR = ∫ g, P (rot α * g) ∂haarR := by
      simp only [mul_assoc]
      exact integral_mul_right_eq_self (fun g => P (rot α * g)) (rot θ)
    rw [h1]
    exact integral_mul_left_eq_self P (rot α)
  have key : ∀ α θ : ℝ, Complex.exp (-(2 * ((j : ℂ) - j') * (α : ℂ) * Complex.I)) *
      Complex.exp (-(2 * ((l : ℂ) - l') * (θ : ℂ) * Complex.I)) * ∫ g, P g ∂haarR = ∫ g, P g ∂haarR := by
    intro α θ
    have h2 := hinv α θ
    simp_rw [hrot α θ] at h2
    rw [integral_const_mul] at h2
    exact h2
  rcases h with hj | hl
  · -- `j ≠ j'`: take `θ = 0` and `α = π / (2 (j - j'))`
    have hd : ((j : ℝ) - j') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hj)
    have h2 := key (π / (2 * ((j : ℝ) - j'))) 0
    have hphase : Complex.exp (-(2 * ((j : ℂ) - j') * ((π / (2 * ((j : ℝ) - j')) : ℝ) : ℂ) * Complex.I)) = -1 := by
      have : -(2 * ((j : ℂ) - j') * ((π / (2 * ((j : ℝ) - j')) : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) := by
        push_cast
        have : (2 * ((j : ℂ) - j')) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hd
        have h3 : ((j : ℂ) - j') ≠ 0 := by exact_mod_cast hd
        field_simp
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [hphase] at h2
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h2
    linear_combination (-1 / 2 : ℂ) * h2
  · have hd : ((l : ℝ) - l') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hl)
    have h2 := key 0 (π / (2 * ((l : ℝ) - l')))
    have hphase : Complex.exp (-(2 * ((l : ℂ) - l') * ((π / (2 * ((l : ℝ) - l')) : ℝ) : ℂ) * Complex.I)) = -1 := by
      have : -(2 * ((l : ℂ) - l') * ((π / (2 * ((l : ℝ) - l')) : ℝ) : ℂ) * Complex.I) = -((π : ℂ) * Complex.I) := by
        push_cast
        have : (2 * ((l : ℂ) - l')) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hd
        have h3 : ((l : ℂ) - l') ≠ 0 := by exact_mod_cast hd
        field_simp
      rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
    rw [hphase] at h2
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul] at h2
    linear_combination (-1 / 2 : ℂ) * h2

end Lightlike.Lorentz.SL2RPlancherel
