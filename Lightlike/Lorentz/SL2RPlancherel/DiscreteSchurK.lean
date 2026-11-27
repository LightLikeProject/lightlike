module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteCoherent
public import Lightlike.Lorentz.SL2RPlancherel.BoxCharacter

/-!
# The matrix coefficients of the `K`-weight vectors of `D_n⁺` in the `K × K`-Fourier components

The matrix coefficient `g ↦ ⟨e_j, D_n(g) e_k⟩` is a `K × K`-eigenfunction: for the rotations it satisfies
`c(k_α g k_θ) = e^{-i(n+2j)α} e^{-i(n+2k)θ} c(g)` (`mcoef_rot`). So its `K × K`-Fourier component `kkCoeff` is
concentrated at the single index `(-(n+2j), -(n+2k))` where it equals `c(a(ξ))` (`kkCoeff_mcoef`), and the Plancherel
identity of the `K × K` components reads
`∫ |c|² d haarR = (2π)² ∫_{ξ>0} sinh ξ |c(a(ξ))|² dξ` (`lintegral_norm_sq_mcoef`).
-/

@[expose] public section

open MeasureTheory Set Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The matrix coefficient** `g ↦ ⟨v, D_n(g) w⟩`. -/
def mcoef (n : ℕ) (v w : Hn n) (g : SL2R) : ℂ := ⟪v, discreteAction n g w⟫_ℂ

lemma continuous_mcoef (n : ℕ) (v w : Hn n) : Continuous (mcoef n v w) := by
  unfold mcoef
  exact continuous_const.inner (continuous_discreteAction n w)

lemma discreteAction_mul' (n : ℕ) (g h : SL2R) (f : Hn n) :
    discreteAction n (g * h) f = discreteAction n g (discreteAction n h f) := by
  simp only [discreteAction_apply]
  exact discreteIso_mul n g h f

lemma discreteAction_one' (n : ℕ) (f : Hn n) : discreteAction n 1 f = f := by
  simp only [discreteAction_apply]
  exact discreteIso_one n f

/-- Moving a rotation across the inner product. -/
lemma inner_discreteAction_rot (n : ℕ) (u y : Hn n) (α : ℝ) :
    ⟪u, discreteAction n (rot α) y⟫_ℂ = ⟪discreteAction n (rot (-α)) u, y⟫_ℂ := by
  have h := discreteAction_inner n (rot (-α)) u (discreteAction n (rot α) y)
  rw [← discreteAction_mul', ← rot_add, neg_add_cancel, rot_zero, discreteAction_one'] at h
  exact h.symm

/-- **The `K × K`-equivariance of the matrix coefficients of the `K`-weight vectors.** -/
theorem mcoef_rot {n : ℕ} (hn : 2 ≤ n) (j k : ℕ) (α θ : ℝ) (g : SL2R) :
    mcoef n (kClass hn j) (kClass hn k) (rot α * g * rot θ) =
      Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        Complex.exp (-(((n + 2 * k : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) * mcoef n (kClass hn j) (kClass hn k) g := by
  unfold mcoef
  rw [discreteAction_mul', discreteAction_mul', discreteAction_rot_kClass hn k θ]
  simp only [map_smul]
  rw [inner_smul_right, inner_discreteAction_rot, discreteAction_rot_kClass hn j (-α), inner_smul_left]
  have h1 : (starRingEnd ℂ) (Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * ((-α : ℝ) : ℂ) * Complex.I))) =
      Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  rw [h1]; ring

/-- The exponents `(n + 2j, n + 2k)` of the `K × K`-weights of `⟨e_j, D(·) e_k⟩`. -/
def kkWeight (n j k : ℕ) : Fin 2 → ℤ := ![((n + 2 * j : ℕ) : ℤ), ((n + 2 * k : ℕ) : ℤ)]

/-- The profile of the matrix coefficient is a single character times its value on `a(ξ)`. -/
lemma kkProfile_mcoef {n : ℕ} (hn : 2 ≤ n) (j k : ℕ) (ξ : ℝ) (x : Fin 2 → ℝ) :
    kkProfile (mcoef n (kClass hn j) (kClass hn k)) ξ x =
      Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j k) i : ℂ) * (x i : ℂ))) *
        mcoef n (kClass hn j) (kClass hn k) (aR ξ) := by
  unfold kkProfile
  rw [mcoef_rot hn j k (2 * π * x 0) (2 * π * x 1) (aR ξ), ← Complex.exp_add]
  congr 2
  simp only [kkWeight, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

/-- **The `K × K`-Fourier components of `⟨e_j, D(·) e_k⟩`**: concentrated at `-(n+2j, n+2k)`. -/
theorem kkCoeff_mcoef {n : ℕ} (hn : 2 ≤ n) (j k : ℕ) (m : Fin 2 → ℤ) (ξ : ℝ) :
    kkCoeff (mcoef n (kClass hn j) (kClass hn k)) m ξ =
      if m + kkWeight n j k = 0 then mcoef n (kClass hn j) (kClass hn k) (aR ξ) else 0 := by
  unfold kkCoeff
  have h1 : ∀ x : Fin 2 → ℝ, Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
      kkProfile (mcoef n (kClass hn j) (kClass hn k)) ξ x =
      mcoef n (kClass hn j) (kClass hn k) (aR ξ) *
        Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + kkWeight n j k) i : ℤ) : ℂ) * (x i : ℂ))) := by
    intro x
    rw [kkProfile_mcoef hn j k ξ x]
    have hexp : Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + kkWeight n j k) i : ℤ) : ℂ) * (x i : ℂ))) =
        Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
          Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j k) i : ℂ) * (x i : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
      ring
    rw [hexp]
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_box_char]
  by_cases h : m + kkWeight n j k = 0
  · simp [h]
  · simp [h]

/-- **Plancherel for `⟨e_j, D(·) e_k⟩` in the radial variable**:
`∫ |c|² d haarR = (2π)² ∫_{ξ>0} sinh ξ |c(a(ξ))|² dξ`. -/
theorem lintegral_norm_sq_mcoef {n : ℕ} (hn : 2 ≤ n) (j k : ℕ) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (kClass hn k) g‖ ^ 2) ∂haarR =
      ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh ξ) *
        ENNReal.ofReal ((2 * π) ^ 2 * ‖mcoef n (kClass hn j) (kClass hn k) (aR ξ)‖ ^ 2) := by
  rw [lintegral_norm_sq_eq_kk (continuous_mcoef n _ _)]
  refine lintegral_congr (fun ξ => ?_)
  congr 2
  rw [tsum_eq_single (-kkWeight n j k)]
  · rw [kkCoeff_mcoef hn j k]
    simp
  · intro m hm
    rw [kkCoeff_mcoef hn j k, if_neg]
    · simp
    · intro h
      apply hm
      have : m = -kkWeight n j k := by
        have := congrArg (fun z => z - kkWeight n j k) h
        simpa [sub_eq_add_neg] using this
      exact this

end Lightlike.Lorentz.SL2RPlancherel
