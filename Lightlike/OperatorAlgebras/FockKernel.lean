import Lightlike.OperatorAlgebras.FockUnique
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Fock kernel is positive semidefinite

Helper lemmas for `T-OP2-P1` (`Tasks/OP/T_OP2_P1.lean`). The kernel `fockGram f g = ⟪W f Ω, W g Ω⟫` of a Fock
representation (`FockUnique.lean`) factors as `e f * e g * exp (⟪f, g⟫ / 2)` with `e f = exp (-‖f‖² / 4)`
(`fockGram_eq`). The kernel `exp (⟪f, g⟫ / 2)` is the sum of the entrywise powers `⟪f, g⟫ ^ n / (2 ^ n n!)`
of the Gram matrix, each positive semidefinite by the Schur product theorem (Mathlib:
`Matrix.PosSemidef.hadamard`), and a pointwise convergent sum of positive semidefinite matrices is
positive semidefinite (`posSemidef_of_hasSum`). So `fockGram`, the Hadamard product of `e f * e g` with it,
is positive semidefinite (`posSemidef_fockMat`).
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate Matrix

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The Gram matrix of vectors indexed by any type is positive semidefinite. -/
lemma posSemidef_gram_inf {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : ι → E) :
    (Matrix.gram ℂ v).PosSemidef := by
  refine ⟨Matrix.isHermitian_gram _ _, fun x => ?_⟩
  have : (x.sum fun i a => x.sum fun j b => star a * Matrix.gram ℂ v i j * b) =
      ⟪x.sum fun i a => a • v i, x.sum fun j b => b • v j⟫_ℂ := by
    unfold Finsupp.sum
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [inner_smul_left, inner_smul_right, Matrix.gram, Matrix.of_apply, RCLike.star_def]
    ring
  rw [this, inner_self_eq_norm_sq_to_K]
  have h0 := Complex.zero_le_real.2 (sq_nonneg ‖x.sum fun i a => a • v i‖)
  push_cast at h0
  exact h0

/-- The entrywise `n`-th power of the Gram matrix `⟪f, g⟫`. -/
noncomputable def gramPow (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] (n : ℕ) :
    Matrix h h ℂ := Matrix.of fun f g => ⟪f, g⟫_ℂ ^ n

/-- **Schur product theorem for the Gram powers**: every entrywise power of the Gram matrix is positive
semidefinite. -/
lemma posSemidef_gramPow (n : ℕ) : (gramPow h n).PosSemidef := by
  induction n with
  | zero =>
    have := posSemidef_gram_inf (fun _ : h => (1 : ℂ))
    convert this using 1
    ext f g; simp [gramPow, Matrix.gram]
  | succ n ih =>
    have := ih.hadamard (posSemidef_gram_inf (fun f : h => f))
    convert this using 1
    ext f g; simp [gramPow, Matrix.gram, Matrix.hadamard, pow_succ]

/-- A pointwise convergent sum of positive semidefinite matrices is positive semidefinite. -/
lemma posSemidef_of_hasSum {ι : Type*} {K : Matrix ι ι ℂ} {M : ℕ → Matrix ι ι ℂ}
    (hM : ∀ n, (M n).PosSemidef) (hK : ∀ i j, HasSum (fun n => M n i j) (K i j)) :
    K.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply]
    have h1 : HasSum (fun n => star (M n j i)) (star (K j i)) := (hK j i).star
    have h2 : (fun n => star (M n j i)) = fun n => M n i j := by
      funext n; exact (hM n).1.apply i j
    rw [h2] at h1
    exact ((hK i j).unique h1).symm
  · have hs : HasSum (fun n => x.sum fun i a => x.sum fun j b => star a * M n i j * b)
        (x.sum fun i a => x.sum fun j b => star a * K i j * b) := by
      unfold Finsupp.sum
      refine hasSum_sum fun i _ => ?_
      refine hasSum_sum fun j _ => ?_
      exact ((hK i j).mul_left (star (x i))).mul_right (x j)
    exact hs.nonneg fun n => (hM n).2 x

/-- The real Gaussian prefactor `e f = exp (-‖f‖² / 4)`. -/
noncomputable def gaussE (f : h) : ℝ := Real.exp (-(‖f‖ ^ 2 / 4))

/-- **`fockGram` factors** as `e f * e g * exp (⟪f, g⟫ / 2)`. -/
lemma fockGram_eq (f g : h) :
    fockGram f g = (gaussE f : ℂ) * (gaussE g : ℂ) * Complex.exp (⟪f, g⟫_ℂ / 2) := by
  unfold fockGram gaussE
  have h1 : symp h (-f) g = -(⟪f, g⟫_ℂ).im := by simp [symp, inner_neg_left]
  have h2 : ‖-f + g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 - 2 * (⟪f, g⟫_ℂ).re := by
    have := norm_sub_sq (𝕜 := ℂ) g f
    rw [show -f + g = g - f by abel, this]
    have h3 : RCLike.re ⟪g, f⟫_ℂ = (⟪f, g⟫_ℂ).re := by
      rw [inner_re_symm]; rfl
    rw [h3]; ring
  rw [h1, h2, Complex.ofReal_exp, Complex.ofReal_exp]
  simp only [← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- The kernel `exp (⟪f, g⟫ / 2)`. -/
noncomputable def expKer (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] : Matrix h h ℂ :=
  Matrix.of fun f g => Complex.exp (⟪f, g⟫_ℂ / 2)

lemma posSemidef_expKer : (expKer h).PosSemidef := by
  refine posSemidef_of_hasSum (M := fun n => (((2 : ℝ) ^ n * (n.factorial : ℝ))⁻¹ : ℝ) • gramPow h n)
    (fun n => ?_) (fun f g => ?_)
  · exact (posSemidef_gramPow n).smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ _))
  · have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (⟪f, g⟫_ℂ / 2)
    rw [← Complex.exp_eq_exp_ℂ] at this
    show HasSum _ (Complex.exp (⟪f, g⟫_ℂ / 2))
    convert this using 1
    funext n
    simp [gramPow, div_pow]
    ring

end Lightlike.OperatorAlgebras
