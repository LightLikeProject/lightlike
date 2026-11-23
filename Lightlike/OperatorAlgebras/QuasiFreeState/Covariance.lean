import Lightlike.OperatorAlgebras.FockKernel
import Lightlike.OperatorAlgebras.WeylAlgebra

/-!
# Covariances of quasi-free states: positivity of the Gaussian kernel

Quasi-free states on the CCR (Weyl) algebra of a symplectic space `(V, ω)` (Bratteli-Robinson 2, Chapter 5; Dereziński,
arXiv:math-ph/0511030, Section 9.1): a *covariance* is a symmetric real bilinear form `η` with `η(φ, φ) ≥ 0` and
`ω(φ, ψ)² ≤ η(φ, φ) η(ψ, ψ)` (`IsCovariance`). The state is determined by `ω_η(W(φ)) = exp(-¼ η(φ, φ))`.

This file proves the positivity that makes it a state: the Hermitian matrix `H(φ, ψ) = ½ (η(φ, ψ) + i ω(φ, ψ))`
is positive semidefinite (`posSemidef_covH`, from `|ω(a, b)| ≤ ½ (η(a, a) + η(b, b))` applied to the real and the
imaginary part of a coefficient vector), hence so is its entrywise exponential (Schur product theorem), hence so is
the Gram kernel `qfKer ω η φ ψ = ⟨W(φ) Ω, W(ψ) Ω⟩ = exp(i ω(φ, ψ)/2) exp(-¼ η(ψ - φ, ψ - φ))`
(`posSemidef_qfKer`).
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate Matrix

namespace Lightlike.OperatorAlgebras.QuasiFreeState

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω η : LinearMap.BilinForm ℝ V}

/-- **A covariance** for the symplectic form `ω`: a symmetric real bilinear form `η`, nonnegative on the diagonal, with
`ω(a, b)² ≤ η(a, a) η(b, b)` (Bratteli-Robinson 2, Chapter 5, the condition for the quasi-free functional to be
positive). -/
structure IsCovariance (ω η : LinearMap.BilinForm ℝ V) : Prop where
  /-- `η` is symmetric. -/
  symm : ∀ a b, η a b = η b a
  /-- `η` is nonnegative on the diagonal. -/
  nonneg : ∀ a, 0 ≤ η a a
  /-- The bound `ω(a, b)² ≤ η(a, a) η(b, b)`. -/
  sq_le : ∀ a b, ω a b ^ 2 ≤ η a a * η b b

lemma IsCovariance.two_mul_le (hη : IsCovariance ω η) (a b : V) : 2 * ω a b ≤ η a a + η b b := by
  have h1 := hη.sq_le a b
  have h2 := hη.nonneg a
  have h3 := hη.nonneg b
  have h4 : (2 * ω a b) ^ 2 ≤ (η a a + η b b) ^ 2 := by nlinarith [sq_nonneg (η a a - η b b)]
  exact (abs_le_of_sq_le_sq' h4 (by positivity)).2

/-- Bilinear expansion of a form on two finite linear combinations. -/
lemma bilin_sum (B : LinearMap.BilinForm ℝ V) (S : Finset V) (p q : V → ℝ) :
    B (∑ i ∈ S, p i • i) (∑ j ∈ S, q j • j) = ∑ i ∈ S, ∑ j ∈ S, p i * q j * B i j := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The real form `η(a, a) + η(b, b) - 2 ω(a, b)` is the Hermitian form of `η + iω` at `a + i b`. -/
lemma form_sum (hω : ∀ a b, ω a b = -ω b a) (hη : ∀ a b, η a b = η b a) (S : Finset V) (r s : V → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, ((r i : ℂ) - Complex.I * (s i : ℂ)) * ((r j : ℂ) + Complex.I * (s j : ℂ)) *
        (((η i j : ℝ) : ℂ) + Complex.I * ((ω i j : ℝ) : ℂ)) =
      ((η (∑ i ∈ S, r i • i) (∑ i ∈ S, r i • i) + η (∑ i ∈ S, s i • i) (∑ i ∈ S, s i • i)
        - 2 * ω (∑ i ∈ S, r i • i) (∑ i ∈ S, s i • i) : ℝ) : ℂ) := by
  have hterm : ∀ i j, ((r i : ℂ) - Complex.I * (s i : ℂ)) * ((r j : ℂ) + Complex.I * (s j : ℂ)) *
        (((η i j : ℝ) : ℂ) + Complex.I * ((ω i j : ℝ) : ℂ)) =
      (((r i * r j * η i j + s i * s j * η i j - r i * s j * ω i j + s i * r j * ω i j : ℝ)) : ℂ) +
        Complex.I * (((r i * s j - s i * r j) * η i j + (r i * r j + s i * s j) * ω i j : ℝ) : ℂ) := by
    intro i j
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im, Complex.mul_im] <;> ring
  simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  set T : ℝ := ∑ i ∈ S, ∑ j ∈ S, (((r i * s j - s i * r j) * η i j + (r i * r j + s i * s j) * ω i j : ℝ)) with hT
  have hI : T = 0 := by
    have hc : T = -T := by
      conv_lhs => rw [hT, Finset.sum_comm]
      rw [hT, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hη j i, hω j i]
      ring
    linarith
  have hD : ∑ i ∈ S, ∑ j ∈ S, s i * r j * ω i j = -∑ i ∈ S, ∑ j ∈ S, r i * s j * ω i j := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hω j i]
    ring
  have hR : ∑ i ∈ S, ∑ j ∈ S, (r i * r j * η i j + s i * s j * η i j - r i * s j * ω i j + s i * r j * ω i j) =
      η (∑ i ∈ S, r i • i) (∑ i ∈ S, r i • i) + η (∑ i ∈ S, s i • i) (∑ i ∈ S, s i • i)
        - 2 * ω (∑ i ∈ S, r i • i) (∑ i ∈ S, s i • i) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hD]
    rw [bilin_sum η S r r, bilin_sum η S s s, bilin_sum ω S r s]
    ring
  have hI' : ∑ i ∈ S, ∑ j ∈ S, ((((r i * s j - s i * r j) * η i j + (r i * r j + s i * s j) * ω i j : ℝ)) : ℂ) = 0 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hI
    simpa [hT, Complex.ofReal_sum] using this
  rw [hI', mul_zero, add_zero, ← hR]
  push_cast
  rfl

/-- The matrix `H(φ, ψ) = ½ (η(φ, ψ) + i ω(φ, ψ))`: the exponent of the quasi-free two-point kernel. -/
noncomputable def covH (ω η : LinearMap.BilinForm ℝ V) : Matrix V V ℂ :=
  Matrix.of fun f g => (((η f g : ℝ) : ℂ) + Complex.I * ((ω f g : ℝ) : ℂ)) / 2

/-- **`η + iω` is a positive Hermitian form**: for a covariance `η` and an antisymmetric `ω`, the matrix
`½ (η + iω)` is positive semidefinite. This is where `ω² ≤ η η` enters: at `a + i b` the form is
`½ (η(a, a) + η(b, b) - 2 ω(a, b))`. -/
theorem posSemidef_covH (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η) : (covH ω η).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, covH, Matrix.of_apply]
    rw [hη.symm j i, hω j i]
    apply Complex.ext <;> simp
  · have hstar : ∀ a : ℂ, star a = (a.re : ℂ) - Complex.I * (a.im : ℂ) := by
      intro a
      apply Complex.ext <;> simp
    have hterm : ∀ a b u : ℂ, star a * (u / 2) * b =
        (1 / 2 : ℂ) * (((a.re : ℂ) - Complex.I * (a.im : ℂ)) * ((b.re : ℂ) + Complex.I * (b.im : ℂ)) * u) := by
      intro a b u
      have hb : (b.re : ℂ) + Complex.I * (b.im : ℂ) = b := by
        apply Complex.ext <;> simp
      rw [hb, hstar a]
      ring
    set a : V := ∑ i ∈ x.support, (x i).re • i with ha
    set b : V := ∑ i ∈ x.support, (x i).im • i with hb
    have key : (x.sum fun i c => x.sum fun j d => star c * covH ω η i j * d) =
        (((η a a + η b b - 2 * ω a b) / 2 : ℝ) : ℂ) := by
      simp only [Finsupp.sum, covH, Matrix.of_apply, hterm, ← Finset.mul_sum]
      rw [form_sum hω hη.symm x.support (fun i => (x i).re) (fun i => (x i).im)]
      push_cast
      ring
    rw [key]
    refine Complex.zero_le_real.2 ?_
    have h1 := hη.two_mul_le a b
    linarith [hη.nonneg a, hη.nonneg b]

/-- Schur product theorem: the entrywise powers of a positive semidefinite matrix are positive semidefinite. -/
lemma posSemidef_hadPow {ι : Type*} {H : Matrix ι ι ℂ} (hH : H.PosSemidef) (n : ℕ) :
    (Matrix.of fun i j => H i j ^ n).PosSemidef := by
  induction n with
  | zero =>
    have := posSemidef_gram_inf (fun _ : ι => (1 : ℂ))
    convert this using 1
    ext f g; simp [Matrix.gram]
  | succ n ih =>
    have := ih.hadamard hH
    convert this using 1
    ext f g; simp [Matrix.hadamard, pow_succ]

/-- **The entrywise exponential of a positive semidefinite matrix is positive semidefinite.** -/
lemma posSemidef_expMat {ι : Type*} {H : Matrix ι ι ℂ} (hH : H.PosSemidef) :
    (Matrix.of fun i j => Complex.exp (H i j)).PosSemidef := by
  refine posSemidef_of_hasSum (M := fun n => (((n.factorial : ℝ))⁻¹ : ℝ) • (Matrix.of fun i j => H i j ^ n))
    (fun n => ?_) (fun i j => ?_)
  · exact (posSemidef_hadPow hH n).smul (by exact_mod_cast (by positivity : (0 : ℝ) ≤ _))
  · have := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (H i j)
    rw [← Complex.exp_eq_exp_ℂ] at this
    show HasSum _ (Complex.exp (H i j))
    convert this using 1
    funext n
    simp [div_eq_inv_mul]

/-- **The Gram kernel of the quasi-free state**, `⟨W(φ) Ω, W(ψ) Ω⟩ = ⟨Ω, W(-φ) W(ψ) Ω⟩
= exp(i ω(φ, ψ)/2) exp(-¼ η(ψ - φ, ψ - φ))`. -/
noncomputable def qfKer (ω η : LinearMap.BilinForm ℝ V) : Matrix V V ℂ :=
  Matrix.of fun f g => Complex.exp (Complex.I * ((ω f g / 2 : ℝ) : ℂ)) *
    ((Real.exp (-(η (g - f) (g - f) / 4)) : ℝ) : ℂ)

/-- The Gaussian prefactor `exp(-¼ η(φ, φ))`, the value of the state on `W(φ)`. -/
noncomputable def gaussVal (η : LinearMap.BilinForm ℝ V) (f : V) : ℝ := Real.exp (-(η f f / 4))

/-- `qfKer` factors as `e_φ e_ψ exp(H(φ, ψ))`. -/
lemma qfKer_eq (hη : ∀ a b, η a b = η b a) (f g : V) :
    qfKer ω η f g = (gaussVal η f : ℂ) * (gaussVal η g : ℂ) * Complex.exp (covH ω η f g) := by
  have hexp : η (g - f) (g - f) = η g g + η f f - 2 * η f g := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hη g f]; ring
  simp only [qfKer, covH, Matrix.of_apply, gaussVal, Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, hexp]
  congr 1
  push_cast
  ring

/-- **The Gram kernel of a quasi-free state is positive semidefinite** (Schur product theorem; this is the
positivity of the quasi-free functional on the Weyl algebra). -/
theorem posSemidef_qfKer (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η) : (qfKer ω η).PosSemidef := by
  have hU := posSemidef_gram_inf (fun f : V => ((gaussVal η f : ℝ) : ℂ))
  have := hU.hadamard (posSemidef_expMat (posSemidef_covH hω hη))
  convert this using 1
  ext f g
  simp only [qfKer_eq hη.symm, Matrix.hadamard, Matrix.gram, Matrix.of_apply]
  simp [Complex.conj_ofReal, mul_comm]

end Lightlike.OperatorAlgebras.QuasiFreeState
