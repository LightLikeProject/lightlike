import Lightlike.OperatorAlgebras.FockVacuumAverage
import Lightlike.OperatorAlgebras.ShaleDeterminant
import Lightlike.OperatorAlgebras.ShaleHilbertSchmidt
import Lightlike.OperatorAlgebras.FockReduction
import Lightlike.FieldTheory.Gaussian.Integral

/-!
# Shale's criterion, necessity

`T-OP2-P6` (`Tasks/OP/T_OP2_P6.lean`): a Bogoliubov transformation `T` implemented in a Fock representation has a
Hilbert-Schmidt antilinear part (`shale_necessity_of_implements`).

Proof. An implementing unitary gives `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖²/4)` (`gaussian_vector_of_implements`).
The Fock representation is irreducible, so `c = |⟪Ω, W g Ψ⟫|² > 0` for some `g`. For a finite orthonormal
family `e` of `n` modes, with `f_x = ∑ₖ (x (inl k) + i x (inr k)) • eₖ` and `Φ = W g Ψ`:

* `(2π)ⁿ c ≤ Re ∫ exp (-‖f_x‖²/4) ⟪Φ, W f_x Φ⟫ dx` (`gaussZ_mul_norm_inner_sq_le`);
* `|⟪Φ, W f Φ⟫| = exp (-‖T f‖²/4)`, so the integral is at most
  `∫ exp (-(‖f_x‖² + ‖T f_x‖²)/4) dx = (2π)ⁿ / √(det ((1 + A)/2))`, `A` the real matrix of `f ↦ ‖T f‖²` in
  the coordinates `x` (`integral_exp_neg_half_quad`);
* `A + i Ω` is the Gram matrix of the vectors `T eₖ`, `T (i eₖ)` (the transformation preserves the symplectic
  form), so `det ((1 + A)/2) ≥ 1 + (1/4) ∑ₖ (‖T eₖ‖² + ‖T (i eₖ)‖² - 2)` (`four_pow_mul_le_det_one_add`).

So the sums `∑ₖ (‖T eₖ‖² + ‖T (i eₖ)‖² - 2)` over finite subfamilies of a Hilbert basis are bounded by
`4 (1/c² - 1)`, which is the hypothesis of `Bogoliubov.isHilbertSchmidt_of_finite_bound`.
-/

open scoped InnerProductSpace
open MeasureTheory Complex Matrix
open scoped ComplexOrder

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {m : Type*} [Fintype m]

/-- The real basis `eₖ`, `i eₖ` of the real span of the modes `e`. -/
noncomputable def modeReal (e : m → h) : m ⊕ m → h := Sum.elim e fun k => I • e k

lemma modeVec_eq_sum (e : m → h) (x : m ⊕ m → ℝ) : modeVec e x = ∑ i, x i • modeReal e i := by
  unfold modeVec modeReal
  rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [add_smul, mul_comm, mul_smul, Complex.coe_smul, Complex.coe_smul]

/-- The block `Re ⟪T eⱼ, T eₖ⟫` of the matrix of `f ↦ ‖T f‖²`. -/
noncomputable def covP (T : Bogoliubov h) (e : m → h) : Matrix m m ℝ :=
  Matrix.of fun j k => (⟪T.toEquiv (e j), T.toEquiv (e k)⟫_ℂ).re

/-- The block `Re ⟪T eⱼ, T (i eₖ)⟫` of the matrix of `f ↦ ‖T f‖²`. -/
noncomputable def covQ (T : Bogoliubov h) (e : m → h) : Matrix m m ℝ :=
  Matrix.of fun j k => (⟪T.toEquiv (e j), T.toEquiv (I • e k)⟫_ℂ).re

/-- The block `Re ⟪T (i eⱼ), T (i eₖ)⟫` of the matrix of `f ↦ ‖T f‖²`. -/
noncomputable def covR (T : Bogoliubov h) (e : m → h) : Matrix m m ℝ :=
  Matrix.of fun j k => (⟪T.toEquiv (I • e j), T.toEquiv (I • e k)⟫_ℂ).re

/-- The real matrix of the quadratic form `f ↦ ‖T f‖²` on the real span of the modes `e`, in the basis
`eₖ`, `i eₖ`. -/
noncomputable def covMatrix (T : Bogoliubov h) (e : m → h) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  fromBlocks (covP T e) (covQ T e) (covQ T e)ᵀ (covR T e)

lemma covMatrix_apply (T : Bogoliubov h) (e : m → h) (i j : m ⊕ m) :
    covMatrix T e i j = (⟪T.toEquiv (modeReal e i), T.toEquiv (modeReal e j)⟫_ℂ).re := by
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · exact inner_re_symm (𝕜 := ℂ) _ _
  · rfl

lemma covP_transpose (T : Bogoliubov h) (e : m → h) : (covP T e)ᵀ = covP T e := by
  ext i j; exact inner_re_symm (𝕜 := ℂ) _ _

lemma covR_transpose (T : Bogoliubov h) (e : m → h) : (covR T e)ᵀ = covR T e := by
  ext i j; exact inner_re_symm (𝕜 := ℂ) _ _

lemma covMatrix_transpose (T : Bogoliubov h) (e : m → h) : (covMatrix T e)ᵀ = covMatrix T e := by
  rw [covMatrix, fromBlocks_transpose, covP_transpose, covR_transpose, transpose_transpose]

/-- `‖T f_x‖² = xᵀ A x`. -/
lemma norm_map_modeVec_sq (T : Bogoliubov h) (e : m → h) (x : m ⊕ m → ℝ) :
    ‖T.toEquiv (modeVec e x)‖ ^ 2 = x ⬝ᵥ covMatrix T e *ᵥ x := by
  have hT : T.toEquiv (modeVec e x) = ∑ i, (x i : ℂ) • T.toEquiv (modeReal e i) := by
    rw [modeVec_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Complex.coe_smul]
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (T.toEquiv (modeVec e x))
  rw [← h2, hT, sum_inner, map_sum]
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, conj_ofReal, covMatrix_apply]
  change ((x i : ℂ) * ((x j : ℂ) * _)).re = _
  rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

variable [DecidableEq m]

/-- **The uncertainty relation**: `A + i Ω` is the Gram matrix of the vectors `T eₖ`, `T (i eₖ)`, hence
positive semidefinite. -/
lemma posSemidef_uncertaintyMatrix (T : Bogoliubov h) {e : m → h} (he : Orthonormal ℂ e) :
    (uncertaintyMatrix (covP T e) (covQ T e) (covR T e)).PosSemidef := by
  have hentry : ∀ a b : h, ⟪T.toEquiv a, T.toEquiv b⟫_ℂ =
      ((⟪T.toEquiv a, T.toEquiv b⟫_ℂ).re : ℂ) + I * ((⟪a, b⟫_ℂ).im : ℂ) := by
    intro a b
    have h1 := T.symp_map a b
    unfold symp at h1
    rw [← h1, mul_comm]
    exact (Complex.re_add_im _).symm
  have hee : ∀ j k, ⟪e j, e k⟫_ℂ = if j = k then 1 else 0 := orthonormal_iff_ite.1 he
  have hG : uncertaintyMatrix (covP T e) (covQ T e) (covR T e) =
      Matrix.gram ℂ fun i => T.toEquiv (modeReal e i) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [uncertaintyMatrix, fromBlocks_apply₁₁, Matrix.map_apply, covP, Matrix.of_apply,
        Matrix.gram_apply, modeReal, Sum.elim_inl]
      rw [hentry (e i) (e j), hee]
      split_ifs <;> simp
    · simp only [uncertaintyMatrix, fromBlocks_apply₁₂, Matrix.map_apply, covQ, Matrix.of_apply,
        Matrix.gram_apply, modeReal, Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      rw [hentry (e i) (I • e j), inner_smul_right, hee]
      split_ifs <;> simp
    · simp only [uncertaintyMatrix, fromBlocks_apply₂₁, Matrix.map_apply, covQ, Matrix.of_apply,
        Matrix.gram_apply, modeReal, Sum.elim_inl, Sum.elim_inr, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Matrix.transpose_apply]
      rw [hentry (I • e i) (e j), inner_smul_left, hee]
      have hs : (⟪T.toEquiv (e j), T.toEquiv (I • e i)⟫_ℂ).re =
          (⟪T.toEquiv (I • e i), T.toEquiv (e j)⟫_ℂ).re := inner_re_symm (𝕜 := ℂ) _ _
      rw [hs]
      split_ifs <;> simp [sub_eq_add_neg]
    · simp only [uncertaintyMatrix, fromBlocks_apply₂₂, Matrix.map_apply, covR, Matrix.of_apply,
        Matrix.gram_apply, modeReal, Sum.elim_inr]
      rw [hentry (I • e i) (I • e j), inner_smul_left, inner_smul_right, hee]
      split_ifs <;> simp
  rw [hG]
  exact Matrix.posSemidef_gram ℂ _

/-- The Gaussian integral over `ι → ℝ` (the statement `integral_exp_neg_half_quad` is over
`EuclideanSpace ℝ ι`). -/
lemma integral_exp_neg_half_quad_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M.PosDef) :
    ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ M *ᵥ x)) =
      Real.sqrt (2 * Real.pi) ^ Fintype.card ι / Real.sqrt M.det := by
  have h1 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).integral_comp'
    (fun x : ι → ℝ => Real.exp (-(1 / 2) * (x ⬝ᵥ M *ᵥ x)))
  rw [← h1]
  exact Lightlike.FieldTheory.integral_exp_neg_half_quad M hM

/-- The modulus of the characteristic function of a displaced Gaussian vector. -/
lemma norm_inner_W_gaussian (R : FockRep h K) (T : Bogoliubov h) {Ψ : K}
    (hΨ : ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ))) (g f : h) :
    ‖⟪R.W g Ψ, R.W f (R.W g Ψ)⟫_ℂ‖ = Real.exp (-(‖T.toEquiv f‖ ^ 2 / 4)) := by
  have hph : ∀ r : ℝ, ‖cexp (-(I * (r : ℂ)))‖ = 1 := fun r => by
    rw [Complex.norm_exp]; simp
  have hadd : -T.toEquiv g + T.toEquiv (f + g) = T.toEquiv f := by
    rw [map_add]; abel
  rw [R.weyl, inner_smul_right, norm_mul, hph, one_mul, gram_gaussian_vector R T hΨ, R.inner_W_Ω]
  unfold fockGram
  rw [norm_mul, hph, one_mul, hadd, Complex.norm_exp, Complex.neg_re, Complex.ofReal_re]

/-- The matrix `(1 + A)/2` of the quadratic form `(‖f‖² + ‖T f‖²)/2` on the real span of the modes. -/
noncomputable def halfCov (T : Bogoliubov h) (e : m → h) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  (1 / 2 : ℝ) • (1 + covMatrix T e)

lemma halfCov_quad (T : Bogoliubov h) (e : m → h) (x : m ⊕ m → ℝ) :
    x ⬝ᵥ halfCov T e *ᵥ x = (1 / 2) * (∑ i, x i ^ 2 + ‖T.toEquiv (modeVec e x)‖ ^ 2) := by
  rw [halfCov, Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
    ← norm_map_modeVec_sq, smul_eq_mul]
  congr 2
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

lemma halfCov_posDef (T : Bogoliubov h) (e : m → h) : (halfCov T e).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [halfCov, Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_one]
    simp [conjTranspose_eq_transpose_of_trivial, covMatrix_transpose]
  · have hx' : star x = x := by ext i; simp
    rw [hx', halfCov_quad]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    have hpos : 0 < ∑ i, x i ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, by
        have : x i ≠ 0 := by simpa using hi
        positivity⟩
    positivity

/-- `exp (-‖f_x‖²/4) exp (-‖T f_x‖²/4)` is the Gaussian of the matrix `(1 + A)/2`. -/
lemma gaussE_mul_gaussE_map (T : Bogoliubov h) {e : m → h} (he : Orthonormal ℂ e) (x : m ⊕ m → ℝ) :
    gaussE (modeVec e x) * gaussE (T.toEquiv (modeVec e x)) =
      Real.exp (-(1 / 2) * (x ⬝ᵥ halfCov T e *ᵥ x)) := by
  rw [gaussE, gaussE, norm_modeVec_sq he, ← Real.exp_add, halfCov_quad]
  congr 1
  ring

lemma integral_gaussE_mul_gaussE_map (T : Bogoliubov h) {e : m → h} (he : Orthonormal ℂ e) :
    ∫ x : m ⊕ m → ℝ, gaussE (modeVec e x) * gaussE (T.toEquiv (modeVec e x)) =
      gaussZ m / Real.sqrt (halfCov T e).det := by
  simp_rw [gaussE_mul_gaussE_map T he]
  rw [integral_exp_neg_half_quad_pi _ (halfCov_posDef T e)]
  rfl

lemma halfCov_det (T : Bogoliubov h) (e : m → h) :
    (halfCov T e).det = (1 + covMatrix T e).det / 4 ^ Fintype.card m := by
  have h4 : (0 : ℝ) < 4 ^ Fintype.card m := by positivity
  rw [halfCov, det_smul, Fintype.card_sum, ← two_mul, pow_mul]
  rw [eq_div_iff h4.ne', mul_comm, ← mul_assoc, ← mul_pow]
  norm_num

omit [DecidableEq m] in
lemma covP_trace_add_covR_trace (T : Bogoliubov h) (e : m → h) :
    (covP T e).trace + (covR T e).trace - 2 * Fintype.card m =
      ∑ k, (‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [Matrix.trace, Matrix.diag, covP, covR, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hn : ∀ v : h, (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := fun v => inner_self_eq_norm_sq (𝕜 := ℂ) v
  simp only [hn]
  ring

omit [DecidableEq m] in
lemma trace_fromBlocks_eq (A B C D : Matrix m m ℝ) : (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

lemma halfCov_trace (T : Bogoliubov h) (e : m → h) :
    (halfCov T e).trace - Fintype.card (m ⊕ m) =
      (∑ k, (‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2)) / 2 := by
  rw [← covP_trace_add_covR_trace, halfCov, trace_smul, trace_add, trace_one, covMatrix, trace_fromBlocks_eq,
    Fintype.card_sum, smul_eq_mul]
  push_cast
  ring

/-- **The determinant bound for the modes**: `1 + (1/4) ∑ₖ (‖T eₖ‖² + ‖T (i eₖ)‖² - 2) ≤ det ((1 + A)/2)`. -/
lemma one_add_le_halfCov_det (T : Bogoliubov h) {e : m → h} (he : Orthonormal ℂ e) :
    1 + (∑ k, (‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2)) / 4 ≤ (halfCov T e).det := by
  have h1 := four_pow_mul_le_det_one_add (covP T e) (covQ T e) (covR T e) (covP_transpose T e)
    (covR_transpose T e) (posSemidef_uncertaintyMatrix T he)
  rw [covP_trace_add_covR_trace] at h1
  have h4 : (0 : ℝ) < 4 ^ Fintype.card m := by positivity
  rw [halfCov_det, le_div_iff₀ h4, mul_comm]
  exact h1

/-- **The finite-mode bound.** For a vector `Ψ` with characteristic function `exp (-‖T f‖²/4)`, a vector `g`
and a finite orthonormal family `e`:
`|⟪Ω, W g Ψ⟫|² √(1 + (1/4) ∑ₖ (‖T eₖ‖² + ‖T (i eₖ)‖² - 2)) ≤ 1`. -/
theorem norm_inner_sq_mul_sqrt_le_one (R : FockRep h K) (T : Bogoliubov h) {Ψ : K}
    (hΨ : ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ))) (g : h)
    {e : m → h} (he : Orthonormal ℂ e) :
    ‖⟪R.Ω, R.W g Ψ⟫_ℂ‖ ^ 2 *
      Real.sqrt (1 + (∑ k, (‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2)) / 4) ≤ 1 := by
  set c := ‖⟪R.Ω, R.W g Ψ⟫_ℂ‖ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hdetpos : 0 < (halfCov T e).det := (halfCov_posDef T e).det_pos
  -- the upper bound of the Gaussian average
  have hnorm : ∀ x : m ⊕ m → ℝ, ‖(gaussE (modeVec e x) : ℂ) *
      ⟪R.W g Ψ, R.W (modeVec e x) (R.W g Ψ)⟫_ℂ‖ =
      gaussE (modeVec e x) * gaussE (T.toEquiv (modeVec e x)) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gaussE_pos _).le, norm_inner_W_gaussian R T hΨ]
    rfl
  have hupper : gaussZ m * c ≤ gaussZ m / Real.sqrt (halfCov T e).det := by
    calc gaussZ m * c
        ≤ (∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
            ⟪R.W g Ψ, R.W (modeVec e x) (R.W g Ψ)⟫_ℂ).re := gaussZ_mul_norm_inner_sq_le R he _
      _ ≤ ‖∫ x : m ⊕ m → ℝ, (gaussE (modeVec e x) : ℂ) *
            ⟪R.W g Ψ, R.W (modeVec e x) (R.W g Ψ)⟫_ℂ‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ ∫ x : m ⊕ m → ℝ, ‖(gaussE (modeVec e x) : ℂ) *
            ⟪R.W g Ψ, R.W (modeVec e x) (R.W g Ψ)⟫_ℂ‖ := norm_integral_le_integral_norm _
      _ = gaussZ m / Real.sqrt (halfCov T e).det := by
          simp_rw [hnorm]
          exact integral_gaussE_mul_gaussE_map T he
  have hsqrtpos : 0 < Real.sqrt (halfCov T e).det := Real.sqrt_pos.2 hdetpos
  have hc1 : c * Real.sqrt (halfCov T e).det ≤ 1 := by
    have h1 : c ≤ 1 / Real.sqrt (halfCov T e).det := by
      have := le_of_mul_le_mul_left (by rw [mul_one_div]; exact hupper :
        gaussZ m * c ≤ gaussZ m * (1 / Real.sqrt (halfCov T e).det)) gaussZ_pos
      exact this
    rwa [le_div_iff₀ hsqrtpos] at h1
  calc c * Real.sqrt (1 + (∑ k, (‖T.toEquiv (e k)‖ ^ 2 + ‖T.toEquiv (I • e k)‖ ^ 2 - 2)) / 4)
      ≤ c * Real.sqrt (halfCov T e).det :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (one_add_le_halfCov_det T he)) hc0
    _ ≤ 1 := hc1

/-- **Shale's criterion, necessity**: a Bogoliubov transformation implemented in a Fock representation has a
Hilbert-Schmidt antilinear part. -/
theorem shale_necessity_of_implements [CompleteSpace h] (R : FockRep h K) (T : Bogoliubov h)
    (hT : Implements R.toCCRRep T) : IsHilbertSchmidt T.betaPart := by
  classical
  obtain ⟨Ψ, hΨ⟩ := gaussian_vector_of_implements R T hT
  have hΨ0 : Ψ ≠ 0 := by
    rintro rfl
    have := hΨ 0
    simp at this
  -- a displaced copy of `Ψ` overlaps the vacuum
  obtain ⟨g, hg⟩ : ∃ g, ⟪R.Ω, R.W g Ψ⟫_ℂ ≠ 0 := by
    by_contra hne
    have hall : ∀ g, ⟪R.Ω, R.W g Ψ⟫_ℂ = 0 := fun g => by
      by_contra hg
      exact hne ⟨g, hg⟩
    have hcyc := fockRep_cyclic R hΨ0
    rw [Submodule.topologicalClosure_eq_top_iff] at hcyc
    have hmem : R.Ω ∈ (Submodule.span ℂ (Set.range fun f => R.W f Ψ))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      induction hu using Submodule.span_induction with
      | mem y hy => obtain ⟨f, rfl⟩ := hy; exact hall f
      | zero => exact inner_zero_right _
      | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
      | smul a b _ hb => rw [inner_smul_right, hb, mul_zero]
    rw [hcyc, Submodule.mem_bot] at hmem
    have := R.norm_Ω
    rw [hmem, norm_zero] at this
    exact zero_ne_one this
  set c := ‖⟪R.Ω, R.W g Ψ⟫_ℂ‖ ^ 2 with hc
  have hc0 : 0 < c := by
    have : 0 < ‖⟪R.Ω, R.W g Ψ⟫_ℂ‖ := norm_pos_iff.2 hg
    positivity
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ h
  refine T.isHilbertSchmidt_of_finite_bound b (4 * ((1 / c) ^ 2 - 1)) fun s => ?_
  have he : Orthonormal ℂ fun k : s => b k := b.orthonormal.comp _ Subtype.val_injective
  have hmain := norm_inner_sq_mul_sqrt_le_one R T hΨ g he
  rw [Finset.sum_coe_sort s fun i => ‖T.toEquiv (b i)‖ ^ 2 + ‖T.toEquiv (I • b i)‖ ^ 2 - 2] at hmain
  set S := ∑ i ∈ s, (‖T.toEquiv (b i)‖ ^ 2 + ‖T.toEquiv (I • b i)‖ ^ 2 - 2) with hS
  by_cases hneg : 1 + S / 4 ≤ 0
  · have : (0 : ℝ) ≤ (1 / c) ^ 2 := sq_nonneg _
    linarith
  · rw [not_le] at hneg
    have h1 : Real.sqrt (1 + S / 4) ≤ 1 / c := by
      rw [le_div_iff₀ hc0, mul_comm]; exact hmain
    have h2 : 1 + S / 4 ≤ (1 / c) ^ 2 := by
      rw [← Real.sq_sqrt hneg.le]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    linarith

end Lightlike.OperatorAlgebras
