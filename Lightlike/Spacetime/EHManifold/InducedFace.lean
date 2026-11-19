import Mathlib.LinearAlgebra.Matrix.Adjugate
import Lightlike.Spacetime.EHManifold.GibbonsHawkingYork

/-!
# The induced metric, unit conormal and second fundamental form of a coordinate hyperplane

For a coordinate metric `g` on `ℝⁿ⁺¹` and the hyperplane `x^i = const`:

* `inducedMetric g i x`: the induced metric, the `n × n` submatrix of `g x` without the `i`-th row and column;
  its determinant is `det g · g^{ii}` (`det_inducedMetric`) and its inverse is
  `g^{ab} - g^{ai} g^{bi} / g^{ii}` restricted to the tangential indices (`inv_inducedMetric`);
* `conormal g i`: the unit conormal `n_β = δ^i_β / √|g^{ii}|`; `secondFF g i x a b = (∇_a n_b)` for tangential
  indices is `-Γ^i_{ab} / √|g^{ii}|` (`covDerivConormal_tangential`);
* `meanCurv g i x`: the trace of the second fundamental form with the inverse induced metric.

`ghyDensity_eq_induced`: the Gibbons–Hawking–York density of `GibbonsHawkingYork.lean` is
`2 √|det h| K` with `h` the induced metric and `K` the mean curvature: the coordinate expressions used there
are the induced ones.

## References

* E. Dyer, K. Hinterbichler, *Boundary Terms, Variational Principles and Higher Derivative Modified Gravity*,
  arXiv:0809.4033, section 4, eqs. (4.1), (4.3), p. 20.
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The submatrix of a square matrix without the `i`-th row and column. -/
def faceSub (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℝ :=
  A.submatrix i.succAbove i.succAbove

/-- The diagonal entry of the inverse is a principal minor over the determinant. -/
lemma inv_apply_diag (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    A⁻¹ i i = (faceSub A i).det / A.det := by
  have hpow : (-1 : ℝ) ^ ((i : ℕ) + (i : ℕ)) = 1 := Even.neg_one_pow ⟨i, rfl⟩
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul,
    Ring.inverse_eq_inv', hpow, one_mul]
  unfold faceSub
  rw [div_eq_mul_inv, mul_comm]

/-- **The determinant of the induced matrix**: `det (A without row and column i) = det A · (A⁻¹)_{ii}`. -/
lemma det_faceSub (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) (hA : A.det ≠ 0) :
    (faceSub A i).det = A.det * A⁻¹ i i := by
  rw [inv_apply_diag]
  field_simp

/-- **The inverse of the induced matrix** is `A⁻¹_{ab} - A⁻¹_{ai} A⁻¹_{bi} / A⁻¹_{ii}` on the remaining
indices, for a matrix with symmetric inverse. -/
lemma inv_faceSub (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) (hA : A.det ≠ 0)
    (hinv : ∀ a b, A⁻¹ a b = A⁻¹ b a) (hii : A⁻¹ i i ≠ 0) :
    (faceSub A i)⁻¹ = Matrix.of fun a b : Fin n =>
      A⁻¹ (i.succAbove a) (i.succAbove b) -
        A⁻¹ (i.succAbove a) i * A⁻¹ (i.succAbove b) i / A⁻¹ i i := by
  refine Matrix.inv_eq_right_inv ?_
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hA)
  have hrow : ∀ (r : Fin (n + 1)) (c : Fin (n + 1)),
      A r i * A⁻¹ i c + ∑ j : Fin n, A r (i.succAbove j) * A⁻¹ (i.succAbove j) c =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) r c := by
    intro r c
    rw [← hAA, Matrix.mul_apply, Fin.sum_univ_succAbove _ i]
  ext a b
  have h1 := hrow (i.succAbove a) (i.succAbove b)
  have h2 := hrow (i.succAbove a) i
  rw [Matrix.one_apply_ne (Fin.succAbove_ne i a)] at h2
  have hone : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i.succAbove a) (i.succAbove b) =
      (1 : Matrix (Fin n) (Fin n) ℝ) a b := by
    by_cases hab : a = b
    · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hab,
        Matrix.one_apply_ne fun h => hab (Fin.succAbove_right_injective h)]
  rw [hone] at h1
  rw [Matrix.mul_apply]
  simp only [faceSub, Matrix.submatrix_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
  have h3 : ∑ j : Fin n, A (i.succAbove a) (i.succAbove j) *
        (A⁻¹ (i.succAbove j) i * A⁻¹ (i.succAbove b) i / A⁻¹ i i) =
      (∑ j : Fin n, A (i.succAbove a) (i.succAbove j) * A⁻¹ (i.succAbove j) i) *
        (A⁻¹ (i.succAbove b) i / A⁻¹ i i) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3]
  have h4 : ∑ j : Fin n, A (i.succAbove a) (i.succAbove j) * A⁻¹ (i.succAbove j) i =
      -(A (i.succAbove a) i * A⁻¹ i i) := by linarith
  have h5 : ∑ j : Fin n, A (i.succAbove a) (i.succAbove j) * A⁻¹ (i.succAbove j) (i.succAbove b) =
      (1 : Matrix (Fin n) (Fin n) ℝ) a b - A (i.succAbove a) i * A⁻¹ i (i.succAbove b) := by linarith
  rw [h4, h5, hinv i (i.succAbove b)]
  field_simp
  ring

/-- **The induced metric** of the hyperplane `x^i = const`. -/
def inducedMetric (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  faceSub (g x) i

/-- **The unit conormal** `n_β = δ^i_β / √|g^{ii}|` of the hyperplanes `x^i = const`. -/
def conormal (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (β : Fin (n + 1)) (y : Fin (n + 1) → ℝ) : ℝ :=
  if β = i then 1 / √|(g y)⁻¹ i i| else 0

/-- The covariant derivative `∇_α n_β = ∂_α n_β - Γ^μ_{αβ} n_μ` of the unit conormal. -/
def covDerivConormal (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (α β : Fin (n + 1)) : ℝ :=
  pd α (conormal g i β) x - ∑ μ, christoffel g μ α β x * conormal g i μ x

/-- **The second fundamental form** of the hyperplane `x^i = const`: `K_{ab} = ∇_a n_b` for tangential
indices. -/
def secondFF (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (a b : Fin n) : ℝ :=
  covDerivConormal g i x (i.succAbove a) (i.succAbove b)

/-- For tangential indices, `∇_a n_b = -Γ^i_{ab} / √|g^{ii}|`. -/
lemma secondFF_eq (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) (a b : Fin n) :
    secondFF g i x a b =
      -(1 / √|(g x)⁻¹ i i|) * christoffel g i (i.succAbove a) (i.succAbove b) x := by
  have hzero : conormal g i (i.succAbove b) = fun _ => (0 : ℝ) := by
    funext y
    simp only [conormal, if_neg (Fin.succAbove_ne i b)]
  have hsum : ∑ μ, christoffel g μ (i.succAbove a) (i.succAbove b) x * conormal g i μ x =
      christoffel g i (i.succAbove a) (i.succAbove b) x * (1 / √|(g x)⁻¹ i i|) := by
    rw [Finset.sum_eq_single i]
    · simp only [conormal, if_true]
    · intro μ _ hμ
      simp only [conormal, if_neg hμ, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  unfold secondFF covDerivConormal
  rw [hzero, hsum]
  unfold pd
  simp
  ring

/-- **The mean curvature** `K = h^{ab} K_{ab}` of the hyperplane `x^i = const`: the trace of the second
fundamental form with the inverse of the induced metric. -/
def meanCurv (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ a, ∑ b, (inducedMetric g i x)⁻¹ a b * secondFF g i x a b

/-- **The mean curvature is the coordinate expression `faceK`.** -/
theorem meanCurv_eq_faceK (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (hdet : (g x).det ≠ 0)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hii : (g x)⁻¹ i i ≠ 0) :
    meanCurv g i x = faceK g i x := by
  have hfull : ∑ α, ∑ β, faceHup g i x α β * christoffel g i α β x =
      ∑ a : Fin n, ∑ b : Fin n, faceHup g i x (i.succAbove a) (i.succAbove b) *
        christoffel g i (i.succAbove a) (i.succAbove b) x := by
    rw [Fin.sum_univ_succAbove _ i]
    have h0 : ∑ β, faceHup g i x i β * christoffel g i i β x = 0 :=
      Finset.sum_eq_zero fun β _ => by rw [faceHup_left g i x hii hinv β, zero_mul]
    rw [h0, zero_add]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_succAbove _ i, faceHup_right g i x hii, zero_mul, zero_add]
  unfold meanCurv faceK inducedMetric
  rw [hfull, inv_faceSub (g x) i hdet hinv hii, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [secondFF_eq, Matrix.of_apply]
  unfold faceHup
  ring

/-- **The Gibbons–Hawking–York density is `2 √|det h| K`**, with `h` the induced metric of the hyperplane
and `K` its mean curvature. -/
theorem ghyDensity_eq_induced (g : (Fin (n + 1) → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) (hdet : (g x).det ≠ 0)
    (hinv : ∀ a b, (g x)⁻¹ a b = (g x)⁻¹ b a) (hii : (g x)⁻¹ i i ≠ 0) :
    ghyDensity g i x = 2 * √|(inducedMetric g i x).det| * meanCurv g i x := by
  unfold ghyDensity inducedMetric
  rw [meanCurv_eq_faceK g i x hdet hinv hii, det_faceSub (g x) i hdet, abs_mul,
    Real.sqrt_mul (abs_nonneg _)]
  ring

end Lightlike
