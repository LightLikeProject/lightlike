module

public import Mathlib

/-!
# The Gaussian model integral with a complex symmetric quadratic form

For a complex symmetric `n × n` matrix `A` whose quadratic form has positive real part on
nonzero real vectors (equivalently, `Re A` is positive definite), the Gaussian integral

  `G(A) = ∫_{ℝⁿ} e^{-⟨A x, x⟩ / 2} dx`

satisfies `G(A)² · det A = (2π)ⁿ` (`integral_gauss_sq_mul_det`) and, with the branch fixed,

  `G(A) = (2π)^{n/2} · invSqrtDet A`   (`integral_gauss_eq_invSqrtDet`),

where `invSqrtDet A` is the product of the principal roots `λ^{-1/2}` over the eigenvalues `λ` of
`A`. This is the model integral of the stationary phase method: Hörmander, *The Analysis of
Linear Partial Differential Operators I* (2nd ed., 1990), §7.6, Theorem 7.6.1 at `ξ = 0`, which
writes it as `(2π)^{n/2} (det A)^{-1/2}`, with the branch obtained by continuity from real
positive definite `A`. That branch is the eigenvalue product, not the principal root of `det A`:
the two differ in sign for `A = (1 + 2i) · I₃` (see `invSqrtDet`).

## Proof

Induction on `n` by completing the square in the first variable:

* `qform_cons`: `⟨A (s, w), (s, w)⟩ = a s² + 2 β(w) s + ⟨A' w, w⟩` with `a = A₀₀`,
  `β(w) = ∑ⱼ A₀ⱼ wⱼ`, and `A'` the lower right block;
* the one-variable integral over `s` is Mathlib's `integral_cexp_quadratic`, and leaves the
  Gaussian of the Schur complement `S = A' - A'₀ A₀' / a` (`integral_gauss_succ`);
* `det A = a · det S` (`det_eq_mul_det_schur0`), and `S` is again symmetric with positive real
  part (`schur0_pos`), because `⟨S w, w⟩ = ⟨A x, x⟩ + ⟨A y, y⟩` for the real and imaginary parts
  `x, y` of the complex minimiser `(-β(w)/a, w)`.

Integrability on `ℝⁿ` (needed for Fubini) follows from the coercivity bound
`μ ∑ xᵢ² ≤ Re ⟨A x, x⟩` (`exists_coercive`), obtained from the minimum on the unit sphere.

## The branch

Along the segment `A_t = (1 - t) • 1 + t • A`, `t ∈ [0, 1]`:

* the eigenvalues of `A_t` are exactly `1 - t + t λ` for the eigenvalues `λ` of `A`
  (`roots_charpoly_smul_one_add_smul`), and every eigenvalue of a symmetric matrix with positive
  definite real part has positive real part (`re_pos_of_mem_roots`), so `invSqrtDet A_t` is
  continuous in `t` (`continuousOn_invSqrtDet_path`);
* `G(A_t)` is continuous in `t` by dominated convergence (`continuousOn_integral_gauss_path`);
* both `G(A_t)` and `(2π)^{n/2} invSqrtDet A_t` square to `(2π)ⁿ / det A_t`, and they agree at
  `t = 0`, where `A_0 = 1`. Their ratio is continuous with values `±1`, hence constantly `1`.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset
open scoped Real

namespace Lightlike.Oscillatory

/-- The quadratic form `x ↦ ∑ᵢⱼ Aᵢⱼ xᵢ xⱼ` of a complex square matrix, evaluated on real
vectors. -/
def qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑ i, ∑ j, A i j * (x i : ℂ) * (x j : ℂ)

/-- The Schur complement of the entry `A₀₀`:
`Sᵢⱼ = A_{i+1, j+1} - A_{i+1, 0} A_{0, j+1} / A₀₀`. -/
noncomputable def schur0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0

/-- The quadratic form vanishes at the origin. -/
theorem qform_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : qform A 0 = 0 := by
  simp [qform]

/-- The quadratic form is homogeneous of degree two. -/
theorem qform_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x : Fin n → ℝ) :
    qform A (t • x) = (t : ℂ) ^ 2 * qform A x := by
  simp only [qform, Pi.smul_apply, smul_eq_mul, ofReal_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form is continuous. -/
theorem continuous_qform {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Continuous (qform A) := by
  unfold qform
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop

/-- Splitting off the first variable: for symmetric `A`,
`⟨A (s, w), (s, w)⟩ = A₀₀ s² + 2 (∑ⱼ A_{0, j+1} wⱼ) s + ⟨A' w, w⟩`, where `A'` is the lower
right block. -/
theorem qform_cons {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsSymm) (s : ℝ)
    (w : Fin n → ℝ) :
    qform A (Fin.cons s w) = A 0 0 * (s : ℂ) ^ 2 + 2 * (∑ j, A 0 j.succ * (w j : ℂ)) * s +
      qform (A.submatrix Fin.succ Fin.succ) w := by
  simp only [qform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, submatrix_apply,
    Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, A i.succ 0 * (w i : ℂ) * s = (∑ j, A 0 j.succ * (w j : ℂ)) * s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hA.apply 0 i.succ]
  have h2 : ∑ j : Fin n, A 0 j.succ * (s : ℂ) * (w j : ℂ) =
      (∑ j, A 0 j.succ * (w j : ℂ)) * s := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  ring

/-- The quadratic form on the first coordinate axis: `⟨A (s, 0), (s, 0)⟩ = A₀₀ s²`. -/
theorem qform_cons_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsSymm)
    (s : ℝ) : qform A (Fin.cons s 0) = A 0 0 * (s : ℂ) ^ 2 := by
  rw [qform_cons A hA, qform_zero]
  simp

/-- The quadratic form of the Schur complement is the reduced form after completing the square:
`⟨S w, w⟩ = ⟨A' w, w⟩ - (∑ⱼ A_{0, j+1} wⱼ)² / A₀₀` for symmetric `A`. -/
theorem qform_schur0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsSymm)
    (w : Fin n → ℝ) :
    qform (schur0 A) w = qform (A.submatrix Fin.succ Fin.succ) w -
      (∑ j, A 0 j.succ * (w j : ℂ)) ^ 2 / A 0 0 := by
  simp only [qform, schur0, of_apply, submatrix_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply 0 i.succ]
  ring

/-- The Schur complement of a symmetric matrix is symmetric. -/
theorem schur0_isSymm {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsSymm) :
    (schur0 A).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [schur0, of_apply, hA.apply i.succ j.succ, hA.apply 0 i.succ, hA.apply 0 j.succ]
  ring

/-- Under positivity of the real part, the pivot `A₀₀` has positive real part. -/
theorem re_pivot_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) : 0 < (A 0 0).re := by
  have hx : (Fin.cons 1 0 : Fin (n + 1) → ℝ) ≠ 0 := fun h => by
    simpa using congrFun h 0
  have := hpos _ hx
  rwa [qform_cons_zero A hA, ofReal_one, one_pow, mul_one] at this

/-- The algebraic identity behind `schur0_pos`: with `z = -β / a`,
`-β² / a = a (Re z)² + 2 β Re z + a (Im z)²`. -/
theorem neg_sq_div_eq (a β : ℂ) (ha : a ≠ 0) :
    -(β ^ 2 / a) = a * ((-β / a).re : ℂ) ^ 2 + 2 * β * ((-β / a).re : ℂ) +
      a * ((-β / a).im : ℂ) ^ 2 := by
  have hz : ((-β / a).re : ℂ) + ((-β / a).im : ℂ) * I = -β / a := re_add_im _
  generalize ((-β / a).re : ℂ) = r at hz ⊢
  generalize ((-β / a).im : ℂ) = m at hz ⊢
  have hβ : β = -(a * (r + m * I)) := by
    rw [hz]
    field_simp
  subst hβ
  have e : (-(a * (r + m * I))) ^ 2 / a = a * (r + m * I) ^ 2 := by
    rw [div_eq_iff ha]
    ring
  rw [e]
  linear_combination (-a * m ^ 2) * I_sq

/-- The Schur complement inherits positivity of the real part: if `Re ⟨A x, x⟩ > 0` for every
nonzero real `x` and `A` is symmetric, the same holds for `schur0 A`. The proof writes
`⟨S w, w⟩ = ⟨A x, x⟩ + ⟨A y, y⟩` with `x = (Re z, w)`, `y = (Im z, 0)`, `z = -β(w)/A₀₀`. -/
theorem schur0_pos {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) : ∀ w ≠ 0, 0 < (qform (schur0 A) w).re := by
  intro w hw
  have ha : 0 < (A 0 0).re := re_pivot_pos hA hpos
  have ha0 : A 0 0 ≠ 0 := fun h => by rw [h, zero_re] at ha; exact lt_irrefl 0 ha
  have key : qform (schur0 A) w =
      qform A (Fin.cons (-(∑ j, A 0 j.succ * (w j : ℂ)) / A 0 0).re w) +
        qform A (Fin.cons (-(∑ j, A 0 j.succ * (w j : ℂ)) / A 0 0).im 0) := by
    rw [qform_schur0 A hA, qform_cons A hA, qform_cons_zero A hA, sub_eq_add_neg,
      neg_sq_div_eq _ _ ha0]
    ring
  have hx : (Fin.cons (-(∑ j, A 0 j.succ * (w j : ℂ)) / A 0 0).re w : Fin (n + 1) → ℝ) ≠ 0 :=
    fun h => hw (funext fun j => by simpa using congrFun h j.succ)
  have h1 := hpos _ hx
  have h2 : 0 ≤ (qform A (Fin.cons (-(∑ j, A 0 j.succ * (w j : ℂ)) / A 0 0).im 0)).re := by
    rw [qform_cons_zero A hA, ← ofReal_pow, mul_comm, re_ofReal_mul]
    exact mul_nonneg (sq_nonneg _) ha.le
  rw [key, add_re]
  linarith

/-- Expansion of the determinant along the first column after one step of Gaussian
elimination: `det A = A₀₀ · det (schur0 A)` when `A₀₀ ≠ 0`. -/
theorem det_eq_mul_det_schur0 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ha : A 0 0 ≠ 0) : A.det = A 0 0 * (schur0 A).det := by
  let c : Fin (n + 1) → ℂ := Fin.cons 0 fun k => A k.succ 0 / A 0 0
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j => A i j - c i * A 0 j
  have hB0 : ∀ j, B 0 j = A 0 j := fun j => by simp [B, c]
  have hAB : A.det = B.det := by
    refine det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) fun i j => ?_
    rw [hB0 j]
    simp only [B, of_apply]
    ring
  have hcol : ∀ k : Fin n, B k.succ 0 = 0 := fun k => by
    simp only [B, c, of_apply, Fin.cons_succ, div_mul_cancel₀ _ ha, sub_self]
  have hsub : B.submatrix Fin.succ Fin.succ = schur0 A := by
    ext i j
    simp only [B, c, schur0, submatrix_apply, of_apply, Fin.cons_succ]
    ring
  rw [hAB, det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, hB0, hsub]

/-- Coercivity: if `Re ⟨A x, x⟩ > 0` for every nonzero real `x`, then
`μ ∑ᵢ xᵢ² ≤ Re ⟨A x, x⟩` for some `μ > 0`. The constant comes from the minimum of
`Re ⟨A x, x⟩` on the unit sphere of the sup norm. -/
theorem exists_coercive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) :
    ∃ μ > 0, ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform A x).re := by
  have hunit : ∀ x : Fin n → ℝ, x ≠ 0 → ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']
  by_cases hK : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hK
      (Complex.continuous_re.comp (continuous_qform A)).continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      rintro rfl
      simp at hx₀
    have hm : 0 < (qform A x₀).re := hpos x₀ hx₀0
    refine ⟨(qform A x₀).re / (n + 1), by positivity, fun x => ?_⟩
    have h1 : (qform A x₀).re * ‖x‖ ^ 2 ≤ (qform A x).re := by
      by_cases hx : x = 0
      · simp [hx, qform_zero]
      · have hn0 : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
        have h := isMinOn_iff.mp hmin _ (hunit x hx)
        simp only [Function.comp_apply, qform_smul, ← ofReal_pow, re_ofReal_mul] at h
        calc (qform A x₀).re * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * (qform A x).re * ‖x‖ ^ 2 := by gcongr
          _ = (qform A x).re := by field_simp
    have h2 : ∑ i, x i ^ 2 ≤ (n + 1) * ‖x‖ ^ 2 := by
      calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [← sq_abs, ← Real.norm_eq_abs]
              gcongr
              exact norm_le_pi_norm x i
        _ = n * ‖x‖ ^ 2 := by simp
        _ ≤ (n + 1) * ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    calc (qform A x₀).re / (n + 1) * ∑ i, x i ^ 2
        ≤ (qform A x₀).re / (n + 1) * ((n + 1) * ‖x‖ ^ 2) := by gcongr
      _ = (qform A x₀).re * ‖x‖ ^ 2 := by field_simp
      _ ≤ (qform A x).re := h1
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hK ⟨_, hunit x hx⟩
    simp [hx, qform_zero]

/-- The Gaussian `e^{-⟨A x, x⟩ / 2}` is integrable on `ℝⁿ` when `Re ⟨A x, x⟩ > 0` for every
nonzero real `x`. -/
theorem integrable_gauss {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) :
    Integrable (fun x : Fin n → ℝ => cexp (-qform A x / 2)) := by
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive A hpos
  have hg := GaussianFourier.integrable_cexp_neg_sum_mul_add (ι := Fin n) (b := fun _ => ((μ / 2 : ℝ) : ℂ))
    (fun _ => by rw [ofReal_re]; positivity) 0
  refine hg.mono ((continuous_qform A).neg.div_const 2).cexp.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_exp, norm_exp, Real.exp_le_exp]
  have hl : (-qform A x / 2).re = -(qform A x).re / 2 := by simp
  have hr : (-∑ i, ((μ / 2 : ℝ) : ℂ) * (x i : ℂ) ^ 2 + ∑ i, (0 : Fin n → ℂ) i * x i).re =
      -(μ / 2 * ∑ i, x i ^ 2) := by
    simp [Finset.mul_sum, ← ofReal_pow]
  rw [hl, hr]
  linarith [hcoer x]

/-- Fubini over the first coordinate: `∫_{ℝⁿ⁺¹} f = ∫_{ℝⁿ} ∫_ℝ f (s, w) ds dw` for integrable
`f`. -/
theorem integral_fin_succ_cons {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℂ) (hf : Integrable f) :
    ∫ x, f x = ∫ w : Fin n → ℝ, ∫ s : ℝ, f (Fin.cons s w) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have h1 := hmp.integral_comp' (fun p => f (e.symm p))
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  have hint : Integrable (fun p => f (e.symm p))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    rw [← Measure.volume_eq_prod, ← hmp.integrable_comp_emb e.measurableEmbedding]
    simpa [Function.comp_def] using hf
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ hint]
  simp only [he]

/-- One step of the induction: integrating out the first variable,
`G(A) = (π / (A₀₀ / 2))^{1/2} · G(schur0 A)`, where `G(A) = ∫ e^{-⟨A x, x⟩ / 2}`. -/
theorem integral_gauss_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) :
    ∫ x, cexp (-qform A x / 2) =
      (π / (A 0 0 / 2)) ^ (1 / 2 : ℂ) * ∫ w, cexp (-qform (schur0 A) w / 2) := by
  have ha : 0 < (A 0 0).re := re_pivot_pos hA hpos
  have ha0 : A 0 0 ≠ 0 := fun h => by rw [h, zero_re] at ha; exact lt_irrefl 0 ha
  rw [integral_fin_succ_cons _ (integrable_gauss A hpos), ← integral_const_mul]
  congr 1
  funext w
  have hb : (-(A 0 0 / 2)).re < 0 := by
    rw [neg_re, div_ofNat_re]
    linarith
  have hfun : (fun s : ℝ => cexp (-qform A (Fin.cons s w) / 2)) = fun s : ℝ =>
      cexp (-(A 0 0 / 2) * (s : ℂ) ^ 2 + (-(∑ j, A 0 j.succ * (w j : ℂ))) * s +
        -qform (A.submatrix Fin.succ Fin.succ) w / 2) := by
    funext s
    rw [qform_cons A hA]
    congr 1
    ring
  rw [hfun, integral_cexp_quadratic hb, neg_neg, qform_schur0 A hA]
  congr 2
  field_simp
  ring

/-- **The Gaussian model integral** (Hörmander, *ALPDO I*, §7.6, Theorem 7.6.1 at `ξ = 0`,
squared): for a complex symmetric matrix `A` with `Re ⟨A x, x⟩ > 0` for every nonzero real `x`,
`(∫_{ℝⁿ} e^{-⟨A x, x⟩ / 2} dx)² · det A = (2π)ⁿ`. -/
theorem integral_gauss_sq_mul_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsSymm)
    (hpos : ∀ x ≠ 0, 0 < (qform A x).re) :
    (∫ x, cexp (-qform A x / 2)) ^ 2 * A.det = (2 * π) ^ n := by
  induction n with
  | zero =>
    have h : (fun x : Fin 0 → ℝ => cexp (-qform A x / 2)) = fun _ => 1 := by
      funext x
      simp [qform]
    rw [h, volume_pi, Measure.pi_of_empty, integral_dirac]
    simp
  | succ n ih =>
    have ha : 0 < (A 0 0).re := re_pivot_pos hA hpos
    have ha0 : A 0 0 ≠ 0 := fun h => by rw [h, zero_re] at ha; exact lt_irrefl 0 ha
    have hsq : ((π / (A 0 0 / 2) : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = π / (A 0 0 / 2) := by
      have := cpow_nat_inv_pow (π / (A 0 0 / 2) : ℂ) (n := 2) two_ne_zero
      rwa [Nat.cast_ofNat, ← one_div] at this
    rw [integral_gauss_succ A hA hpos, det_eq_mul_det_schur0 A ha0, mul_pow]
    calc _ = ((π / (A 0 0 / 2) : ℂ) ^ (1 / 2 : ℂ)) ^ 2 * A 0 0 *
          ((∫ w, cexp (-qform (schur0 A) w / 2)) ^ 2 * (schur0 A).det) := by ring
      _ = (2 * π) ^ (n + 1) := by
        rw [hsq, ih _ (schur0_isSymm hA) (schur0_pos hA hpos), pow_succ]
        field_simp

/-! ## The branch: `G(A) = (2π)^{n/2} invSqrtDet A` -/

section Branch

open Polynomial

/-- `det(M)^{-1/2}` with the branch that the Gaussian integral selects: the product, over the
eigenvalues `λ` of `M` (the roots of the characteristic polynomial, with algebraic
multiplicity), of their principal inverse square roots `λ^{-1/2}`.

For `M` as in `integral_gauss_eq_invSqrtDet`, every eigenvalue has positive real part
(`re_pos_of_mem_roots`), so each factor is the root that is continuous on the right half-plane.

The principal root of `det M` itself is **not** this branch from `n = 3` on. Take
`M = (1 + 2i) · I₃`. The integral factorizes, `G(M) = (2π / (1 + 2i))^{3/2}`, with each
one-dimensional factor a principal root. The eigenvalue arguments sum to `3 arctan 2 ≈ 3.32 > π`,
so `det M = (1 + 2i)³ = -11 - 2i` lies just across the negative real axis, and
`(2π)^{3/2} (det M)^{-1/2} = -G(M)` (proved in `cpow_det_diagonal_wrong_branch`). The same
happens for `diag(1 + 2i, 1 + 2.5i, 1 + 3i)` and its rotations, whose arguments sum to about
`3.55` (control (b) of `scripts/oscillatory/gauss_check.py`). For `n ≤ 2` the arguments sum to
less than `π` in absolute value, and the two branches agree. This is why `G(A)` is identified
along the path `(1 - t) • 1 + t • A` rather than through `det A`. -/
noncomputable def invSqrtDet {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (M.charpoly.roots.map fun μ => μ ^ (-(1 / 2 : ℂ))).prod

/-- Under the positivity hypothesis, the real part of the quadratic form is nonnegative
everywhere. -/
theorem re_qform_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform A x).re) (x : Fin n → ℝ) :
    0 ≤ (qform A x).re := by
  by_cases hx : x = 0
  · rw [hx, qform_zero, zero_re]
  · exact (hpos x hx).le

/-- A nonzero real vector has positive squared length. -/
theorem sum_sq_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : 0 < ∑ i, x i ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa using hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi'))⟩

/-- For symmetric `A` and `v = p + i q` with `p, q` real, the Hermitian form
`∑ᵢ v̄ᵢ (A v)ᵢ` is `⟨A p, p⟩ + ⟨A q, q⟩`: the cross terms cancel by symmetry. -/
theorem sum_star_mul_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (p q : Fin n → ℝ) :
    ∑ i, star ((p i : ℂ) + q i * I) * (A *ᵥ fun j => (p j : ℂ) + q j * I) i =
      qform A p + qform A q := by
  have hstar : ∀ i, star ((p i : ℂ) + q i * I) = (p i : ℂ) - q i * I := fun i => by
    apply Complex.ext <;> simp
  have key : ∀ i j, star ((p i : ℂ) + q i * I) * (A i j * ((p j : ℂ) + q j * I)) =
      A i j * p i * p j + A i j * q i * q j +
        I * (A i j * p i * q j - A i j * q i * p j) := by
    intro i j
    rw [hstar]
    linear_combination (-A i j * q i * q j) * I_sq
  have hanti : ∑ i, ∑ j, A i j * (p i : ℂ) * q j = ∑ i, ∑ j, A i j * (q i : ℂ) * p j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA.apply j i]
    ring
  have hzero : ∑ i, ∑ j, (A i j * (p i : ℂ) * q j - A i j * q i * p j) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [hanti, sub_self]
  calc _ = ∑ i, ∑ j, (A i j * p i * p j + A i j * q i * q j) +
        I * ∑ i, ∑ j, (A i j * (p i : ℂ) * q j - A i j * q i * p j) := by
        simp only [mulVec, dotProduct, Finset.mul_sum, key, Finset.sum_add_distrib]
    _ = qform A p + qform A q := by
        rw [hzero, mul_zero, add_zero]
        simp only [qform, Finset.sum_add_distrib]

/-- Every eigenvalue of a complex symmetric matrix with positive definite real part has positive
real part. -/
theorem re_pos_of_mem_roots {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform A x).re) {μ : ℂ}
    (hμ : μ ∈ A.charpoly.roots) : 0 < μ.re := by
  rw [Polynomial.mem_roots (charpoly_monic A).ne_zero, Polynomial.IsRoot.def, eval_charpoly] at hμ
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hμ
  have hAv : ∀ i, (A *ᵥ v) i = μ * v i := fun i => by
    have h := congrFun hv i
    simp only [sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero, scalar_apply,
      mulVec_diagonal] at h
    exact h.symm
  set p : Fin n → ℝ := fun i => (v i).re
  set q : Fin n → ℝ := fun i => (v i).im
  have hvpq : (fun j => (p j : ℂ) + q j * I) = v := funext fun j => re_add_im (v j)
  have hsum := sum_star_mul_mulVec hA p q
  have hvj : ∀ j, (p j : ℂ) + q j * I = v j := fun j => re_add_im (v j)
  simp only [hvj, hAv] at hsum
  have hN : ∑ i, star (v i) * (μ * v i) = μ * ((∑ i, normSq (v i) : ℝ) : ℂ) := by
    rw [ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [normSq_eq_conj_mul_self, star_def]
    ring
  rw [hN] at hsum
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hv0
    rw [← hvpq, h.1, h.2]
    funext j
    simp
  have hre : 0 < (qform A p + qform A q).re := by
    rw [add_re]
    rcases hpq with h | h
    · linarith [hpos p h, re_qform_nonneg hpos q]
    · linarith [hpos q h, re_qform_nonneg hpos p]
  have hNpos : 0 < ∑ i, normSq (v i) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    exact Finset.sum_pos' (fun j _ => normSq_nonneg _)
      ⟨i, Finset.mem_univ _, normSq_pos.mpr (by simpa using hi)⟩
  rw [← hsum, re_mul_ofReal] at hre
  by_contra h
  nlinarith

/-- The characteristic polynomial of `c • 1 + t • A`, evaluated at `z`: its roots are
`c + t λ` for the eigenvalues `λ` of `A`. -/
theorem eval_charpoly_smul_one_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c t z : ℂ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A).charpoly.eval z =
      ((A.charpoly.roots.map fun μ => c + t * μ).map fun a => z - a).prod := by
  rw [eval_charpoly, Multiset.map_map]
  have hcard : A.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]
  rcases eq_or_ne t 0 with rfl | ht
  · have hM : scalar (Fin n) z - ((c • (1 : Matrix (Fin n) (Fin n) ℂ)) + (0 : ℂ) • A) =
        (z - c) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [h, scalar_apply, one_apply]
    rw [hM, det_smul, det_one, mul_one, Fintype.card_fin]
    simp only [Function.comp_def, zero_mul, add_zero, Multiset.map_const', Multiset.prod_replicate,
      hcard]
  · have hM : scalar (Fin n) z - (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A) =
        t • (scalar (Fin n) ((z - c) / t) - A) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp [scalar_apply, one_apply, mul_sub]
        field_simp
        ring
      · simp [h, scalar_apply, one_apply]
    rw [hM, det_smul, Fintype.card_fin, ← eval_charpoly,
      (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots, (charpoly_monic A).leadingCoeff, one_mul,
      show t ^ n = (A.charpoly.roots.map fun _ => t).prod by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard],
      ← Multiset.prod_map_mul]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun μ _ => ?_)
    simp only [Function.comp_apply]
    field_simp
    ring

/-- The eigenvalues of `c • 1 + t • A` are `c + t λ` for the eigenvalues `λ` of `A`, with
multiplicity. -/
theorem roots_charpoly_smul_one_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c t : ℂ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A).charpoly.roots =
      A.charpoly.roots.map fun μ => c + t * μ := by
  have h : (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A).charpoly =
      ((A.charpoly.roots.map fun μ => c + t * μ).map fun a => X - C a).prod := by
    refine Polynomial.funext fun z => ?_
    rw [eval_charpoly_smul_one_add_smul, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  rw [h, roots_multiset_prod_X_sub_C]

/-- `invSqrtDet` along the segment `c • 1 + t • A`. -/
theorem invSqrtDet_smul_one_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c t : ℂ) :
    invSqrtDet (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A) =
      (A.charpoly.roots.map fun μ => (c + t * μ) ^ (-(1 / 2 : ℂ))).prod := by
  rw [invSqrtDet, roots_charpoly_smul_one_add_smul, Multiset.map_map]
  rfl

/-- `invSqrtDet M` is a square root of `(det M)⁻¹` when no eigenvalue vanishes. -/
theorem invSqrtDet_sq_mul_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ μ ∈ M.charpoly.roots, μ ≠ 0) : invSqrtDet M ^ 2 * M.det = 1 := by
  rw [invSqrtDet, det_eq_prod_roots_charpoly, ← Multiset.prod_map_pow,
    show M.charpoly.roots.prod = (M.charpoly.roots.map fun μ => μ).prod by rw [Multiset.map_id'],
    ← Multiset.prod_map_mul]
  refine Multiset.prod_eq_one fun x hx => ?_
  obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
  rw [← cpow_nat_mul, show ((2 : ℕ) : ℂ) * -(1 / 2) = -1 by norm_num, cpow_neg_one,
    inv_mul_cancel₀ (h μ hμ)]


/-- For a diagonal matrix, `invSqrtDet (diagonal d) = ∏ᵢ dᵢ^{-1/2}`: the eigenvalues are the
diagonal entries (`Matrix.charpoly_diagonal`). -/
theorem invSqrtDet_diagonal {n : ℕ} (d : Fin n → ℂ) :
    invSqrtDet (diagonal d) = ∏ i, d i ^ (-(1 / 2 : ℂ)) := by
  have hroots : (diagonal d).charpoly.roots = Finset.univ.val.map d := by
    have h : (∏ i, (X - C (d i)) : ℂ[X]) =
        ((Finset.univ.val.map d).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [charpoly_diagonal, h, roots_multiset_prod_X_sub_C]
  rw [invSqrtDet, hroots, Multiset.map_map]
  rfl

/-- The quadratic form of `c • 1 + t • A`. -/
theorem qform_smul_one_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c t : ℂ)
    (x : Fin n → ℝ) :
    qform (c • (1 : Matrix (Fin n) (Fin n) ℂ) + t • A) x =
      c * ∑ i, (x i : ℂ) ^ 2 + t * qform A x := by
  simp only [qform, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [one_apply, sq, mul_assoc]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The real part of the quadratic form along the segment `(1 - t) • 1 + t • A`, `t` real. -/
theorem re_qform_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x : Fin n → ℝ) :
    (qform (((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (t : ℂ) • A) x).re =
      (1 - t) * ∑ i, x i ^ 2 + t * (qform A x).re := by
  rw [qform_smul_one_add_smul, show ∑ i, (x i : ℂ) ^ 2 = ((∑ i, x i ^ 2 : ℝ) : ℂ) by push_cast; rfl,
    add_re, ← ofReal_mul, ofReal_re, re_ofReal_mul]

/-- A uniform coercivity bound along the segment `(1 - t) • 1 + t • A`, `t ∈ [0, 1]`. -/
theorem coercive_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {μ : ℝ}
    (hcoer : ∀ x : Fin n → ℝ, μ * ∑ i, x i ^ 2 ≤ (qform A x).re) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Fin n → ℝ) :
    min 1 μ * ∑ i, x i ^ 2 ≤
      (qform (((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (t : ℂ) • A) x).re := by
  rw [re_qform_path]
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 := min_le_left 1 μ
  have h2 := min_le_right 1 μ
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h1)) hS,
    mul_nonneg (mul_nonneg ht.1 (sub_nonneg.2 h2)) hS, mul_nonneg ht.1 (sub_nonneg.2 (hcoer x))]

/-- The norm of the Gaussian integrand. -/
theorem norm_cexp_neg_qform_div_two {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℝ) :
    ‖cexp (-qform A x / 2)‖ = Real.exp (-(qform A x).re / 2) := by
  rw [Complex.norm_exp, neg_div, neg_re, div_ofNat_re, neg_div]

/-- The real part of the quadratic form of `m • 1`, `m` real. -/
theorem re_qform_ofReal_smul_one {n : ℕ} (m : ℝ) (x : Fin n → ℝ) :
    (qform ((m : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) x).re = m * ∑ i, x i ^ 2 := by
  have h := qform_smul_one_add_smul (0 : Matrix (Fin n) (Fin n) ℂ) (m : ℂ) 0 x
  rw [zero_smul, add_zero, zero_mul, add_zero] at h
  rw [h, show ∑ i, (x i : ℂ) ^ 2 = ((∑ i, x i ^ 2 : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul,
    ofReal_re]

/-- The Gaussian integral is continuous along the segment `(1 - t) • 1 + t • A`, `t ∈ [0, 1]`
(dominated convergence with the uniform coercivity bound). -/
theorem continuousOn_integral_gauss_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform A x).re) :
    ContinuousOn (fun t : ℝ => ∫ x, cexp (-qform (((1 - t : ℝ) : ℂ) •
      (1 : Matrix (Fin n) (Fin n) ℂ) + (t : ℂ) • A) x / 2)) (Set.Icc 0 1) := by
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive A hpos
  have hm0 : 0 < min 1 μ := lt_min one_pos hμ
  have hb : Integrable (fun x : Fin n → ℝ => Real.exp (-(min 1 μ * ∑ i, x i ^ 2) / 2)) := by
    have hposm : ∀ x : Fin n → ℝ, x ≠ 0 →
        0 < (qform (((min 1 μ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) x).re := fun x hx => by
      rw [re_qform_ofReal_smul_one]
      exact mul_pos hm0 (sum_sq_pos hx)
    refine (integrable_gauss _ hposm).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_cexp_neg_qform_div_two, re_qform_ofReal_smul_one]
  refine continuousOn_of_dominated
    (bound := fun x : Fin n → ℝ => Real.exp (-(min 1 μ * ∑ i, x i ^ 2) / 2)) ?_ ?_ hb ?_
  · intro t _
    exact (Complex.continuous_exp.comp ((continuous_qform _).neg.div_const 2)).aestronglyMeasurable
  · intro t ht
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_cexp_neg_qform_div_two]
    exact Real.exp_le_exp.mpr (by linarith [coercive_path A hcoer ht x])
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [qform_smul_one_add_smul]
    exact Continuous.continuousOn (by fun_prop)

/-- `invSqrtDet` is continuous along the segment `(1 - t) • 1 + t • A`, `t ∈ [0, 1]`: its factors
are `(1 - t + t λ)^{-1/2}`, and `1 - t + t λ` stays in the right half-plane. -/
theorem continuousOn_invSqrtDet_path {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform A x).re) :
    ContinuousOn (fun t : ℝ => invSqrtDet (((1 - t : ℝ) : ℂ) •
      (1 : Matrix (Fin n) (Fin n) ℂ) + (t : ℂ) • A)) (Set.Icc 0 1) := by
  simp only [invSqrtDet_smul_one_add_smul]
  refine continuousOn_multiset_prod
    (f := fun μ (t : ℝ) => (((1 - t : ℝ) : ℂ) + (t : ℂ) * μ) ^ (-(1 / 2 : ℂ))) _ fun μ hμ => ?_
  have hre := re_pos_of_mem_roots hA hpos hμ
  refine ContinuousOn.cpow_const (Continuous.continuousOn (by fun_prop)) fun t ht => ?_
  rw [mem_slitPlane_iff]
  left
  rw [add_re, ofReal_re, re_ofReal_mul]
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]
    linarith
  · nlinarith [mul_nonneg ht.1 hre.le]

/-- `(x^{n/2})² = xⁿ` for `x ≥ 0`. -/
theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ ((n : ℝ) / 2)) ^ 2 = x ^ n := by
  rw [← Real.rpow_mul_natCast hx, show (n : ℝ) / 2 * ((2 : ℕ) : ℝ) = n by push_cast; ring,
    Real.rpow_natCast]

/-- **The Gaussian model integral with its branch** (Hörmander, *ALPDO I*, §7.6, Theorem 7.6.1
at `ξ = 0`): for a complex symmetric `A` with positive definite real part,
`∫_{ℝⁿ} e^{-⟨A x, x⟩ / 2} dx = (2π)^{n/2} · invSqrtDet A`, where `invSqrtDet A` is the product of
the principal roots `λ^{-1/2}` over the eigenvalues `λ` of `A` (all in the right half-plane).

The proof follows the segment `A_t = (1 - t) • 1 + t • A`, `t ∈ [0, 1]`. Both sides are
continuous and nonvanishing on it, their squares agree (`integral_gauss_sq_mul_det` and
`invSqrtDet_sq_mul_det`), and they agree at `t = 0`, where `A_0 = 1`. So their ratio is a
continuous function with values `±1` that equals `1` at `t = 0`, hence everywhere. -/
theorem integral_gauss_eq_invSqrtDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform A x).re) :
    ∫ x, cexp (-qform A x / 2) = ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet A := by
  set P : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t =>
    ((1 - t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + (t : ℂ) • A with hP
  set u : ℝ → ℂ := fun t => ∫ x, cexp (-qform (P t) x / 2) with hu
  set v : ℝ → ℂ := fun t => ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (P t) with hv
  obtain ⟨μ, hμ, hcoer⟩ := exists_coercive A hpos
  have hPsymm : ∀ t, (P t).IsSymm := fun t => (isSymm_one.smul _).add (hA.smul _)
  have hPpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin n → ℝ, x ≠ 0 → 0 < (qform (P t) x).re :=
    fun t ht x hx => lt_of_lt_of_le (mul_pos (lt_min one_pos hμ) (sum_sq_pos hx))
      (coercive_path A hcoer ht x)
  have hC : ((((2 * π) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) ^ 2 = (2 * π) ^ n := by
    rw [← ofReal_pow, rpow_half_sq (by positivity)]
    push_cast
    ring
  have hπn : (2 * (π : ℂ)) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hu2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t ^ 2 * (P t).det = (2 * π) ^ n := fun t ht =>
    integral_gauss_sq_mul_det _ (hPsymm t) (hPpos t ht)
  have hv2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t ^ 2 * (P t).det = (2 * π) ^ n := by
    intro t ht
    have hne : ∀ μ ∈ (P t).charpoly.roots, μ ≠ 0 := fun μ hμ h => by
      have := re_pos_of_mem_roots (hPsymm t) (hPpos t ht) hμ
      rw [h, zero_re] at this
      exact lt_irrefl 0 this
    simp only [hv]
    rw [mul_pow, hC, mul_assoc, invSqrtDet_sq_mul_det _ hne, mul_one]
  have hv0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t ≠ 0 := fun t ht h =>
    hπn (by rw [← hv2 t ht, h]; ring)
  have huv : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = v t ∨ u t = -v t := by
    intro t ht
    have hdet : (P t).det ≠ 0 := fun h => hπn (by rw [← hu2 t ht, h, mul_zero])
    have h2 : u t ^ 2 = v t ^ 2 := mul_right_cancel₀ hdet ((hu2 t ht).trans (hv2 t ht).symm)
    have h3 : (u t - v t) * (u t + v t) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  set w : ℝ → ℝ := fun t => (u t / v t).re with hw
  have hw_cont : ContinuousOn w (Set.Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn
      ((continuousOn_integral_gauss_path A hpos).div
        (continuousOn_const.mul (continuousOn_invSqrtDet_path hA hpos)) hv0)
  have hwpm : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t = 1 ∨ w t = -1 := by
    intro t ht
    rcases huv t ht with h | h
    · left
      simp only [hw, h, div_self (hv0 t ht), one_re]
    · right
      simp only [hw, h, neg_div, div_self (hv0 t ht), neg_re, one_re]
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- At `t = 0`, `u 0` and `v 0` are positive reals.
  have hP0 : P 0 = 1 := by simp [hP]
  have hu0 : u 0 = ((∫ x : Fin n → ℝ, Real.exp (-(∑ i, x i ^ 2) / 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [hu, hP0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hq : qform (1 : Matrix (Fin n) (Fin n) ℂ) x = ((∑ i, x i ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp [qform, Matrix.one_apply, sq]
    simp only [hq, ofReal_exp]
    push_cast
    ring_nf
  have hr : 0 < ∫ x : Fin n → ℝ, Real.exp (-(∑ i, x i ^ 2) / 2) := by
    have hint : Integrable (fun x : Fin n → ℝ => Real.exp (-(∑ i, x i ^ 2) / 2)) := by
      have hpos1 : ∀ x : Fin n → ℝ, x ≠ 0 →
          0 < (qform (((1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) x).re := fun x hx => by
        rw [re_qform_ofReal_smul_one, one_mul]
        exact sum_sq_pos hx
      refine (integrable_gauss _ hpos1).norm.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_cexp_neg_qform_div_two, re_qform_ofReal_smul_one, one_mul]
    exact integral_exp_pos hint
  have hiv0 : invSqrtDet (P 0) = 1 := by
    simp only [hP, invSqrtDet_smul_one_add_smul]
    simp
  have hw0 : w 0 = 1 := by
    rcases hwpm 0 h0 with h | h
    · exact h
    · exfalso
      have hpos0 : 0 < w 0 := by
        simp only [hw, hu0, hv, hiv0, mul_one, ← ofReal_div, ofReal_re]
        positivity
      linarith
  have hw1 : w 1 = 1 := by
    rcases hwpm 1 h1 with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hw_cont
        (show (0 : ℝ) ∈ Set.Icc (w 1) (w 0) by rw [h, hw0]; norm_num)
      rcases hwpm s hs with h' | h' <;> rw [h'] at hs0 <;> norm_num at hs0
  have hP1 : P 1 = A := by simp [hP]
  rcases huv 1 h1 with h | h
  · simpa only [hu, hv, hP1] using h
  · exfalso
    have : w 1 = -1 := by
      simp only [hw, h, neg_div, div_self (hv0 1 h1), neg_re, one_re]
    rw [hw1] at this
    norm_num at this

end Branch

end Lightlike.Oscillatory
