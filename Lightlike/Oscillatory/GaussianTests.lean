module

public import Lightlike.Oscillatory.Gaussian

/-!
# Trust checks for the Gaussian model integral

* **Known value** (`gauss_one_sq`): for `A = 1` the theorem gives the standard Gaussian on `ℝⁿ`,
  `(∫ e^{-|x|²/2} dx)² = (2π)ⁿ`.
* **Independent cross-check** (`gauss_diagonal_mathlib`): for diagonal `A = diag(b)` with
  `Re bᵢ > 0`, the identity `G(A)² det A = (2π)ⁿ` is proved a second time from Mathlib's product
  formula `integral_cexp_neg_sum_mul_add`, without the Schur-complement induction.
* **Non-vacuity with a complex matrix** (`gauss_two_complex`): `A = [[1, i], [i, 2]]`, with
  `det A = 3`, satisfies the hypotheses and gives `G(A)² = (2π)² / 3`.
* **Wrong input** (`integral_gauss_sq_mul_det_needs_symm`): the non-symmetric
  `B = [[1, 1], [-1, 1]]` has the quadratic form of the identity, so `G(B) = 2π` but
  `det B = 2`. The identity fails, and the symmetry hypothesis cannot be dropped.
* **Wrong constant** (`gauss_one_sq_ne_pi`): `(2π)ⁿ` cannot be replaced by `πⁿ`.

For the branch, `integral_gauss_eq_invSqrtDet`:

* **Known value** (`integral_gauss_one`): `G(1) = (2π)^{n/2}`, since `invSqrtDet 1 = 1`.
* **Independent cross-check, branch included** (`gauss_diagonal_branch_mathlib`): for every
  diagonal `A = diag(b)` with `Re bᵢ > 0`, `G(A) = (2π)^{n/2} invSqrtDet A` is proved a second
  time from Mathlib's product formula, without the path argument. This covers
  `A = (1 + 2i) · I₃`, where the principal root of `det A` fails.
* **Wrong branch** (`cpow_det_diagonal_wrong_branch`, `integral_gauss_principal_det_fails`): for
  `A = (1 + 2i) · I₃` the principal root of `det A` gives `(det A)^{-1/2} = -invSqrtDet A`, so the
  formula `G(A) = (2π)^{3/2} (det A)^{-1/2}` is false for a symmetric `A` with positive definite
  real part.
* **Wrong constant** (`integral_gauss_eq_invSqrtDet_wrong_constant`): `(2π)^{n/2}` cannot be
  replaced by `π^{n/2}`.
-/

@[expose] public section

open MeasureTheory Complex Matrix Finset
open scoped Real

namespace Lightlike.Oscillatory

/-- The quadratic form of the identity matrix is `∑ᵢ xᵢ²`. -/
theorem qform_one {n : ℕ} (x : Fin n → ℝ) :
    qform (1 : Matrix (Fin n) (Fin n) ℂ) x = ∑ i, (x i : ℂ) ^ 2 := by
  simp [qform, Matrix.one_apply, sq]

/-- The identity matrix satisfies the positivity hypothesis. -/
theorem re_qform_one_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < (qform (1 : Matrix (Fin n) (Fin n) ℂ) x).re := by
  rw [qform_one]
  simp only [← ofReal_pow, ← ofReal_sum, ofReal_re]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa using hi
  calc 0 < x i ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi'))
    _ ≤ ∑ j, x j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- Known value: the standard Gaussian on `ℝⁿ`, `(∫ e^{-|x|²/2} dx)² = (2π)ⁿ`. -/
theorem gauss_one_sq {n : ℕ} :
    (∫ x : Fin n → ℝ, cexp (-qform (1 : Matrix (Fin n) (Fin n) ℂ) x / 2)) ^ 2 = (2 * π) ^ n := by
  have h := integral_gauss_sq_mul_det (1 : Matrix (Fin n) (Fin n) ℂ) isSymm_one
    (fun x hx => re_qform_one_pos x hx)
  rwa [det_one, mul_one] at h

/-- The quadratic form of a diagonal matrix is `∑ᵢ bᵢ xᵢ²`. -/
theorem qform_diagonal {n : ℕ} (b : Fin n → ℂ) (x : Fin n → ℝ) :
    qform (diagonal b) x = ∑ i, b i * (x i : ℂ) ^ 2 := by
  simp [qform, diagonal_apply, sq, mul_assoc]

/-- A diagonal matrix with entries in the right half-plane satisfies the positivity
hypothesis. -/
theorem re_qform_diagonal_pos {n : ℕ} (b : Fin n → ℂ) (hb : ∀ i, 0 < (b i).re)
    (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < (qform (diagonal b) x).re := by
  rw [qform_diagonal, re_sum]
  simp only [← ofReal_pow, re_mul_ofReal]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := by simpa using hi
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hb j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos (hb i) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi')))⟩

/-- The diagonal Gaussian from Mathlib's product formula `integral_cexp_neg_sum_mul_add`:
`G(diag b) = ∏ᵢ (π / (bᵢ / 2))^{1/2}` for `Re bᵢ > 0`. -/
theorem integral_gauss_diagonal_prod {n : ℕ} (b : Fin n → ℂ) (hb : ∀ i, 0 < (b i).re) :
    ∫ x : Fin n → ℝ, cexp (-qform (diagonal b) x / 2) = ∏ i, (π / (b i / 2)) ^ (1 / 2 : ℂ) := by
  have hb2 : ∀ i, 0 < (b i / 2).re := fun i => by rw [div_ofNat_re]; linarith [hb i]
  have hfun : (fun x : Fin n → ℝ => cexp (-qform (diagonal b) x / 2)) =
      fun x => cexp (-∑ i, b i / 2 * (x i : ℂ) ^ 2 + ∑ i, (0 : Fin n → ℂ) i * x i) := by
    funext x
    rw [qform_diagonal, neg_div, Finset.sum_div]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun, GaussianFourier.integral_cexp_neg_sum_mul_add hb2]
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Complex.exp_zero, mul_one]

/-- Independent cross-check for diagonal matrices: `G(diag b)² · det (diag b) = (2π)ⁿ` for
`Re bᵢ > 0`, proved from Mathlib's product formula `integral_cexp_neg_sum_mul_add` and not from
`integral_gauss_sq_mul_det`. -/
theorem gauss_diagonal_mathlib {n : ℕ} (b : Fin n → ℂ) (hb : ∀ i, 0 < (b i).re) :
    (∫ x : Fin n → ℝ, cexp (-qform (diagonal b) x / 2)) ^ 2 * (diagonal b).det =
      (2 * π) ^ n := by
  rw [integral_gauss_diagonal_prod b hb, det_diagonal, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, show (2 * (π : ℂ)) ^ n = ∏ _i : Fin n, (2 * π : ℂ) by simp]
  apply Finset.prod_congr rfl
  intro i _
  have hb0 : b i ≠ 0 := fun h => by have := hb i; rw [h, zero_re] at this; exact lt_irrefl 0 this
  have hsq : ((π / (b i / 2) : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = π / (b i / 2) := by
    have := cpow_nat_inv_pow (π / (b i / 2) : ℂ) (n := 2) two_ne_zero
    rwa [Nat.cast_ofNat, ← one_div] at this
  rw [hsq]
  field_simp

/-- The complex example `A = [[1, i], [i, 2]]` (`det A = 3`) satisfies the hypotheses of
`integral_gauss_sq_mul_det`, which gives `G(A)² = (2π)² / 3`. -/
theorem gauss_two_complex :
    (∫ x : Fin 2 → ℝ, cexp (-qform !![1, I; I, 2] x / 2)) ^ 2 = (2 * π) ^ 2 / 3 := by
  have hsymm : (!![1, I; I, 2] : Matrix (Fin 2) (Fin 2) ℂ).IsSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> rfl
  have hq : ∀ x : Fin 2 → ℝ, qform !![1, I; I, 2] x =
      ((x 0 ^ 2 + 2 * x 1 ^ 2 : ℝ) : ℂ) + ((2 * x 0 * x 1 : ℝ) : ℂ) * I := fun x => by
    simp [qform, Fin.sum_univ_two]
    ring
  have hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < (qform !![1, I; I, 2] x).re := by
    intro x hx
    rw [hq, add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero, add_zero]
    have h01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    rcases h01 with h | h
    · nlinarith [lt_of_le_of_ne (sq_nonneg (x 0)) (Ne.symm (pow_ne_zero 2 h)), sq_nonneg (x 1)]
    · nlinarith [lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h)), sq_nonneg (x 0)]
  have h := integral_gauss_sq_mul_det _ hsymm hpos
  have hdet : (!![1, I; I, 2] : Matrix (Fin 2) (Fin 2) ℂ).det = 3 := by
    rw [det_fin_two_of, I_mul_I]
    ring
  rw [hdet] at h
  rw [eq_div_iff (by norm_num)]
  exact h

/-- The non-symmetric matrix `[[1, 1], [-1, 1]]` has the quadratic form of the identity. -/
theorem qform_nonsymm :
    qform (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) = qform (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  funext x
  simp [qform, Fin.sum_univ_two, Matrix.one_apply]
  ring

/-- Wrong input: for the non-symmetric `B = [[1, 1], [-1, 1]]`, `G(B)² det B = 2 (2π)²`, twice
the value `(2π)²` of `integral_gauss_sq_mul_det`. -/
theorem gauss_sq_mul_det_nonsymm :
    (∫ x : Fin 2 → ℝ, cexp (-qform (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) x / 2)) ^ 2 *
        (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ).det = 2 * (2 * π) ^ 2 := by
  rw [qform_nonsymm, gauss_one_sq, det_fin_two_of]
  ring

/-- The symmetry hypothesis of `integral_gauss_sq_mul_det` cannot be dropped: without it the
identity fails for `[[1, 1], [-1, 1]]`, which satisfies the positivity hypothesis. -/
theorem integral_gauss_sq_mul_det_needs_symm :
    ¬ ∀ A : Matrix (Fin 2) (Fin 2) ℂ, (∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < (qform A x).re) →
      (∫ x : Fin 2 → ℝ, cexp (-qform A x / 2)) ^ 2 * A.det = (2 * π) ^ 2 := by
  intro h
  have hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 →
      0 < (qform (!![1, 1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ) x).re := fun x hx => by
    rw [qform_nonsymm]
    exact re_qform_one_pos x hx
  have h1 := h _ hpos
  rw [gauss_sq_mul_det_nonsymm] at h1
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h0 : (2 * (π : ℂ)) ^ 2 = 0 := by linear_combination h1
  exact pow_ne_zero 2 (mul_ne_zero two_ne_zero hπ) h0

/-- Wrong constant: in one dimension `G(1)² = 2π ≠ π`, so `(2π)ⁿ` cannot be replaced by `πⁿ`. -/
theorem gauss_one_sq_ne_pi :
    (∫ x : Fin 1 → ℝ, cexp (-qform (1 : Matrix (Fin 1) (Fin 1) ℂ) x / 2)) ^ 2 ≠ π ^ 1 := by
  rw [gauss_one_sq, pow_one, pow_one]
  intro h
  have : (π : ℂ) = 0 := by linear_combination h
  exact ofReal_ne_zero.mpr Real.pi_ne_zero this

/-! ## The branch: trust checks for `integral_gauss_eq_invSqrtDet` -/

/-- `invSqrtDet 1 = 1`: every eigenvalue of the identity is `1`. -/
theorem invSqrtDet_one {n : ℕ} : invSqrtDet (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [← diagonal_one, invSqrtDet_diagonal]
  simp

/-- Known value: the standard Gaussian on `ℝⁿ`, `∫ e^{-|x|²/2} dx = (2π)^{n/2}`. -/
theorem integral_gauss_one {n : ℕ} :
    ∫ x : Fin n → ℝ, cexp (-qform (1 : Matrix (Fin n) (Fin n) ℂ) x / 2) =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) := by
  rw [integral_gauss_eq_invSqrtDet 1 isSymm_one (fun x hx => re_qform_one_pos x hx),
    invSqrtDet_one, mul_one]

/-- `(π / (b / 2))^{1/2} = (2π)^{1/2} b^{-1/2}` for `Re b > 0`, with principal roots. -/
theorem cpow_pi_div_half (b : ℂ) (hb : 0 < b.re) :
    (π / (b / 2) : ℂ) ^ (1 / 2 : ℂ) = (((2 * π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * b ^ (-(1 / 2 : ℂ)) := by
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_re] at hb; exact lt_irrefl 0 hb
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have harg : b.arg ≠ π := fun h => by rw [arg_eq_pi_iff] at h; linarith [h.1]
  have heq : (π / (b / 2) : ℂ) = ((2 * π : ℝ) : ℂ) * b⁻¹ := by
    push_cast
    field_simp
  rw [heq, cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr h2π.ne') (inv_ne_zero hb0)),
    log_ofReal_mul h2π (inv_ne_zero hb0), add_mul, Complex.exp_add,
    ← cpow_def_of_ne_zero (inv_ne_zero hb0), inv_cpow _ _ harg, ← cpow_neg, ofReal_cpow h2π.le,
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr h2π.ne'), ← ofReal_log h2π.le]
  push_cast
  ring_nf

/-- Independent cross-check of `integral_gauss_eq_invSqrtDet` for diagonal matrices, branch
included: `G(diag b) = (2π)^{n/2} invSqrtDet (diag b)` for `Re bᵢ > 0`, proved from Mathlib's
product formula and not from the path argument. -/
theorem gauss_diagonal_branch_mathlib {n : ℕ} (b : Fin n → ℂ) (hb : ∀ i, 0 < (b i).re) :
    ∫ x : Fin n → ℝ, cexp (-qform (diagonal b) x / 2) =
      ((2 * π) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (diagonal b) := by
  rw [integral_gauss_diagonal_prod b hb, invSqrtDet_diagonal,
    Finset.prod_congr rfl fun i _ => cpow_pi_div_half (b i) (hb i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ofReal_pow,
    ← Real.rpow_mul_natCast (by positivity)]
  congr 3
  ring

/-- The principal root `x^{1/2}` has nonnegative real part. -/
theorem re_cpow_half_nonneg (x : ℂ) : 0 ≤ (x ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_cpow (by norm_num), zero_re]
  · rw [cpow_def_of_ne_zero hx, exp_re]
    have him : (log x * (1 / 2 : ℂ)).im = arg x / 2 := by
      rw [mul_im, log_im]
      norm_num
      ring
    rw [him]
    refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
    · linarith [neg_pi_lt_arg x]
    · linarith [arg_le_pi x]

/-- **Wrong branch.** For `A = (1 + 2i) · I₃`, the principal root of `det A` gives the negative
of `invSqrtDet A`: `(det A)^{-1/2} = -invSqrtDet A`. With `integral_gauss_eq_invSqrtDet`, the
"formula" `(2π)^{3/2} (det A)^{-1/2}` therefore equals `-G(A)`. The eigenvalue arguments sum to
`3 arctan 2 > π`. -/
theorem cpow_det_diagonal_wrong_branch :
    (diagonal fun _ : Fin 3 => (1 + 2 * I : ℂ)).det ^ (-(1 / 2 : ℂ)) =
      -invSqrtDet (diagonal fun _ : Fin 3 => (1 + 2 * I : ℂ)) := by
  rw [det_diagonal, invSqrtDet_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [cpow_neg, cpow_neg, inv_pow, neg_inv]
  congr 1
  set c : ℂ := 1 + 2 * I with hc
  set r := c ^ (1 / 2 : ℂ) with hr
  set s := (c ^ 3) ^ (1 / 2 : ℂ) with hs
  have hsq : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    have := cpow_nat_inv_pow z (n := 2) two_ne_zero
    rwa [Nat.cast_ofNat, ← one_div] at this
  have hr2 : r ^ 2 = c := hsq c
  have hs2 : s ^ 2 = c ^ 3 := hsq (c ^ 3)
  have h1 : r.re * r.re - r.im * r.im = 1 := by
    have := congrArg Complex.re hr2
    simpa [sq, hc] using this
  have h2 : r.re * r.im + r.im * r.re = 2 := by
    have := congrArg Complex.im hr2
    simpa [sq, hc] using this
  have ha : 0 ≤ r.re := re_cpow_half_nonneg c
  have hsre : 0 ≤ s.re := re_cpow_half_nonneg (c ^ 3)
  have hr3 : (r ^ 3).re = r.re - 2 * r.im := by
    rw [show r ^ 3 = r * r * r by ring, mul_re, mul_re, mul_im, h1, h2]
    ring
  have hneg : (r ^ 3).re < 0 := by
    rw [hr3]
    have hab : r.re * r.im = 1 := by linear_combination h2 / 2
    have hapos : 0 < r.re := lt_of_le_of_ne ha fun h => by rw [← h, zero_mul] at hab; norm_num at hab
    have ht : r.re ^ 2 * (r.re ^ 2 - 1) = 1 := by
      have him2 : r.im ^ 2 = r.re ^ 2 - 1 := by linear_combination -h1
      rw [← him2]
      linear_combination (r.re * r.im + 1) * hab
    have ha2 : r.re ^ 2 < 2 := by nlinarith [ht, sq_nonneg (r.re ^ 2 - 2)]
    nlinarith
  have hfac : (s - r ^ 3) * (s + r ^ 3) = 0 := by
    linear_combination hs2 - (r ^ 4 + r ^ 2 * c + c ^ 2) * hr2
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    have : s = r ^ 3 := by linear_combination h
    rw [this] at hsre
    linarith
  · linear_combination h

/-- **Wrong branch, integral form.** The principal root of the determinant does not give the
Gaussian integral: `G(A) = (2π)^{3/2} (det A)^{-1/2}` fails for `A = (1 + 2i) · I₃`, which is
symmetric with positive definite real part. There `(2π)^{3/2} (det A)^{-1/2} = -G(A) ≠ G(A)`. -/
theorem integral_gauss_principal_det_fails :
    ¬ ∀ A : Matrix (Fin 3) (Fin 3) ℂ, A.IsSymm → (∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < (qform A x).re) →
      ∫ x, cexp (-qform A x / 2) = ((2 * π) ^ ((3 : ℝ) / 2) : ℝ) * A.det ^ (-(1 / 2 : ℂ)) := by
  intro h
  have hre : ∀ _ : Fin 3, 0 < (1 + 2 * I : ℂ).re := fun _ => by simp
  have hsymm := isSymm_diagonal (fun _ : Fin 3 => (1 + 2 * I : ℂ))
  have hpos := re_qform_diagonal_pos _ hre
  have h1 := h _ hsymm hpos
  have h2 := integral_gauss_eq_invSqrtDet _ hsymm hpos
  rw [cpow_det_diagonal_wrong_branch] at h1
  simp only [Nat.cast_ofNat] at h2
  have hK : ((((2 * π) ^ ((3 : ℝ) / 2)) : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hinv : invSqrtDet (diagonal fun _ : Fin 3 => (1 + 2 * I : ℂ)) ≠ 0 := by
    rw [invSqrtDet_diagonal, Finset.prod_ne_zero_iff]
    intro i _ hz
    rw [cpow_eq_zero_iff] at hz
    have := hre i
    rw [hz.1, zero_re] at this
    exact lt_irrefl 0 this
  have h0 : (2 : ℂ) * ((((2 * π) ^ ((3 : ℝ) / 2)) : ℝ) : ℂ) *
      invSqrtDet (diagonal fun _ : Fin 3 => (1 + 2 * I : ℂ)) = 0 := by
    linear_combination h2.symm.trans h1
  rcases mul_eq_zero.mp h0 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · exact two_ne_zero h4
    · exact hK h4
  · exact hinv h3

/-- Wrong constant: `(2π)^{n/2}` in `integral_gauss_eq_invSqrtDet` cannot be replaced by
`π^{n/2}`; already for `n = 1` and `A = 1` this would give `2π = π`. -/
theorem integral_gauss_eq_invSqrtDet_wrong_constant :
    ¬ ∀ n : ℕ, ∫ x : Fin n → ℝ, cexp (-qform (1 : Matrix (Fin n) (Fin n) ℂ) x / 2) =
      ((π ^ ((n : ℝ) / 2) : ℝ) : ℂ) * invSqrtDet (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have h1 := h 1
  rw [integral_gauss_one, invSqrtDet_one, mul_one] at h1
  have h2 := congrArg (· ^ 2) (ofReal_injective h1)
  simp only [rpow_half_sq (by positivity : (0 : ℝ) ≤ 2 * π), rpow_half_sq Real.pi_pos.le,
    pow_one] at h2
  linarith [Real.pi_pos]

end Lightlike.Oscillatory
