import Mathlib

/-!
# The determinant bound of the necessity part of Shale's criterion

Helper for `T-OP2-P6` (`Tasks/OP/T_OP2_P6.lean`). Let `A = [[P, Q], [Qᵀ, R]]` be a real symmetric matrix on
`m ⊕ m` such that the complex matrix `A + i Ω`, `Ω = [[0, 1], [-1, 0]]`, is positive semidefinite (for the
quadratic form `‖T f‖²` of a symplectic map this is the Gram matrix of the vectors `T eₖ`, `T (i eₖ)`). Then

`det (1 + A) ≥ 4ⁿ (1 + (tr A - 2 n) / 4)`, `n = card m`.

Proof. Conjugation with `U = [[1, i], [1, -i]]` (`U Uᴴ = 2`) turns `A + i Ω` into `[[E, B], [Bᴴ, D - 4]]` and
`1 + A` into `[[E, B], [Bᴴ, D]]`; the transpose of `A + i Ω` gives `E - 4 ≥ 0` in the same way. The Schur
complement `D - 4 - Bᴴ E⁻¹ B` is then positive semidefinite, so
`4ⁿ det (1 + A) = det E · det (4 + (D - 4 - Bᴴ E⁻¹ B)) ≥ 4ⁿ (1 + tr (E - 4) / 4) · 4ⁿ`, by
`det (4 + X) ≥ 4ⁿ (1 + tr X / 4)` for a positive semidefinite `X`.
-/

namespace Lightlike.OperatorAlgebras

open Matrix Complex
open scoped ComplexOrder

/-- `1 + ∑ aᵢ ≤ ∏ (1 + aᵢ)` for nonnegative reals. -/
lemma one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
    nlinarith [ha i, mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one (ha i)),
      mul_nonneg (ha i) h1]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a positive semidefinite complex matrix `X`, `det (4 + X)` is a real number, at least
`4ⁿ (1 + tr X / 4)`. -/
lemma det_four_add_of_posSemidef (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    ∃ r : ℝ, ((4 : ℂ) • (1 : Matrix n n ℂ) + X).det = (r : ℂ) ∧
      (4 : ℝ) ^ Fintype.card n * (1 + X.trace.re / 4) ≤ r ∧ (4 : ℝ) ^ Fintype.card n ≤ r := by
  have hH := hX.isHermitian
  set ev := hH.eigenvalues with hev
  have hnn : ∀ i, 0 ≤ ev i := fun i => hX.eigenvalues_nonneg i
  have hdet : ((4 : ℂ) • (1 : Matrix n n ℂ) + X).det = ((∏ i, (4 + ev i) : ℝ) : ℂ) := by
    have h1 : (4 : ℂ) • (1 : Matrix n n ℂ) + X = -(scalar n (-4 : ℂ) - X) := by
      rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul]; abel
    rw [h1, det_neg, ← eval_charpoly, hH.charpoly_eq, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      RCLike.ofReal_eq_complex_ofReal]
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  have htr : X.trace.re = ∑ i, ev i := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_sum, Complex.ofReal_re]
    rfl
  have hprod : (∏ i, (4 + ev i) : ℝ) = 4 ^ Fintype.card n * ∏ i, (1 + ev i / 4) := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hle := one_add_sum_le_prod_one_add Finset.univ (fun i => ev i / 4) fun i => by
    have := hnn i; positivity
  have hsum : 0 ≤ ∑ i, ev i := Finset.sum_nonneg fun i _ => hnn i
  refine ⟨∏ i, (4 + ev i), hdet, ?_, ?_⟩
  · rw [hprod, htr]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    simpa [Finset.sum_div] using hle
  · rw [hprod]
    refine le_mul_of_one_le_right (by positivity) ?_
    refine le_trans ?_ hle
    have : 0 ≤ ∑ i, ev i / 4 := Finset.sum_nonneg fun i _ => by have := hnn i; positivity
    linarith

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The complex matrix `A + i Ω` of a real block matrix `A = [[P, Q], [Qᵀ, R]]` and the standard symplectic
matrix `Ω = [[0, 1], [-1, 0]]`. -/
noncomputable def uncertaintyMatrix (P Q R : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks (P.map ofReal) (Q.map ofReal + I • (1 : Matrix m m ℂ))
    (Qᵀ.map ofReal - I • (1 : Matrix m m ℂ)) (R.map ofReal)

/-- The matrix `U = [[1, i], [1, -i]]` that diagonalises the complex structure. -/
noncomputable def cayleyBlock (m : Type*) [DecidableEq m] : Matrix (m ⊕ m) (m ⊕ m) ℂ :=
  fromBlocks 1 (I • (1 : Matrix m m ℂ)) 1 (-(I • (1 : Matrix m m ℂ)))

omit [Fintype m] in
lemma cayleyBlock_conjTranspose :
    (cayleyBlock m)ᴴ = fromBlocks 1 1 (-(I • (1 : Matrix m m ℂ))) (I • (1 : Matrix m m ℂ)) := by
  simp [cayleyBlock, fromBlocks_conjTranspose, conjTranspose_smul]

/-- The conjugate `U [[a, b], [c, d]] Uᴴ` in blocks. -/
lemma cayleyBlock_conj (a b c d : Matrix m m ℂ) :
    cayleyBlock m * fromBlocks a b c d * (cayleyBlock m)ᴴ =
      fromBlocks (a + d + I • (c - b)) (a - d + I • (c + b))
        (a - d - I • (c + b)) (a + d - I • (c - b)) := by
  rw [cayleyBlock_conjTranspose, cayleyBlock, fromBlocks_multiply, fromBlocks_multiply]
  have hI : (I : ℂ) * I = -1 := I_mul_I
  congr 1 <;>
  · ext i j
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.neg_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg]
    first | linear_combination (d i j) * hI | linear_combination (-(d i j)) * hI

lemma det_cayleyBlock_mul :
    (cayleyBlock m).det * (cayleyBlock m)ᴴ.det = (4 : ℂ) ^ Fintype.card m := by
  rw [← det_mul]
  have h := cayleyBlock_conj (m := m) 1 0 0 1
  rw [fromBlocks_one, Matrix.mul_one] at h
  rw [h]
  have h2 : fromBlocks ((1 : Matrix m m ℂ) + 1 + I • (0 - 0)) (1 - 1 + I • (0 + 0))
      (1 - 1 - I • (0 + 0)) (1 + 1 - I • (0 - 0)) = (2 : ℂ) • (1 : Matrix (m ⊕ m) (m ⊕ m) ℂ) := by
    rw [← fromBlocks_one, fromBlocks_smul]
    congr 1 <;> simp [two_smul]
  rw [h2, det_smul, det_one, mul_one, Fintype.card_sum, ← two_mul, pow_mul]
  norm_num

/-- **The determinant bound.** If `A = [[P, Q], [Qᵀ, R]]` is real with `P`, `R` symmetric and `A + i Ω` is
positive semidefinite, then `4ⁿ (1 + (tr P + tr R - 2 n) / 4) ≤ det (1 + A)`. -/
theorem four_pow_mul_le_det_one_add (P Q R : Matrix m m ℝ) (hP : Pᵀ = P) (hR : Rᵀ = R)
    (hG : (uncertaintyMatrix P Q R).PosSemidef) :
    (4 : ℝ) ^ Fintype.card m * (1 + (P.trace + R.trace - 2 * Fintype.card m) / 4) ≤
      (1 + fromBlocks P Q Qᵀ R).det := by
  set Pc : Matrix m m ℂ := P.map ofReal with hPc
  set Qc : Matrix m m ℂ := Q.map ofReal with hQc
  set Rc : Matrix m m ℂ := R.map ofReal with hRc
  have hQt : Qᵀ.map ofReal = Qcᵀ := by rw [hQc, transpose_map]
  have hPt : Pcᵀ = Pc := by rw [hPc, ← transpose_map, hP]
  have hRt : Rcᵀ = Rc := by rw [hRc, ← transpose_map, hR]
  -- the three conjugated matrices
  set E : Matrix m m ℂ := Pc + Rc + I • (Qcᵀ - Qc) + (2 : ℂ) • 1 with hE
  set B : Matrix m m ℂ := Pc - Rc + I • (Qcᵀ + Qc) with hB
  set D : Matrix m m ℂ := Pc + Rc - I • (Qcᵀ - Qc) + (2 : ℂ) • 1 with hD
  have hI : (I : ℂ) * I = -1 := I_mul_I
  -- `U (A + i Ω) Uᴴ`
  have h1 : cayleyBlock m * uncertaintyMatrix P Q R * (cayleyBlock m)ᴴ =
      fromBlocks E B (Pc - Rc - I • (Qcᵀ + Qc)) (D - (4 : ℂ) • 1) := by
    rw [uncertaintyMatrix, hQt, ← hPc, ← hQc, ← hRc, cayleyBlock_conj]
    congr 1 <;>
    · ext i j
      simp only [hE, hD, hB, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      first | linear_combination (2 * (1 : Matrix m m ℂ) i j) * hI |
        linear_combination (-2 * (1 : Matrix m m ℂ) i j) * hI |
        linear_combination ((1 : Matrix m m ℂ) i j) * hI | linear_combination (-(1 : Matrix m m ℂ) i j) * hI | ring
  -- `U (A + i Ω)ᵀ Uᴴ`
  have h2 : cayleyBlock m * (uncertaintyMatrix P Q R)ᵀ * (cayleyBlock m)ᴴ =
      fromBlocks (E - (4 : ℂ) • 1) B (Pc - Rc - I • (Qcᵀ + Qc)) D := by
    rw [uncertaintyMatrix, hQt, ← hPc, ← hQc, ← hRc, fromBlocks_transpose, cayleyBlock_conj]
    simp only [transpose_add, transpose_sub, transpose_smul, transpose_transpose, transpose_one, hPt, hRt]
    congr 1 <;>
    · ext i j
      simp only [hE, hD, hB, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      first | linear_combination (2 * (1 : Matrix m m ℂ) i j) * hI |
        linear_combination (-2 * (1 : Matrix m m ℂ) i j) * hI |
        linear_combination ((1 : Matrix m m ℂ) i j) * hI | linear_combination (-(1 : Matrix m m ℂ) i j) * hI | ring
  -- `U (1 + A) Uᴴ`
  have h3 : cayleyBlock m * (1 + fromBlocks Pc Qc Qcᵀ Rc) * (cayleyBlock m)ᴴ =
      fromBlocks E B (Pc - Rc - I • (Qcᵀ + Qc)) D := by
    rw [← fromBlocks_one, fromBlocks_add, cayleyBlock_conj]
    congr 1 <;>
    · ext i j
      simp only [hE, hD, hB, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply]
      ring
  have hBH : Pc - Rc - I • (Qcᵀ + Qc) = Bᴴ := by
    have hcc : ∀ M : Matrix m m ℝ, (M.map ofReal : Matrix m m ℂ)ᴴ = (Mᵀ).map ofReal := fun M => by
      ext i j; simp [conjTranspose_apply]
    have hPh : Pcᴴ = Pc := by rw [hPc, hcc, hP]
    have hRh : Rcᴴ = Rc := by rw [hRc, hcc, hR]
    have hQh : Qcᴴ = Qcᵀ := by rw [hQc, hcc, transpose_map]
    have hQth : Qcᵀᴴ = Qc := by rw [← hQh, conjTranspose_conjTranspose]
    rw [hB, conjTranspose_add, conjTranspose_sub, conjTranspose_smul, conjTranspose_add, hPh, hRh, hQh, hQth]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_def, conj_I]
    ring
  -- positivity of the conjugates
  have hN1 : (fromBlocks E B Bᴴ (D - (4 : ℂ) • 1)).PosSemidef := by
    rw [← hBH, ← h1]; exact hG.mul_mul_conjTranspose_same _
  have hN2 : (fromBlocks (E - (4 : ℂ) • 1) B Bᴴ D).PosSemidef := by
    rw [← hBH, ← h2]; exact hG.transpose.mul_mul_conjTranspose_same _
  have hY : (E - (4 : ℂ) • 1).PosSemidef := by
    have := hN2.submatrix (Sum.inl : m → m ⊕ m)
    have he : (fromBlocks (E - (4 : ℂ) • 1) B Bᴴ D).submatrix Sum.inl Sum.inl = E - (4 : ℂ) • 1 := by
      ext i j; simp
    rwa [he] at this
  have h4 : ((4 : ℂ) • (1 : Matrix m m ℂ)).PosDef := by
    have : ((4 : ℝ) • (1 : Matrix m m ℂ)).PosDef := PosDef.one.smul (by norm_num)
    convert this using 1
  have hEpd : E.PosDef := by
    have := h4.add_posSemidef hY
    simpa using this
  have hEinv : Invertible E := hEpd.isUnit.invertible
  have hZ : (D - (4 : ℂ) • 1 - Bᴴ * E⁻¹ * B).PosSemidef := (PosDef.fromBlocks₁₁ B _ hEpd).1 hN1
  -- the determinant
  obtain ⟨r1, hr1, hr1le, -⟩ := det_four_add_of_posSemidef _ hY
  obtain ⟨r2, hr2, -, hr2le⟩ := det_four_add_of_posSemidef _ hZ
  have hEeq : (4 : ℂ) • (1 : Matrix m m ℂ) + (E - (4 : ℂ) • 1) = E := by abel
  have hDeq : (4 : ℂ) • (1 : Matrix m m ℂ) + (D - (4 : ℂ) • 1 - Bᴴ * E⁻¹ * B) = D - Bᴴ * E⁻¹ * B := by
    abel
  rw [hEeq] at hr1
  rw [hDeq] at hr2
  have hdet : ((4 : ℂ) ^ Fintype.card m) * ((1 + fromBlocks P Q Qᵀ R).det : ℂ) = (r1 : ℂ) * r2 := by
    have hmap : ((1 + fromBlocks P Q Qᵀ R).det : ℂ) = (1 + fromBlocks Pc Qc Qcᵀ Rc).det := by
      have : (1 + fromBlocks Pc Qc Qcᵀ Rc) = (1 + fromBlocks P Q Qᵀ R).map ofReal := by
        rw [Matrix.map_add _ (by simp), fromBlocks_map, hQt]
        congr 1
        ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
      rw [this]
      exact (RingHom.map_det Complex.ofRealHom _)
    rw [hmap, ← det_cayleyBlock_mul, mul_right_comm, ← det_mul, ← det_mul, h3, hBH, det_fromBlocks₁₁,
      invOf_eq_nonsing_inv, hr1, hr2]
  have hreal : (4 : ℝ) ^ Fintype.card m * (1 + fromBlocks P Q Qᵀ R).det = r1 * r2 := by
    exact_mod_cast hdet
  -- the trace
  have htr : (E - (4 : ℂ) • 1).trace.re = P.trace + R.trace - 2 * Fintype.card m := by
    have hre : ∀ M : Matrix m m ℝ, (M.map ofReal : Matrix m m ℂ).trace = ((M.trace : ℝ) : ℂ) := fun M => by
      simp [Matrix.trace]
    rw [hE, trace_sub, trace_add, trace_add, trace_add, trace_smul, trace_sub, trace_transpose, sub_self,
      smul_zero, trace_smul, trace_smul, trace_one, hPc, hRc, hre, hre]
    simp only [smul_eq_mul, add_zero]
    have : ((P.trace : ℂ) + R.trace + 2 * (Fintype.card m : ℂ) - 4 * (Fintype.card m : ℂ)) =
        ((P.trace + R.trace - 2 * Fintype.card m : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [htr] at hr1le
  have h4pos : (0 : ℝ) < 4 ^ Fintype.card m := by positivity
  -- combine
  by_cases hneg : 1 + (P.trace + R.trace - 2 * Fintype.card m) / 4 ≤ 0
  · have hr1pos : 0 ≤ r1 := by
      have hdE := hEpd.det_pos
      rw [hr1] at hdE
      exact le_of_lt (by exact_mod_cast hdE)
    have : 0 ≤ (4 : ℝ) ^ Fintype.card m * (1 + fromBlocks P Q Qᵀ R).det := by
      rw [hreal]; exact mul_nonneg hr1pos (le_trans h4pos.le hr2le)
    have hdetnn : 0 ≤ (1 + fromBlocks P Q Qᵀ R).det := nonneg_of_mul_nonneg_right this h4pos
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos h4pos.le hneg) hdetnn
  · push_neg at hneg
    have hprod : (4 : ℝ) ^ Fintype.card m * (1 + (P.trace + R.trace - 2 * Fintype.card m) / 4) *
        (4 : ℝ) ^ Fintype.card m ≤ r1 * r2 :=
      mul_le_mul hr1le hr2le h4pos.le (le_trans (mul_nonneg h4pos.le hneg.le) hr1le)
    rw [← hreal] at hprod
    have := le_of_mul_le_mul_left (by linarith : (4 : ℝ) ^ Fintype.card m *
      ((4 : ℝ) ^ Fintype.card m * (1 + (P.trace + R.trace - 2 * Fintype.card m) / 4)) ≤
      (4 : ℝ) ^ Fintype.card m * (1 + fromBlocks P Q Qᵀ R).det) h4pos
    exact this

end Lightlike.OperatorAlgebras
