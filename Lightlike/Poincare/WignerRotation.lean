module

public import Lightlike.Lorentz.SL2C

/-!
# The Wigner rotation of a massive momentum

Momenta are Hermitian `2 × 2` matrices `P = p⁰ + p·σ`, with `det P = p²` (signature `(+,−,−,−)`), on which
`SL(2,ℂ)` acts by `A • P = A P Aᴴ` (the universal cover of the restricted Lorentz group acting on momentum space).
For `m > 0` the forward mass shell `MassShellH m = {P | P > 0, det P = m²}` is invariant (`act_mem`).

* **Standard lift.** For `P` on the mass shell, `L(P) = (Q + 1)/√(tr Q + 2)` with `Q = P/m` is a Hermitian element
  of `SL(2,ℂ)` with `L(P)² = Q`, so `L(P) • (m·1) = P` (`stdLift_act_rest`): it is the standard boost of the Wigner
  construction, lifted to `SL(2,ℂ)`.
* **Wigner rotation.** `W(A, P) = L(A • P)⁻¹ A L(P)` lies in `SU(2)`, the little group of the rest momentum `m·1`
  (`wigner_mem_specialUnitaryGroup`), and satisfies the cocycle identity
  `W(A'A, P) = W(A', A • P) W(A, P)` (`wigner_mul`).

This is the algebraic core of the induced massive representations: for a unitary representation `D` of `SU(2)`,
`(U(A) ψ)(P) = D(W(A, A⁻¹ • P)) ψ(A⁻¹ • P)` is a representation because of the cocycle identity.

**Difference from the source (kind: representation).** Bekaert–Boulanger write the standard boost, the little
group and the Wigner rotation for `Λ ∈ SO(D−1,1)↑` acting on `ℝ^{D−1,1}` (§3.1, equations (10)–(13); §3.2); here
they are stated for the universal cover `SL(2,ℂ) ≅ Spin(3,1)` acting on Hermitian `2 × 2` momenta, which is how
§1.1 (page 3) says the representations are meant ("a single (or double) valued representation of `SO(D−1,1)↑` is
meant to be a genuine representation of `Spin(D−1,1)`"). The `SO(3,1)↑` form is not derived from this file.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1, equations (10)–(13) (standard Lorentz transformation `L(p)` and
  `W(Λ, p) = L⁻¹(Λp) Λ L(p)` in the little group), page 10 of v2.
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz
open scoped ComplexOrder

namespace Lightlike.Poincare

/-- The forward mass shell of mass `m`, as positive definite Hermitian matrices of determinant `m²`. -/
def MassShellH (m : ℝ) : Set (Matrix (Fin 2) (Fin 2) ℂ) := {P | P.PosDef ∧ P.det = ((m ^ 2 : ℝ) : ℂ)}

/-- The action `A • P = A P Aᴴ` of `SL(2,ℂ)` on Hermitian matrices. -/
def actP (A : SL2C) (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (A : Matrix (Fin 2) (Fin 2) ℂ) * P * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ

lemma actP_mul (A B : SL2C) (P : Matrix (Fin 2) (Fin 2) ℂ) : actP (A * B) P = actP A (actP B P) := by
  simp only [actP, Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma actP_one (P : Matrix (Fin 2) (Fin 2) ℂ) : actP 1 P = P := by
  simp [actP]

lemma det_actP (A : SL2C) (P : Matrix (Fin 2) (Fin 2) ℂ) : (actP A P).det = P.det := by
  simp [actP, Matrix.det_mul, Matrix.det_conjTranspose, A.2]

/-- The mass shell is invariant under `SL(2,ℂ)`. -/
lemma act_mem {m : ℝ} (A : SL2C) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    actP A P ∈ MassShellH m := by
  refine ⟨hP.1.mul_mul_conjTranspose_same ?_, by rw [det_actP]; exact hP.2⟩
  have hu : IsUnit (A : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [Matrix.isUnit_iff_isUnit_det, A.2]; exact isUnit_one
  exact Matrix.vecMul_injective_iff_isUnit.2 hu

/-! ## Two-by-two identities -/

lemma det_add_one_fin_two (Q : Matrix (Fin 2) (Fin 2) ℂ) : (Q + 1).det = Q.det + Q.trace + 1 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring

lemma mul_self_fin_two (Q : Matrix (Fin 2) (Fin 2) ℂ) : Q * Q = Q.trace • Q - Q.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring


/-! ## The mass shell as a type with an `SL(2,ℂ)` action -/

/-- The forward mass shell as a type. -/
abbrev MassShell (m : ℝ) := {P : Matrix (Fin 2) (Fin 2) ℂ // P ∈ MassShellH m}

/-- The action of `SL(2,ℂ)` on the mass shell. -/
def shellAct {m : ℝ} (A : SL2C) (P : MassShell m) : MassShell m := ⟨actP A P.1, act_mem A P.2⟩

lemma shellAct_mul {m : ℝ} (A B : SL2C) (P : MassShell m) :
    shellAct (A * B) P = shellAct A (shellAct B P) := Subtype.ext (actP_mul A B P.1)

lemma shellAct_one {m : ℝ} (P : MassShell m) : shellAct 1 P = P := Subtype.ext (actP_one P.1)

/-! ## The standard lift -/

/-- `Q = P / m`. -/
def normP (m : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ((1 / m : ℝ) : ℂ) • P

lemma normP_posDef {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    (normP m P).PosDef := by
  have hc : (0 : ℂ) < ((1 / m : ℝ) : ℂ) := by exact_mod_cast one_div_pos.2 hm
  exact hP.1.smul hc

lemma det_normP {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    (normP m P).det = 1 := by
  rw [normP, Matrix.det_smul, hP.2]
  simp only [Fintype.card_fin]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have : (1 / m) ^ 2 * m ^ 2 = 1 := by field_simp
  rw [this]; simp

/-- The trace of `Q = P/m`, a positive real number. -/
def trN (m : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((normP m P).trace).re

lemma trace_normP {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    (normP m P).trace = (trN m P : ℂ) ∧ 0 < trN m P := by
  have h := (normP_posDef hm hP).trace_pos
  rw [Complex.lt_def] at h
  refine ⟨Complex.ext (by simp [trN]) (by simp only [Complex.ofReal_im]; simpa using h.2.symm),
    by simpa [trN] using h.1⟩

/-- The standard lift `L(P) = (Q + 1)/√(tr Q + 2)` as a matrix. -/
def stdLiftMat (m : ℝ) (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt (trN m P + 2) : ℝ) : ℂ) • (normP m P + 1)

lemma sqrt_inv_sq {t : ℝ} (ht : 0 < t) : (1 / Real.sqrt t) * (1 / Real.sqrt t) = 1 / t := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt ht.le]

lemma det_stdLiftMat {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    (stdLiftMat m P).det = 1 := by
  obtain ⟨htr, htpos⟩ := trace_normP hm hP
  have hpos : 0 < trN m P + 2 := by linarith
  rw [stdLiftMat, Matrix.det_smul, det_add_one_fin_two, det_normP hm hP, htr]
  simp only [Fintype.card_fin]
  rw [← Complex.ofReal_pow, pow_two, sqrt_inv_sq hpos]
  push_cast
  field_simp
  ring

lemma stdLiftMat_mul_self {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    stdLiftMat m P * stdLiftMat m P = normP m P := by
  obtain ⟨htr, htpos⟩ := trace_normP hm hP
  have hpos : 0 < trN m P + 2 := by linarith
  have hsq : (normP m P + 1) * (normP m P + 1) = ((trN m P + 2 : ℝ) : ℂ) • normP m P := by
    rw [add_mul, mul_add, mul_add, mul_self_fin_two, det_normP hm hP, htr]
    simp only [one_smul, Matrix.mul_one, Matrix.one_mul]
    push_cast
    rw [add_smul, two_smul]
    abel
  rw [stdLiftMat, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, sqrt_inv_sq hpos, one_div_mul_cancel hpos.ne', Complex.ofReal_one, one_smul]

lemma stdLiftMat_conjTranspose {m : ℝ} (hm : 0 < m) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P ∈ MassShellH m) :
    (stdLiftMat m P)ᴴ = stdLiftMat m P := by
  have hQ : (normP m P)ᴴ = normP m P := (normP_posDef hm hP).isHermitian
  rw [stdLiftMat, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hQ, Matrix.conjTranspose_one]
  simp

/-- **The standard lift** of a momentum on the mass shell to `SL(2,ℂ)`. -/
def stdLift {m : ℝ} (hm : 0 < m) (P : MassShell m) : SL2C := ⟨stdLiftMat m P.1, det_stdLiftMat hm P.2⟩

/-- The standard lift takes the rest momentum `m · 1` to `P`. -/
theorem stdLift_act_rest {m : ℝ} (hm : 0 < m) (P : MassShell m) :
    actP (stdLift hm P) ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = P.1 := by
  show stdLiftMat m P.1 * ((m : ℂ) • 1) * (stdLiftMat m P.1)ᴴ = P.1
  rw [stdLiftMat_conjTranspose hm P.2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    stdLiftMat_mul_self hm P.2, normP, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel hm.ne',
    Complex.ofReal_one, one_smul]

/-! ## The Wigner rotation -/

/-- The Wigner rotation `W(A, P) = L(A • P)⁻¹ A L(P)`. -/
def wigner {m : ℝ} (hm : 0 < m) (A : SL2C) (P : MassShell m) : SL2C :=
  (stdLift hm (shellAct A P))⁻¹ * A * stdLift hm P

/-- The Wigner rotation fixes the rest momentum. -/
lemma wigner_act_rest {m : ℝ} (hm : 0 < m) (A : SL2C) (P : MassShell m) :
    actP (wigner hm A P) ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (m : ℂ) • 1 := by
  have h1 := stdLift_act_rest hm (shellAct A P)
  have h2 : actP ((stdLift hm (shellAct A P))⁻¹) (shellAct A P).1 = (m : ℂ) • 1 := by
    rw [← h1, ← actP_mul, inv_mul_cancel, actP_one]
  rw [wigner, actP_mul, actP_mul, stdLift_act_rest hm P]
  exact h2

/-- **The Wigner rotation lies in `SU(2)`**, the little group of the rest momentum. -/
theorem wigner_mem_specialUnitaryGroup {m : ℝ} (hm : 0 < m) (A : SL2C) (P : MassShell m) :
    ((wigner hm A P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, (wigner hm A P).2⟩
  have h := wigner_act_rest hm A P
  simp only [actP, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) hm' h
  simpa [Matrix.star_eq_conjTranspose] using this

/-- **Cocycle identity** `W(A'A, P) = W(A', A • P) W(A, P)`. -/
theorem wigner_mul {m : ℝ} (hm : 0 < m) (A' A : SL2C) (P : MassShell m) :
    wigner hm (A' * A) P = wigner hm A' (shellAct A P) * wigner hm A P := by
  simp only [wigner, shellAct_mul]
  group

end Lightlike.Poincare
