module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Momentum

/-!
# The standard boost `L(p)` on the massive mass shell

HA6 (Wigner's classification), second piece. For `m > 0` the positive-energy mass shell is the set of
Hermitian matrices `P` with `det P = m²` and `tr P > 0` (that is `p₀ > 0`, `p² = m²`). For such `P`
the *standard boost* is the positive Hermitian matrix
`L(P) = (P + m·1) / √(m (tr P + 2m))` of `SL(2,ℂ)`; it carries the rest momentum to `P`:
`L(P) (m·1) L(P)† = P` (`boost_smul_rest`). This is the first ingredient of the Wigner rotation
`W(A, P) = L(A P)⁻¹ A L(P) ∈ SU(2)` used to induce representations from the little group.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- The positive-energy mass shell of mass `m`: `det P = m²` and `tr P > 0`. -/
def massShell (m : ℝ) : Set Herm2 :=
  {P | P.1.det = ((m ^ 2 : ℝ) : ℂ) ∧ 0 < P.1.trace.re}

/-- The trace of a Hermitian matrix is real. -/
lemma trace_eq_re (P : Herm2) : P.1.trace = ((P.1.trace.re : ℝ) : ℂ) := by
  have h : star P.1.trace = P.1.trace := by
    rw [← Matrix.trace_conjTranspose, P.2.eq]
  exact ((Complex.conj_eq_iff_re).mp h).symm

/-- Cayley–Hamilton for `2 × 2` matrices: `Q² = tr Q · Q - det Q · 1`. -/
lemma sq_eq_trace_det (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    Q * Q = Q.trace • Q - Q.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- The determinant of `Q + m·1`: `det Q + m tr Q + m²`. -/
lemma det_add_smul_one (Q : Matrix (Fin 2) (Fin 2) ℂ) (m : ℂ) :
    (Q + m • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = Q.det + m * Q.trace + m ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

/-- The normalisation `1 / √(m (tr P + 2m))` of the standard boost. -/
noncomputable def boostScale (m : ℝ) (P : Herm2) : ℝ :=
  (Real.sqrt (m * (P.1.trace.re + 2 * m)))⁻¹

lemma boostScale_sq {m : ℝ} (hm : 0 < m) {P : Herm2} (hP : 0 < P.1.trace.re) :
    boostScale m P ^ 2 * (m * (P.1.trace.re + 2 * m)) = 1 := by
  have hpos : 0 < m * (P.1.trace.re + 2 * m) := by positivity
  unfold boostScale
  rw [inv_pow, Real.sq_sqrt hpos.le]
  exact inv_mul_cancel₀ hpos.ne'

/-- The matrix of the standard boost, `(P + m·1) / √(m (tr P + 2m))`. -/
noncomputable def boostMat (m : ℝ) (P : Herm2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (boostScale m P : ℂ) • (P.1 + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

lemma det_boostMat {m : ℝ} (hm : 0 < m) {P : Herm2} (hP : P ∈ massShell m) :
    (boostMat m P).det = 1 := by
  obtain ⟨hd, ht⟩ := hP
  have h1 := boostScale_sq hm ht
  have h2 : ((boostScale m P ^ 2 * (m * (P.1.trace.re + 2 * m)) : ℝ) : ℂ) = 1 := by
    rw [h1]; simp
  unfold boostMat
  rw [Matrix.det_smul, det_add_smul_one, hd, trace_eq_re P]
  simp only [Fintype.card_fin]
  push_cast at h2 ⊢
  linear_combination h2

/-- **The standard boost** `L(P) ∈ SL(2,ℂ)` of a point of the massive mass shell. -/
noncomputable def boost {m : ℝ} (hm : 0 < m) (P : massShell m) : SL2C :=
  ⟨boostMat m P.1, det_boostMat hm P.2⟩

lemma coe_boost {m : ℝ} (hm : 0 < m) (P : massShell m) :
    ((boost hm P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = boostMat m P.1 := rfl

/-- The standard boost is a Hermitian matrix. -/
lemma boostMat_conjTranspose (m : ℝ) (P : Herm2) : (boostMat m P)ᴴ = boostMat m P := by
  unfold boostMat
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, P.2.eq, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one]
  simp

/-- **The standard boost carries the rest momentum to `P`**: `L(P) (m·1) L(P)† = P`. -/
theorem boost_smul_rest {m : ℝ} (hm : 0 < m) (P : massShell m) :
    boost hm P • restMom m = P.1 := by
  apply Subtype.ext
  obtain ⟨hd, ht⟩ := P.2
  have h1 := boostScale_sq hm ht
  rw [coe_smul, coe_boost, boostMat_conjTranspose]
  set Q : Matrix (Fin 2) (Fin 2) ℂ := P.1.1 with hQ
  have hsq := sq_eq_trace_det Q
  have hBB : (Q + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (Q + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (((P.1.1.trace.re : ℝ) : ℂ) + 2 * m) • Q := by
    have hT : Q.trace = ((P.1.1.trace.re : ℝ) : ℂ) := trace_eq_re P.1
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul,
      smul_smul, hsq, hT, hd]
    push_cast
    module
  have h2 : ((boostScale m P.1 ^ 2 * (m * (P.1.1.trace.re + 2 * m)) : ℝ) : ℂ) = 1 := by
    rw [h1]; simp
  unfold boostMat
  simp only [restMom, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [show (P.1.1 + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (P.1.1 + (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = _ from hBB, smul_smul]
  push_cast at h2
  have h3 : (boostScale m P.1 : ℂ) * ((m : ℂ) * (boostScale m P.1 : ℂ)) *
      (((P.1.1.trace.re : ℝ) : ℂ) + 2 * m) = 1 := by
    linear_combination h2
  rw [h3, one_smul]

/-! ## The mass shell is a `SL(2,ℂ)`-space and the Wigner rotation -/

/-- `tr (M M†) > 0` for `M ∈ SL(2,ℂ)`: the sum of the squared moduli of the entries. -/
lemma trace_mul_conjTranspose_pos (M : SL2C) :
    0 < ((M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace.re := by
  have hdet := SL2C.det_eq M
  have key : ((M : Matrix (Fin 2) (Fin 2) ℂ) * (M : Matrix (Fin 2) (Fin 2) ℂ)ᴴ).trace.re =
      Complex.normSq (M 0 0) + Complex.normSq (M 0 1) + Complex.normSq (M 1 0) +
        Complex.normSq (M 1 1) := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_conj, Complex.normSq_apply]
    ring
  rw [key]
  by_contra hneg
  have h0 := Complex.normSq_nonneg (M 0 0)
  have h1 := Complex.normSq_nonneg (M 0 1)
  have h2 := Complex.normSq_nonneg (M 1 0)
  have h3 := Complex.normSq_nonneg (M 1 1)
  have e0 : Complex.normSq (M 0 0) = 0 := by linarith
  have e1 : Complex.normSq (M 0 1) = 0 := by linarith
  rw [Complex.normSq_eq_zero] at e0 e1
  rw [e0, e1] at hdet
  simp at hdet

/-- The mass shell is stable under `SL(2,ℂ)`: `det` is invariant and `tr (A P A†) > 0` because
`P = L (m·1) L†` for the standard boost. -/
lemma smul_mem_massShell {m : ℝ} (hm : 0 < m) (A : SL2C) (P : massShell m) :
    A • P.1 ∈ massShell m := by
  refine ⟨by rw [det_smul]; exact P.2.1, ?_⟩
  have h : A • P.1 = (A * boost hm P) • restMom m := by
    rw [mul_smul, boost_smul_rest]
  rw [h, coe_smul]
  simp only [restMom, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul]
  have := trace_mul_conjTranspose_pos (A * boost hm P)
  simpa [Complex.smul_re, mul_comm] using mul_pos hm this

/-- The action of `SL(2,ℂ)` on the mass shell. -/
def shellSMul {m : ℝ} (hm : 0 < m) (A : SL2C) (P : massShell m) : massShell m :=
  ⟨A • P.1, smul_mem_massShell hm A P⟩

/-- **The Wigner rotation** as an element of `SL(2,ℂ)`: `L(A P)⁻¹ A L(P)`. -/
noncomputable def wignerSL {m : ℝ} (hm : 0 < m) (A : SL2C) (P : massShell m) : SL2C :=
  (boost hm (shellSMul hm A P))⁻¹ * A * boost hm P

/-- The Wigner rotation fixes the rest momentum, i.e. lies in the massive little group. -/
theorem wignerSL_mem_stabilizer {m : ℝ} (hm : 0 < m) (A : SL2C) (P : massShell m) :
    wignerSL hm A P ∈ MulAction.stabilizer SL2C (restMom m) := by
  rw [MulAction.mem_stabilizer_iff]
  unfold wignerSL
  rw [mul_assoc, mul_smul, mul_smul, boost_smul_rest, inv_smul_eq_iff]
  exact (boost_smul_rest hm (shellSMul hm A P)).symm

/-- **The Wigner rotation of `A` at momentum `P` is an element of `SU(2)`.** -/
theorem exists_wigner_su2 {m : ℝ} (hm : 0 < m) (A : SL2C) (P : massShell m) :
    ∃ u : Lightlike.SU2, SL2C.ofSU2 u = wignerSL hm A P := by
  have := wignerSL_mem_stabilizer hm A P
  rw [stabilizer_restMom hm.ne', MonoidHom.mem_range] at this
  exact this

end Lightlike.Lorentz.Poincare
