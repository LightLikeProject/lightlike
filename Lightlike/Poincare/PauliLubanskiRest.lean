import Lightlike.Poincare.RestSpin
import Lightlike.Spin4.Ladder

/-!
# The Pauli–Lubanski square in the rest frame, from the generators of the induced representation

For the induced massive representation of `SL(2,ℂ)` built on the spin representation `D = spinRep n`, the rotation
generators at the rest momentum `q = m · 1` are derivatives of the representation itself:
`d/dθ (U(R_a(θ)) ψ)(q) |_{θ = 0} = dSpin n (X_a) ψ(q)` along the rotation curves `R_a` of `SU(2)` with velocities
`X_a` (`hasDerivAt_inducedAct_rest`). With the Hermitian spin operators `J_a = (i/2) dSpin n (X_a)` (the curves turn by
the angle `2θ`) and the rest-frame Pauli–Lubanski vector `W = (0, m J)` (signature `(+,−,−,−)`), the square is
`W² = −m² Σ J_a² = −m² s(s+1)` with `s = n/2` (`pauliLubanski_sq_rest`).

**Difference from the source (kind: weaker).** Bekaert–Boulanger evaluate the quartic Casimir of a massive
representation in the rest frame (§5.2, equation (54), page 39 of v2) as an operator identity; here the rotation
generators are derived from the representation at the rest momentum only, the rest-frame form `W = (0, m J)` is used
as the definition of `W` there, and the boost terms (which cancel by antisymmetry at the rest momentum) and the
Pauli–Lubanski operator at other momenta are not formalised.

**Attempts recorded** (`docs/notes/ha6-pauli-lubanski-attempts.md`): (1) generators at the standard momentum, this
file; (2) a direct computation at a general momentum: in the massless case stopped by the discontinuity of the
standard lift near `P₀₀ = 0` (no continuous global section exists); in the massive case completed in
`Lightlike/Poincare/PauliLubanskiGenerators.lean`.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §5.2, equation (54) and the example after it (page 39 of v2: "the square of the
  Pauli–Lubanski vector acting on a massive field of spin-s is indeed equal to `m² s(s+1)`", signature `(−,+,+,+)`).
-/

noncomputable section

open Matrix Lightlike.Lorentz Lightlike.SU2

namespace Lightlike.Poincare

/-- The velocities of the three rotation curves of `SU(2)`. -/
def rotVel : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Complex.I • (matE + matF), matF - matE, Complex.I • matH]

/-- The three rotation curves of `SU(2)` (about the `x`, `y`, `z` axes). -/
def rotCurve : Fin 3 → ℝ → SU2 := ![curveX, curveY, curveZ]

lemma rotCurve_zero (a : Fin 3) : (rotCurve a 0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  fin_cases a
  · exact curveX_zero
  · exact curveY_zero
  · exact curveZ_zero

lemma hasDerivAt_rotCurve (a : Fin 3) (i j : Fin 2) :
    HasDerivAt (fun θ => (rotCurve a θ : Matrix (Fin 2) (Fin 2) ℂ) i j) (rotVel a i j) 0 := by
  fin_cases a
  · exact hasDerivAt_curveX i j
  · exact hasDerivAt_curveY i j
  · exact hasDerivAt_curveZ i j

/-- **The rotation generators at rest are derivatives of the induced representation**:
`d/dθ (U(R_a(θ)) ψ)(q) = dSpin n (X_a) ψ(q)` at `θ = 0`. -/
theorem hasDerivAt_inducedAct_rest {m : ℝ} (hm : 0 < m) (n : ℕ) (a : Fin 3)
    (ψ : MassShell m → Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    HasDerivAt (fun θ => inducedAct hm (spinRep n) (SL2C.ofSU2 (rotCurve a θ)) ψ (restShell hm) k)
      ((dSpin n (rotVel a) *ᵥ ψ (restShell hm)) k) 0 := by
  have h : (fun θ => inducedAct hm (spinRep n) (SL2C.ofSU2 (rotCurve a θ)) ψ (restShell hm) k) =
      fun θ => ∑ l, spinMat n (rotCurve a θ : Matrix (Fin 2) (Fin 2) ℂ) k l * ψ (restShell hm) l := by
    funext θ
    rw [inducedAct_rest]
    rfl
  rw [h]
  simp only [Matrix.mulVec, dotProduct]
  refine HasDerivAt.fun_sum fun l _ => ?_
  exact (hasDerivAt_spinMat (rotCurve_zero a) (hasDerivAt_rotCurve a) k l).mul_const _

/-- The Hermitian spin operators `J_a = (i/2) dSpin n (X_a)`. -/
def spinOp (n : ℕ) (a : Fin 3) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (Complex.I / 2) • dSpin n (rotVel a)

/-- **The spin Casimir** `J_x² + J_y² + J_z² = s(s+1)`, `s = n/2`. -/
theorem sum_spinOp_sq (n : ℕ) :
    ∑ a, spinOp n a * spinOp n a = ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [← Lightlike.Spin4.casimir_eq n]
  simp only [Fin.sum_univ_three, spinOp, rotVel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, dSpin_smul, dSpin_add, dSpin_sub,
    smul_mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
  have hI : Complex.I / 2 * (Complex.I / 2) * (Complex.I * Complex.I) = 1 / 4 := by
    rw [div_mul_div_comm, Complex.I_mul_I]; norm_num
  have hI2 : Complex.I / 2 * (Complex.I / 2) = -(1 / 4) := by
    rw [div_mul_div_comm, Complex.I_mul_I]; norm_num
  rw [hI, hI2]
  module

/-- The rest-frame Pauli–Lubanski vector `W = (0, m J)`: its spatial components on the states at rest. -/
def restPL (m : ℝ) (n : ℕ) (a : Fin 3) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (m : ℂ) • spinOp n a

/-- **`W² = −m² s(s+1)` in the rest frame** (signature `(+,−,−,−)`, `W⁰ = 0`). -/
theorem pauliLubanski_sq_rest (m : ℝ) (n : ℕ) :
    -∑ a, restPL m n a * restPL m n a =
      (-(m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  simp only [restPL, smul_mul_smul_comm, ← Finset.smul_sum, sum_spinOp_sq, smul_smul]
  rw [← neg_smul]
  congr 1
  ring

end Lightlike.Poincare
