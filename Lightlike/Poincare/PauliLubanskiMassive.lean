import Lightlike.Poincare.PauliLubanskiRest

/-!
# The Pauli–Lubanski square at every momentum of a massive representation

Let `P` be a momentum on the mass shell and `L(P)` its standard lift. The little group of `P` is
`L(P) SU(2) L(P)⁻¹`, and its elements act on the states of momentum `P` by the spin representation:
`(U(L(P) u L(P)⁻¹) ψ)(P) = D(u) ψ(P)` (`inducedAct_conj`), because the Wigner rotation of `L(P) u L(P)⁻¹` at `P` is
`u` (`wigner_conj`). This is the transport of `inducedAct_rest` from the rest momentum to `P` by the group law of `U`;
no differentiability of the wave function or of the section is used, since these curves fix `P`.

Differentiating along `θ ↦ L(P) R_a(θ) L(P)⁻¹` gives the generators of the little group of `P` as derivatives of the
induced representation at `P` (`hasDerivAt_inducedAct_littleGen`): `dSpin n (X_a) ψ(P)`. With the Pauli–Lubanski
vector at `P` given by `m` times these generators in the frame `L(P)` (`W(P) = Λ(L(P)) (0, m J)`), its square is
`W²(P) = −m² s(s+1)` at every momentum `P` (`pauliLubanski_sq`).

**Difference from the source (kind: weaker).** The Pauli–Lubanski vector at `P` is taken in its little-group form
`W(P) = Λ(L(P)) (0, m J)` (Bekaert–Boulanger §5.2: the quartic Casimir is evaluated in the rest frame), with the
generators `J` derived from `U` at `P`; the identity `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` for the full generators (including
the boosts and the orbital parts, which cancel) is not formalised.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1, equations (11)–(13) (page 10 of v2), §5.2, equation (54) (page 39 of v2).
-/

noncomputable section

open Matrix Lightlike.Lorentz Lightlike.SU2

namespace Lightlike.Poincare

/-- The standard lift takes the rest momentum to `P`, on the mass shell. -/
lemma shellAct_stdLift {m : ℝ} (hm : 0 < m) (P : MassShell m) :
    shellAct (stdLift hm P) (restShell hm) = P := Subtype.ext (stdLift_act_rest hm P)

/-- The little group of `P`: `L(P) u L(P)⁻¹` fixes `P`. -/
lemma shellAct_conj {m : ℝ} (hm : 0 < m) (P : MassShell m) (u : SU2) :
    shellAct (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹) P = P := by
  rw [shellAct_mul, shellAct_mul]
  have h1 : shellAct (stdLift hm P)⁻¹ P = restShell hm := by
    have := congrArg (shellAct (stdLift hm P)⁻¹) (shellAct_stdLift hm P)
    rw [← shellAct_mul, inv_mul_cancel, shellAct_one] at this
    exact this.symm
  rw [h1, shellAct_rest hm u, shellAct_stdLift hm P]

/-- The Wigner rotation of `L(P) u L(P)⁻¹` at `P` is `u`. -/
lemma wigner_conj {m : ℝ} (hm : 0 < m) (P : MassShell m) (u : SU2) :
    wigner hm (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹) P = SL2C.ofSU2 u := by
  rw [wigner, shellAct_conj hm P u]
  group

lemma wignerSU2_conj {m : ℝ} (hm : 0 < m) (P : MassShell m) (u : SU2) :
    wignerSU2 hm (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹) P = u := by
  apply Subtype.ext
  simp [wignerSU2, wigner_conj hm P u]

/-- **The little group of `P` acts on the states of momentum `P` by the spin representation.** -/
theorem inducedAct_conj {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : SU2 →* Matrix.unitaryGroup ι ℂ) (P : MassShell m) (u : SU2) (ψ : MassShell m → ι → ℂ) :
    inducedAct hm D (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹) ψ P =
      ((D u : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ ψ P := by
  have h1 : shellAct (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹)⁻¹ P = P := by
    have := congrArg (shellAct (stdLift hm P * SL2C.ofSU2 u * (stdLift hm P)⁻¹)⁻¹) (shellAct_conj hm P u)
    rw [← shellAct_mul, inv_mul_cancel, shellAct_one] at this
    exact this.symm
  simp only [inducedAct, h1, wignerSU2_conj hm P u]

/-- **The little-group generators at `P` are derivatives of the induced representation at `P`**:
`d/dθ (U(L(P) R_a(θ) L(P)⁻¹) ψ)(P) = dSpin n (X_a) ψ(P)` at `θ = 0`. -/
theorem hasDerivAt_inducedAct_littleGen {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (a : Fin 3)
    (ψ : MassShell m → Fin (n + 1) → ℂ) (k : Fin (n + 1)) :
    HasDerivAt (fun θ => inducedAct hm (spinRep n)
        (stdLift hm P * SL2C.ofSU2 (rotCurve a θ) * (stdLift hm P)⁻¹) ψ P k)
      ((dSpin n (rotVel a) *ᵥ ψ P) k) 0 := by
  have h : (fun θ => inducedAct hm (spinRep n)
        (stdLift hm P * SL2C.ofSU2 (rotCurve a θ) * (stdLift hm P)⁻¹) ψ P k) =
      fun θ => ∑ l, spinMat n (rotCurve a θ : Matrix (Fin 2) (Fin 2) ℂ) k l * ψ P l := by
    funext θ
    rw [inducedAct_conj]
    rfl
  rw [h]
  simp only [Matrix.mulVec, dotProduct]
  refine HasDerivAt.fun_sum fun l _ => ?_
  exact (hasDerivAt_spinMat (rotCurve_zero a) (hasDerivAt_rotCurve a) k l).mul_const _

/-- **`W² = −m² s(s+1)` at every momentum `P`**: the Pauli–Lubanski square built from the little-group generators at
`P` (in the frame `L(P)`, `W(P) = Λ(L(P)) (0, m J)`, with `J_a = (i/2) dSpin n (X_a)` the Hermitian generators
of `hasDerivAt_inducedAct_littleGen`) acts on the states of momentum `P` as the scalar `−m² s(s+1)`. -/
theorem pauliLubanski_sq {m : ℝ} (hm : 0 < m) (n : ℕ) (P : MassShell m) (ψ : MassShell m → Fin (n + 1) → ℂ) :
    (-∑ a, restPL m n a * restPL m n a) *ᵥ ψ P =
      (-(m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • ψ P := by
  rw [pauliLubanski_sq_rest]
  funext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

end Lightlike.Poincare
