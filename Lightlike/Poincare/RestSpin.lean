module

public import Lightlike.Poincare.InducedUnitary

/-!
# The states at rest carry the spin representation

At the rest momentum `q = m · 1` the standard lift is the identity (`stdLift_restShell`), the rotations `u ∈ SU(2)`
fix `q` (`shellAct_rest`), and their Wigner rotation at `q` is `u` itself (`wigner_rest`). Hence the induced massive
representation acts on the states of momentum `q` by the spin representation `D` of the little group:
`(U(u) ψ)(q) = D(u) ψ(q)` (`inducedAct_rest`). For `D = Lightlike.SU2.spinRep n` these states form the spin-`n/2`
representation, whose Casimir is `(n/2)(n/2 + 1)` (`Lightlike.Spin4.casimir_eq`): the little-group content of
`W² = −m² s(s+1)`, whose operator form for the induced representation is `pauliLubanski_sq_generators`
(`Lightlike/Poincare/PauliLubanskiGenerators.lean`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1, equation (12) (page 10 of v2: the little group acts on the states of the standard
  momentum through the representation `D`), §5.2 (page 39 of v2: the quartic Casimir of a massive representation is
  evaluated in the rest frame).
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

lemma normP_rest {m : ℝ} (hm : 0 < m) : normP m ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  rw [normP, smul_smul, ← Complex.ofReal_mul, one_div_mul_cancel hm.ne', Complex.ofReal_one, one_smul]

lemma stdLiftMat_rest {m : ℝ} (hm : 0 < m) :
    stdLiftMat m ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  have htr : trN m ((m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 2 := by
    rw [trN, normP_rest hm]; simp
  rw [stdLiftMat, htr, normP_rest hm]
  have h4 : Real.sqrt (2 + 2) = 2 := by
    rw [show (2 : ℝ) + 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, ← two_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ), smul_smul]
  norm_num

/-- The standard lift of the rest momentum is the identity. -/
lemma stdLift_restShell {m : ℝ} (hm : 0 < m) : stdLift hm (restShell hm) = 1 :=
  Subtype.ext (stdLiftMat_rest hm)

/-- The rotations fix the rest momentum. -/
lemma shellAct_rest {m : ℝ} (hm : 0 < m) (u : Lightlike.SU2) :
    shellAct (SL2C.ofSU2 u) (restShell hm) = restShell hm := by
  apply Subtype.ext
  show (u : Matrix (Fin 2) (Fin 2) ℂ) * ((m : ℂ) • 1) * (u : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (m : ℂ) • 1
  have hu : (u : Matrix (Fin 2) (Fin 2) ℂ) * star (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 (Matrix.mem_specialUnitaryGroup_iff.1 u.2).1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.star_eq_conjTranspose, hu]

/-- The Wigner rotation of a rotation at the rest momentum is the rotation itself. -/
lemma wigner_rest {m : ℝ} (hm : 0 < m) (u : Lightlike.SU2) :
    wigner hm (SL2C.ofSU2 u) (restShell hm) = SL2C.ofSU2 u := by
  rw [wigner, shellAct_rest hm u, stdLift_restShell hm, inv_one, one_mul, mul_one]

lemma wignerSU2_rest {m : ℝ} (hm : 0 < m) (u : Lightlike.SU2) :
    wignerSU2 hm (SL2C.ofSU2 u) (restShell hm) = u := by
  apply Subtype.ext
  simp [wignerSU2, wigner_rest hm u]

/-- **The states at rest carry the spin representation**: `(U(u) ψ)(q) = D(u) ψ(q)` for `u ∈ SU(2)`. -/
theorem inducedAct_rest {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (u : Lightlike.SU2) (ψ : MassShell m → ι → ℂ) :
    inducedAct hm D (SL2C.ofSU2 u) ψ (restShell hm) =
      ((D u : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *ᵥ ψ (restShell hm) := by
  have h1 : shellAct (SL2C.ofSU2 u)⁻¹ (restShell hm) = restShell hm := by
    rw [← map_inv, shellAct_rest hm u⁻¹]
  simp only [inducedAct, h1, wignerSU2_rest hm u]

end Lightlike.Poincare
