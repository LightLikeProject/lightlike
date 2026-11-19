module

public import Lightlike.Poincare.WignerRotation

/-!
# The Pauli–Lubanski combination lies in the little algebra

In `SL(2,ℂ)` notation a Lorentz generator `X ∈ sl(2,ℂ)` moves a Hermitian momentum `P` by `X P + P Xᴴ`. With the
rotation generators `(i/2) σ_k` and the boost generators `(1/2) σ_k`, the Pauli–Lubanski combination
`W^μ = ½ ε^{μνρσ} M_{νρ} p_σ` of the generators is, for the momentum `P = p⁰ + p·σ`,

* `X⁰_P = (i/2) (p·σ)` (that is `J · p`),
* `X^i_P = (i/2) p⁰ σ_i + ½ (p × σ)_i` (that is `p⁰ J_i + (p × K)_i`),

(`plGen`), and each of them fixes `P` infinitesimally: `X^μ_P P + P (X^μ_P)ᴴ = 0` (`plGen_fix`). So the
Pauli–Lubanski operators are generators of the little group of `P`: on the induced representation they act without
orbital part, through the little-group representation. At rest (`p = 0`, `p⁰ = m`) the combination is
`X^i = m (i/2) σ_i`, `m` times the rotation generators (`plGen_rest`).

Supporting lemmas for the Pauli–Lubanski operator; no catalogue entry.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §1.2 (page 4 of v2: the Poincaré algebra and the Pauli–Lubanski vector,
  `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ` in `D = 4`).
-/

@[expose] public section

noncomputable section

open Matrix Complex

namespace Lightlike.Poincare

/-- The Pauli matrices. -/
def pauliM : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -I; I, 0], !![1, 0; 0, -1]]

/-- The Hermitian momentum `p⁰ + p·σ`. -/
def momH (p0 : ℝ) (p : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p0 : ℂ) + p 2, (p 0 : ℂ) - I * p 1; (p 0 : ℂ) + I * p 1, (p0 : ℂ) - p 2]

/-- The Pauli–Lubanski combination of the generators for the momentum `p⁰ + p·σ`, as elements of `sl(2,ℂ)`. -/
def plGen (p0 : ℝ) (p : Fin 3 → ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(I / 2) • ((p 0 : ℂ) • pauliM 0 + (p 1 : ℂ) • pauliM 1 + (p 2 : ℂ) • pauliM 2),
    (I / 2 * p0) • pauliM 0 + (1 / 2 : ℂ) • ((p 1 : ℂ) • pauliM 2 - (p 2 : ℂ) • pauliM 1),
    (I / 2 * p0) • pauliM 1 + (1 / 2 : ℂ) • ((p 2 : ℂ) • pauliM 0 - (p 0 : ℂ) • pauliM 2),
    (I / 2 * p0) • pauliM 2 + (1 / 2 : ℂ) • ((p 0 : ℂ) • pauliM 1 - (p 1 : ℂ) • pauliM 0)]

/-- **The Pauli–Lubanski combination fixes the momentum**: `X^μ_P P + P (X^μ_P)ᴴ = 0`. -/
theorem plGen_fix (p0 : ℝ) (p : Fin 3 → ℝ) (μ : Fin 4) :
    plGen p0 p μ * momH p0 p + momH p0 p * (plGen p0 p μ)ᴴ = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.zero_apply]
  simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply]
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    simp [plGen, pauliM, momH] <;> apply Complex.ext <;> simp <;> ring

/-- At rest the Pauli–Lubanski combination is `m` times the rotation generators `(i/2) σ_i`. -/
theorem plGen_rest (m : ℝ) (i : Fin 3) :
    plGen m 0 i.succ = (I / 2 * m) • pauliM i := by
  fin_cases i <;> simp [plGen]

end Lightlike.Poincare
