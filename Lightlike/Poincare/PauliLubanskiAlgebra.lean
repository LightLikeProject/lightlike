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

/-! ## The Lorentz generators and the Levi-Civita combination -/

/-- The momentum `p^μ = (p⁰, p)` with its index lowered by `η = diag(1, −1, −1, −1)`: `p_μ`. -/
def pLow (p0 : ℝ) (p : Fin 3 → ℝ) : Fin 4 → ℝ := ![p0, -p 0, -p 1, -p 2]

/-- The Hermitian momentum of a four-vector `v = (v⁰, v¹, v², v³)`. -/
def momHv (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ := momH (v 0) ![v 1, v 2, v 3]

/-- The Lorentz generator `M_{νρ}` acting on a momentum: `(M_{νρ} p)^α = δ^α_ν p_ρ − δ^α_ρ p_ν`. -/
def lorAct (p0 : ℝ) (p : Fin 3 → ℝ) (ν ρ : Fin 4) : Fin 4 → ℝ := fun α =>
  (if α = ν then pLow p0 p ρ else 0) - (if α = ρ then pLow p0 p ν else 0)

/-- The Lorentz generators `M_{νρ}` as elements of `sl(2,ℂ)`: `M_{0k} = −½ σ_k`, `M_{k0} = ½ σ_k`,
`M_{ij} = −ε_{ijk} (i/2) σ_k`. They are fixed by `lorGen_act`. -/
def lorGen : Fin 4 → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, (-1 / 2 : ℂ) • pauliM 0, (-1 / 2 : ℂ) • pauliM 1, (-1 / 2 : ℂ) • pauliM 2],
    ![(1 / 2 : ℂ) • pauliM 0, 0, (-I / 2) • pauliM 2, (I / 2) • pauliM 1],
    ![(1 / 2 : ℂ) • pauliM 1, (I / 2) • pauliM 2, 0, (-I / 2) • pauliM 0],
    ![(1 / 2 : ℂ) • pauliM 2, (-I / 2) • pauliM 1, (I / 2) • pauliM 0, 0]]

/-- **The generators are the Lorentz generators**: the generator `lorGen ν ρ` moves the momentum `p` by
`M_{νρ} p`, `X P + P Xᴴ = (M_{νρ} p)^α σ_α`. -/
theorem lorGen_act (p0 : ℝ) (p : Fin 3 → ℝ) (ν ρ : Fin 4) :
    lorGen ν ρ * momH p0 p + momH p0 p * (lorGen ν ρ)ᴴ = momHv (lorAct p0 p ν ρ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, Matrix.conjTranspose_apply]
  fin_cases ν <;> fin_cases ρ <;> fin_cases i <;> fin_cases j <;>
    simp [lorGen, pauliM, momH, momHv, lorAct, pLow] <;> apply Complex.ext <;> simp <;> ring

/-- The Levi-Civita symbol with `ε^{0123} = 1`, as the normalised Vandermonde product. -/
def levi (a b c d : Fin 4) : ℝ :=
  (((b : ℕ) : ℝ) - a) * (((c : ℕ) : ℝ) - a) * (((d : ℕ) : ℝ) - a) * (((c : ℕ) : ℝ) - b) *
    (((d : ℕ) : ℝ) - b) * (((d : ℕ) : ℝ) - c) / 12

lemma levi_0123 : levi 0 1 2 3 = 1 := by norm_num [levi]

lemma levi_swap01 (a b c d : Fin 4) : levi b a c d = -levi a b c d := by unfold levi; ring
lemma levi_swap12 (a b c d : Fin 4) : levi a c b d = -levi a b c d := by unfold levi; ring
lemma levi_swap23 (a b c d : Fin 4) : levi a b d c = -levi a b c d := by unfold levi; ring

/-- The Pauli–Lubanski combination `½ ε^{μνρσ} M_{νρ} p_σ` of the Lorentz generators. -/
def plComb (p0 : ℝ) (p : Fin 3 → ℝ) (μ : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ ν ρ σ * pLow p0 p σ : ℝ) : ℂ) • lorGen ν ρ

/-- **The Levi-Civita combination is `plGen`.** -/
theorem plComb_eq (p0 : ℝ) (p : Fin 3 → ℝ) (μ : Fin 4) : plComb p0 p μ = plGen p0 p μ := by
  fin_cases μ <;>
  · simp only [plComb, Fin.sum_univ_four]
    norm_num [levi, lorGen, pLow, plGen]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pauliM] <;> ring

/-! ## The Fierz identity for the Pauli–Lubanski combination -/

/-- The Minkowski weights `η_{μμ}`. -/
def minkW : Fin 4 → ℂ := ![1, -1, -1, -1]

/-- **Fierz identity**: `Σ_μ η_{μμ} (X^μ_P)_{ab} (X^μ_P)_{cd} = (p²/4) (2 δ_{ad} δ_{bc} − δ_{ab} δ_{cd})`, where
`p² = p⁰² − |p|² = det P`. -/
theorem plGen_fierz (p0 : ℝ) (p : Fin 3 → ℝ) (a b c d : Fin 2) :
    ∑ μ, minkW μ * (plGen p0 p μ a b * plGen p0 p μ c d) =
      ((p0 ^ 2 - p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 : ℝ) : ℂ) / 4 *
        (2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) a d * (1 : Matrix (Fin 2) (Fin 2) ℂ) b c) -
          (1 : Matrix (Fin 2) (Fin 2) ℂ) a b * (1 : Matrix (Fin 2) (Fin 2) ℂ) c d) := by
  simp only [Fin.sum_univ_four]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [plGen, pauliM, minkW] <;> apply Complex.ext <;> simp [← Complex.ofReal_pow] <;> ring

/-- The determinant of the Hermitian momentum is the Minkowski square. -/
lemma det_momH (p0 : ℝ) (p : Fin 3 → ℝ) :
    (momH p0 p).det = ((p0 ^ 2 - p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp only [momH, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The coordinates of a Hermitian momentum: `p⁰ = (P₀₀ + P₁₁)/2`. -/
def coord0 (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ((P 0 0 + P 1 1) / 2).re

/-- The spatial coordinates of a Hermitian momentum. -/
def coordV (P : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![(P 1 0).re, (P 1 0).im, ((P 0 0 - P 1 1) / 2).re]

/-- Every Hermitian `2 × 2` matrix is `p⁰ + p·σ` for its coordinates. -/
theorem momH_coords {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian) :
    momH (coord0 P) (coordV P) = P := by
  have h00 : (P 0 0).im = 0 := by
    have := hP.apply 0 0
    have h := congrArg Complex.im this
    simp at h; linarith
  have h11 : (P 1 1).im = 0 := by
    have := hP.apply 1 1
    have h := congrArg Complex.im this
    simp at h; linarith
  have h01 : P 0 1 = star (P 1 0) := (hP.apply 0 1).symm
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [momH, coord0, coordV, h01, h00, h11] <;> ring

end Lightlike.Poincare
