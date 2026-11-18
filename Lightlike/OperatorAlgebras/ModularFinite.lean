import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Modular theory of a faithful state on a matrix algebra, and the KMS condition

For a matrix algebra `M_n(ℂ)` and a faithful state `ω(a) = Tr(ρ a)` with `ρ = exp (-H)`, the modular flow is
`σ_z(a) = exp (-i z H) a exp (i z H)` and the state is KMS at inverse temperature `1` for it: the correlation
functions `F(z) = Tr (e^{-H} b σ_z(a))` take the values `ω(b σ_s(a))` on the real line and `ω(σ_s(a) b)` on the line
`Im z = -1` (Witten, *Notes on some entanglement properties of quantum field theory*, arXiv:1803.04993, Section 4.2,
equations (4.46) and (4.47)). The modular operator of the vector `Ψ = ρ^{1/2}` in the Hilbert–Schmidt space is
`Δ(y) = ρ y ρ⁻¹` and `S(y) = ρ^{-1/2} y† ρ^{1/2}` is the antilinear involution with `S (a Ψ) = a† Ψ` and `Δ = S† S`
(Section 4.1, equations (4.4) and (4.11)).
-/

open NormedSpace Matrix

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {n : ℕ}

/-- The complexified Boltzmann factor `exp (z H)` of a matrix `H`. -/
def boltz (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ := exp (z • H)

lemma boltz_add (H : Matrix (Fin n) (Fin n) ℂ) (z w : ℂ) : boltz H (z + w) = boltz H z * boltz H w := by
  unfold boltz
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl H).smul_left z).smul_right w)

lemma boltz_comm (H : Matrix (Fin n) (Fin n) ℂ) (z w : ℂ) : boltz H z * boltz H w = boltz H w * boltz H z := by
  rw [← boltz_add, ← boltz_add, add_comm]

lemma boltz_zero (H : Matrix (Fin n) (Fin n) ℂ) : boltz H 0 = 1 := by
  simp [boltz]

lemma boltz_neg_mul (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : boltz H (-z) * boltz H z = 1 := by
  rw [← boltz_add, neg_add_cancel, boltz_zero]

lemma boltz_mul_neg (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : boltz H z * boltz H (-z) = 1 := by
  rw [← boltz_add, add_neg_cancel, boltz_zero]

/-- **The state** `ω_H(a) = Tr (e^{-H} a)` (a state when `Tr e^{-H} = 1`; faithful when `H` is Hermitian). -/
def omega (H : Matrix (Fin n) (Fin n) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) : ℂ := trace (boltz H (-1) * a)

/-- **The modular flow** `σ_z(a) = e^{-i z H} a e^{i z H}`, entire in `z`. -/
def flow (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  boltz H (-(Complex.I * z)) * a * boltz H (Complex.I * z)

/-- **The KMS condition at inverse temperature `1`** for the modular flow of `ω_H`:
`ω(b σ_{s - i}(a)) = ω(σ_s(a) b)` for every complex `s` (Witten, (4.47)). -/
theorem kms (H a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    omega H (b * flow H (s - Complex.I) a) = omega H (flow H s a * b) := by
  unfold omega flow
  set P := boltz H (-(Complex.I * s)) with hP
  set Q := boltz H (Complex.I * s) with hQ
  set e1 := boltz H (-1) with he1
  set E := boltz H 1 with hE
  have h1 : boltz H (-(Complex.I * (s - Complex.I))) = P * e1 := by
    rw [hP, he1, ← boltz_add]; congr 1; linear_combination Complex.I_sq
  have h2 : boltz H (Complex.I * (s - Complex.I)) = Q * E := by
    rw [hQ, hE, ← boltz_add]; congr 1; linear_combination (-1 : ℂ) * Complex.I_sq
  have hEe : E * e1 = 1 := by rw [hE, he1, boltz_mul_neg]
  have hPe : e1 * P = P * e1 := boltz_comm H _ _
  rw [h1, h2]
  calc trace (e1 * (b * (P * e1 * a * (Q * E))))
      = trace ((e1 * (b * (P * e1 * a))) * (Q * E)) := by simp only [Matrix.mul_assoc]
    _ = trace ((Q * E) * (e1 * (b * (P * e1 * a)))) := Matrix.trace_mul_comm _ _
    _ = trace (Q * (b * (P * e1 * a))) := by
        congr 1
        calc (Q * E) * (e1 * (b * (P * e1 * a))) = Q * ((E * e1) * (b * (P * e1 * a))) := by
              simp only [Matrix.mul_assoc]
          _ = Q * (b * (P * e1 * a)) := by rw [hEe, Matrix.one_mul]
    _ = trace ((Q * b) * (e1 * (P * a))) := by
        congr 1
        rw [← hPe]; simp only [Matrix.mul_assoc]
    _ = trace ((e1 * (P * a)) * (Q * b)) := Matrix.trace_mul_comm _ _
    _ = trace (e1 * (P * a * Q * b)) := by simp only [Matrix.mul_assoc]


/-- The Boltzmann factor of a Hermitian matrix at a real exponent is Hermitian. -/
lemma boltz_conjTranspose {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (r : ℝ) :
    (boltz H (r : ℂ))ᴴ = boltz H (r : ℂ) := by
  unfold boltz
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq]
  simp

/-- **The Tomita operator** `S(y) = ρ^{-1/2} y† ρ^{1/2}` for `ρ = e^{-H}`, an antilinear map on the
Hilbert–Schmidt space `M_n(ℂ)`: `S (a ρ^{1/2}) = a† ρ^{1/2}` (Witten, (4.4)). -/
def tomita (H : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  boltz H ((1 / 2 : ℝ) : ℂ) * yᴴ * boltz H (((-1 / 2 : ℝ)) : ℂ)

/-- **The modular operator** `Δ(y) = ρ y ρ⁻¹` (Witten, (4.11)). -/
def modOp (H : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  boltz H (-1) * y * boltz H 1

/-- `S` is an involution. -/
theorem tomita_tomita {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (y : Matrix (Fin n) (Fin n) ℂ) :
    tomita H (tomita H y) = y := by
  have hA := boltz_conjTranspose hH (1 / 2)
  have hB := boltz_conjTranspose hH (-1 / 2)
  have hAB : boltz H ((1 / 2 : ℝ) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ) = 1 := by
    rw [← boltz_add]; push_cast; ring_nf; simpa using boltz_zero H
  have hBA : boltz H (((-1 / 2 : ℝ)) : ℂ) * boltz H ((1 / 2 : ℝ) : ℂ) = 1 := by
    rw [← boltz_add]; push_cast; ring_nf; simpa using boltz_zero H
  unfold tomita
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  calc boltz H ((1 / 2 : ℝ) : ℂ) * (boltz H (((-1 / 2 : ℝ)) : ℂ) * (y * boltz H ((1 / 2 : ℝ) : ℂ))) *
        boltz H (((-1 / 2 : ℝ)) : ℂ)
      = (boltz H ((1 / 2 : ℝ) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ)) * y *
          (boltz H ((1 / 2 : ℝ) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = y := by rw [hAB, Matrix.one_mul, Matrix.mul_one]

/-- **`Δ = S† S`** for the Hilbert–Schmidt inner product `⟪x, y⟫ = Tr (x† y)`: `⟪S y, S z⟫ = ⟪z, Δ y⟫`
(Witten, (4.11) and the definition of `Δ_Ψ` as `S_Ψ† S_Ψ`). -/
theorem inner_tomita {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (y z : Matrix (Fin n) (Fin n) ℂ) :
    trace ((tomita H y)ᴴ * tomita H z) = trace (zᴴ * modOp H y) := by
  have hA := boltz_conjTranspose hH (1 / 2)
  have hB := boltz_conjTranspose hH (-1 / 2)
  have hAA : boltz H ((1 / 2 : ℝ) : ℂ) * boltz H ((1 / 2 : ℝ) : ℂ) = boltz H 1 := by
    rw [← boltz_add]; congr 1; push_cast; ring
  have hBB : boltz H (((-1 / 2 : ℝ)) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ) = boltz H (-1) := by
    rw [← boltz_add]; congr 1; push_cast; ring
  unfold tomita modOp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA, hB]
  set A := boltz H ((1 / 2 : ℝ) : ℂ)
  set B := boltz H (((-1 / 2 : ℝ)) : ℂ)
  calc trace (B * (y * A) * (A * zᴴ * B))
      = trace (B * (B * (y * (A * A) * zᴴ))) := by
        rw [show B * (y * A) * (A * zᴴ * B) = (B * (y * A * (A * zᴴ))) * B by simp only [Matrix.mul_assoc]]
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = trace ((B * B) * (y * (A * A)) * zᴴ) := by simp only [Matrix.mul_assoc]
    _ = trace (zᴴ * (boltz H (-1) * y * boltz H 1)) := by
        rw [hAA, hBB, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

/-- `S (a ρ^{1/2}) = a† ρ^{1/2}`: the defining property of the Tomita operator (Witten, (4.4)). -/
theorem tomita_apply {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (a : Matrix (Fin n) (Fin n) ℂ) :
    tomita H (a * boltz H (((-1 / 2 : ℝ)) : ℂ)) = aᴴ * boltz H (((-1 / 2 : ℝ)) : ℂ) := by
  have hB := boltz_conjTranspose hH (-1 / 2)
  have hAB : boltz H ((1 / 2 : ℝ) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ) = 1 := by
    rw [← boltz_add]; push_cast; ring_nf; simpa using boltz_zero H
  unfold tomita
  rw [Matrix.conjTranspose_mul, hB]
  calc boltz H ((1 / 2 : ℝ) : ℂ) * (boltz H (((-1 / 2 : ℝ)) : ℂ) * aᴴ) * boltz H (((-1 / 2 : ℝ)) : ℂ)
      = (boltz H ((1 / 2 : ℝ) : ℂ) * boltz H (((-1 / 2 : ℝ)) : ℂ)) * aᴴ * boltz H (((-1 / 2 : ℝ)) : ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hAB, Matrix.one_mul]

/-- **The modular flow is multiplicative**: `σ_z (a b) = σ_z(a) σ_z(b)` (conjugation by an invertible matrix). -/
theorem flow_mul (H a b : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : flow H z (a * b) = flow H z a * flow H z b := by
  unfold flow
  have h : boltz H (Complex.I * z) * boltz H (-(Complex.I * z)) = 1 := boltz_mul_neg H _
  calc boltz H (-(Complex.I * z)) * (a * b) * boltz H (Complex.I * z)
      = boltz H (-(Complex.I * z)) * a * (boltz H (Complex.I * z) * boltz H (-(Complex.I * z))) * b *
          boltz H (Complex.I * z) := by rw [h]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- **The modular flow is a one-parameter group**: `σ_{z + w} = σ_z ∘ σ_w`. -/
theorem flow_add (H a : Matrix (Fin n) (Fin n) ℂ) (z w : ℂ) : flow H (z + w) a = flow H z (flow H w a) := by
  unfold flow
  have e1 : -(Complex.I * (z + w)) = -(Complex.I * z) + -(Complex.I * w) := by ring
  have e2 : Complex.I * (z + w) = Complex.I * w + Complex.I * z := by ring
  rw [e1, e2, boltz_add, boltz_add]
  simp only [Matrix.mul_assoc]

/-- **The state is invariant under its modular flow**: `ω(σ_z(a)) = ω(a)`. -/
theorem omega_flow (H a : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : omega H (flow H z a) = omega H a := by
  unfold omega flow
  have hc : boltz H (-1) * boltz H (-(Complex.I * z)) = boltz H (-(Complex.I * z)) * boltz H (-1) := boltz_comm H _ _
  have h : boltz H (Complex.I * z) * boltz H (-(Complex.I * z)) = 1 := boltz_mul_neg H _
  calc trace (boltz H (-1) * (boltz H (-(Complex.I * z)) * a * boltz H (Complex.I * z)))
      = trace ((boltz H (Complex.I * z) * (boltz H (-1) * boltz H (-(Complex.I * z)))) * a) := by
        rw [show boltz H (-1) * (boltz H (-(Complex.I * z)) * a * boltz H (Complex.I * z)) =
          (boltz H (-1) * (boltz H (-(Complex.I * z)) * a)) * boltz H (Complex.I * z) by simp only [Matrix.mul_assoc]]
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = trace (boltz H (-1) * a) := by
        rw [hc, ← Matrix.mul_assoc, h, Matrix.one_mul]

/-- `ρ` is `(H, β)`-KMS: `Tr (ρ b σ_{s - i β}(a)) = Tr (ρ σ_s(a) b)` for the flow `σ_z(a) = e^{-i z H} a e^{i z H}`. -/
def IsKMS (ρ H : Matrix (Fin n) (Fin n) ℂ) (β : ℂ) : Prop :=
  ∀ a b : Matrix (Fin n) (Fin n) ℂ, ∀ s : ℂ,
    trace (ρ * (b * flow H (s - Complex.I * β) a)) = trace (ρ * (flow H s a * b))

lemma boltz_smul (H : Matrix (Fin n) (Fin n) ℂ) (β w : ℂ) : boltz (β • H) w = boltz H (β * w) := by
  unfold boltz; rw [smul_smul, mul_comm]

lemma flow_smul (H a : Matrix (Fin n) (Fin n) ℂ) (β z : ℂ) : flow (β • H) z a = flow H (β * z) a := by
  unfold flow
  rw [boltz_smul, boltz_smul, show β * (-(Complex.I * z)) = -(Complex.I * (β * z)) by ring,
    show β * (Complex.I * z) = Complex.I * (β * z) by ring]

/-- **The Gibbs state is KMS at its own temperature**: `ρ = e^{-β H}` is `(H, β)`-KMS (for `β ≠ 0`). -/
theorem isKMS_gibbs (H : Matrix (Fin n) (Fin n) ℂ) {β : ℂ} (hβ : β ≠ 0) :
    IsKMS (boltz (β • H) (-1)) H β := by
  intro a b s
  have := kms (β • H) a b (s / β)
  unfold omega at this
  rw [flow_smul, flow_smul] at this
  have h1 : β * (s / β - Complex.I) = s - Complex.I * β := by field_simp
  have h2 : β * (s / β) = s := by field_simp
  rw [h1, h2] at this
  exact this

/-- The Hamiltonian of a qubit with energy splitting `E`. -/
def qubitH (E : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, E]

lemma boltz_qubit (E w : ℂ) : boltz (qubitH E) w = Matrix.diagonal ![1, Complex.exp (w * E)] := by
  unfold boltz qubitH
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [← Complex.exp_eq_exp_ℂ]

/-- **A non-Gibbs state fails the KMS condition**: for the diagonal state `ρ = diag (p, q)` and the qubit
Hamiltonian `diag (0, E)`, KMS at inverse temperature `β` forces `p = q e^{β E}`, the Gibbs weights. -/
theorem not_isKMS_of_ne (E β p q : ℂ) (h : p ≠ q * Complex.exp (β * E)) :
    ¬ IsKMS (Matrix.diagonal ![p, q]) (qubitH E) β := by
  intro hK
  have := hK (Matrix.single 0 1 1) (Matrix.single 1 0 1) 0
  have e1 : -(Complex.I * (0 - Complex.I * β)) = -β := by
    have := Complex.I_sq; linear_combination β * this
  have e2 : Complex.I * (0 - Complex.I * β) = β := by
    have := Complex.I_sq; linear_combination (-β) * this
  simp only [flow, boltz_qubit, mul_zero, zero_mul, zero_sub, neg_zero, Complex.exp_zero] at this
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.single_apply] at this
  have e3 : -(Complex.I * (Complex.I * β) * E) = β * E := by
    have := Complex.I_sq; linear_combination (-(β * E)) * this
  rw [e3] at this
  exact h this.symm

end Lightlike.OperatorAlgebras

end
