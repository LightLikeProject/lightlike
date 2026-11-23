import Lightlike.OperatorAlgebras.FiniteModular
import Lightlike.OperatorAlgebras.ModularFinite

/-!
# OP3 capstone: the modular state of a faithful state on a matrix algebra is KMS at `β = 1`

`ModularFinite.lean` treats a state `Tr (e^{-H} ·)` with its modular flow `σ_z(a) = e^{-izH} a e^{izH}`, and `FiniteModular.lean`
treats a positive definite `ρ` with `log ρ` built from the spectral decomposition.  This file joins the two: for a faithful state
`ρ` (positive definite, trace `1`) the Hamiltonian `H = -log ρ` gives `e^{-H} = ρ`, the flow of `H` is the modular dynamics `modGroup`,
and `ρ` is KMS at inverse temperature `1` for it (`isKMS_modular_one`, `modular_flow_eq_modGroup`).  It also gives the qubit
trust check in one statement: a diagonal qubit state of trace `1` is `β`-KMS for `H = diag (0, E)` iff it is the Gibbs state
(`qubit_isKMS_iff`).
-/

open Matrix NormedSpace
open scoped ComplexOrder

noncomputable section

namespace Lightlike.OperatorAlgebras

/-- `e^{-H} = ρ` for the modular Hamiltonian `H = -log ρ`. -/
lemma boltz_neg_logPosDef {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef) :
    boltz (-logPosDef hρ) (-1) = ρ := by
  simp [boltz, exp_logPosDef hρ]

/-- **The modular state is KMS at `β = 1`** for the flow of `H = -log ρ`: a faithful state `ρ` of a matrix algebra
satisfies `IsKMS (-log ρ) ρ 1` (the form of `FiniteKMS.lean`). -/
theorem isKMS_modular_one {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef) :
    IsKMS (-logPosDef hρ) ρ 1 := by
  have := isKMS_boltz (-logPosDef hρ)
  rwa [boltz_neg_logPosDef hρ] at this

/-- The state `Tr (e^{-H} ·)` for `H = -log ρ` is `Tr (ρ ·)`. -/
lemma omega_neg_logPosDef {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef) (a : Matrix (Fin n) (Fin n) ℂ) :
    omega (-logPosDef hρ) a = (ρ * a).trace := by
  rw [omega, boltz_neg_logPosDef hρ]

/-- The flow of `H = -log ρ` at real time is the modular dynamics `ς_ρ^t(A) = e^{it log ρ} A e^{-it log ρ}`. -/
theorem modular_flow_eq_modGroup {n : ℕ} {ρ : Matrix (Fin n) (Fin n) ℂ} (hρ : ρ.PosDef) (t : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : flow (-logPosDef hρ) (t : ℂ) A = modGroup hρ t A := by
  have h1 : (-(Complex.I * (t : ℂ))) • (-logPosDef hρ) = ((t : ℂ) * Complex.I) • logPosDef hρ := by
    rw [smul_neg, neg_smul, neg_neg, mul_comm]
  have h2 : (Complex.I * (t : ℂ)) • (-logPosDef hρ) = -(((t : ℂ) * Complex.I) • logPosDef hρ) := by
    rw [smul_neg, mul_comm]
  simp only [flow, boltz, modGroup, h1, h2]

/-- **The KMS condition for the qubit** `H = diag (0, E)`: a diagonal state `diag (p, q)` of trace `1` is `β`-KMS iff
`p = q e^{βE}`, i.e. iff it is the Gibbs state at inverse temperature `β`. -/
theorem qubit_isKMS_iff (E : ℂ) (β : ℝ) (p q : ℂ) (hpq : p + q = 1) :
    IsKMS (qubitHam E) (Matrix.diagonal ![p, q]) β ↔ p = q * Complex.exp (β * E) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    exact not_isKMS_of_ne E β p q hne h
  · have hexp : Complex.exp (β * E) * Complex.exp (-(β * E)) = 1 := by
      rw [← Complex.exp_add]; simp
    set w := Complex.exp (-(β * E)) with hw
    have hq : q = p * w := by
      calc q = q * (Complex.exp (β * E) * w) := by rw [hexp, mul_one]
        _ = p * w := by rw [h]; ring
    have hpz : p * (1 + w) = 1 := by
      calc p * (1 + w) = p + p * w := by ring
        _ = p + q := by rw [hq]
        _ = 1 := hpq
    have hZ' : (1 + w) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpz; exact zero_ne_one hpz
    have hb : exp (-((β : ℂ) • qubitHam E)) = Matrix.diagonal ![1, w] := by
      rw [← neg_smul]
      have := boltz_qubit E (-(β : ℂ))
      rw [boltz] at this
      rw [this, hw, neg_mul]
    have htrZ : (exp (-((β : ℂ) • qubitHam E))).trace = 1 + w := by
      rw [hb]; simp [Matrix.trace_diagonal, Fin.sum_univ_two]
    have htr : (Matrix.diagonal ![p, q]).trace = 1 := by
      simp [Matrix.trace_diagonal, Fin.sum_univ_two, hpq]
    refine (isKMS_iff_eq_gibbs _ _ β (by rw [htrZ]; exact hZ') htr).mpr ?_
    rw [gibbs, htrZ, hb, ← Matrix.diagonal_smul]
    have hp : p = (1 + w)⁻¹ := eq_inv_of_mul_eq_one_left hpz
    congr 1
    funext i
    fin_cases i
    · simp [hp]
    · simp [hq, hp, mul_comm]

end Lightlike.OperatorAlgebras

end
