import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The KMS condition in finite dimensions: KMS states are Gibbs states

Jakšić, Ogata, Pautrat and Pillet, "Entropic fluctuations in quantum statistical mechanics. An introduction", arXiv:1106.3786
(read): for the finite quantum system `O = B(K)` with dynamics `τ^t(A) = e^{itH} A e^{-itH}` (eq. (2.23)), a state `ρ` (a density
matrix, `ρ(A) = tr(ρ A)`, Section 2.1) is `β`-KMS if `ρ(AB) = ρ(τ^{-iβ}(B) A)` for all `A, B` (eq. (2.24), Section 2.9, p. 53), and
`ρ` is `β`-KMS iff `ρ` is the Gibbs state `e^{-βH} / tr(e^{-βH})` (Proposition 2.20, p. 53).

Here `O` is `Matrix n n ℂ`, `τ^{-iβ}(B) = e^{βH} B e^{-βH}` (`imagEvol`), and the statements are `isKMS_gibbs` and `isKMS_iff_eq_gibbs`.
-/

open Matrix NormedSpace

namespace Lightlike.OperatorAlgebras

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The dynamics at imaginary time `-iβ`: `τ^{-iβ}(B) = e^{βH} B e^{-βH}` for `τ^t(B) = e^{itH} B e^{-itH}`. -/
noncomputable def imagEvol (H : Matrix n n ℂ) (β : ℝ) (B : Matrix n n ℂ) : Matrix n n ℂ :=
  exp ((β : ℂ) • H) * B * exp (-((β : ℂ) • H))

/-- **The `β`-KMS condition** (eq. (2.24)): `tr(ρ A B) = tr(ρ τ^{-iβ}(B) A)` for all `A, B`. -/
def IsKMS (H ρ : Matrix n n ℂ) (β : ℝ) : Prop :=
  ∀ A B : Matrix n n ℂ, (ρ * (A * B)).trace = (ρ * (imagEvol H β B * A)).trace

/-- The Gibbs state `e^{-βH} / tr(e^{-βH})`. -/
noncomputable def gibbs (H : Matrix n n ℂ) (β : ℝ) : Matrix n n ℂ :=
  (exp (-((β : ℂ) • H))).trace⁻¹ • exp (-((β : ℂ) • H))

lemma exp_neg_mul_exp (X : Matrix n n ℂ) : exp (-X) * exp X = 1 := by
  rw [← exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

lemma exp_mul_exp_neg (X : Matrix n n ℂ) : exp X * exp (-X) = 1 := by
  rw [← exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero]

lemma trace_gibbs (H : Matrix n n ℂ) (β : ℝ) (hZ : (exp (-((β : ℂ) • H))).trace ≠ 0) : (gibbs H β).trace = 1 := by
  rw [gibbs, trace_smul, smul_eq_mul, inv_mul_cancel₀ hZ]

/-- **The Gibbs state is `β`-KMS** (Jakšić-Ogata-Pautrat-Pillet, Section 2.9, p. 53, the computation before (2.24)). -/
theorem isKMS_gibbs (H : Matrix n n ℂ) (β : ℝ) : IsKMS H (gibbs H β) β := by
  intro A B
  set G := exp (-((β : ℂ) • H))
  have hGE : G * exp ((β : ℂ) • H) = 1 := exp_neg_mul_exp _
  simp only [gibbs, imagEvol, Matrix.smul_mul, trace_smul]
  congr 1
  calc (G * (A * B)).trace = (B * (G * A)).trace := by rw [← Matrix.mul_assoc, trace_mul_comm]
    _ = (G * (exp ((β : ℂ) • H) * B * G * A)).trace := by
      rw [show G * (exp ((β : ℂ) • H) * B * G * A) = (G * exp ((β : ℂ) • H)) * B * G * A by
        simp only [Matrix.mul_assoc], hGE, Matrix.one_mul, Matrix.mul_assoc]

/-- A matrix `X` with `tr(X B C) = tr(X C B)` for all `B, C` is a scalar matrix. -/
lemma mem_range_scalar_of_trace_comm {X : Matrix n n ℂ} (h : ∀ B C : Matrix n n ℂ, (X * B * C).trace = (X * C * B).trace) :
    X ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_single fun i j _ => ?_
  -- `X` commutes with `single i j 1`: the trace form `C ↦ tr(M C)` is nondegenerate
  have hc : ∀ C : Matrix n n ℂ, ((X * single i j 1 - single i j 1 * X) * C).trace = 0 := by
    intro C
    rw [Matrix.sub_mul, trace_sub, h, Matrix.mul_assoc (single i j 1), trace_mul_comm (single i j 1) (X * C),
      Matrix.mul_assoc, sub_self]
  have hz : X * single i j 1 - single i j 1 * X = 0 := by
    ext k l
    have := hc (single l k 1)
    rw [trace_mul_single] at this
    simpa using this
  exact (sub_eq_zero.mp hz).symm

/-- **KMS states are Gibbs states** (Jakšić-Ogata-Pautrat-Pillet, Proposition 2.20, p. 53): a matrix `ρ` of trace `1` is `β`-KMS
for the dynamics of `H` iff `ρ = e^{-βH} / tr(e^{-βH})`. -/
theorem isKMS_iff_eq_gibbs (H ρ : Matrix n n ℂ) (β : ℝ) (hZ : (exp (-((β : ℂ) • H))).trace ≠ 0) (hρ : ρ.trace = 1) :
    IsKMS H ρ β ↔ ρ = gibbs H β := by
  refine ⟨fun hK => ?_, fun h => h ▸ isKMS_gibbs H β⟩
  set E := exp ((β : ℂ) • H)
  set G := exp (-((β : ℂ) • H))
  have hGE : G * E = 1 := exp_neg_mul_exp _
  have hEG : E * G = 1 := exp_mul_exp_neg _
  set X := ρ * E
  have hX : ∀ B C : Matrix n n ℂ, (X * B * C).trace = (X * C * B).trace := by
    intro B C
    have := hK (E * C) B
    simp only [imagEvol] at this
    -- `tr(ρ E C B) = tr(ρ E B G E C) = tr(ρ E B C)`
    calc (X * B * C).trace = (ρ * (E * B * G * (E * C))).trace := by
          rw [show E * B * G * (E * C) = E * B * (G * E) * C by simp only [Matrix.mul_assoc], hGE, Matrix.mul_one]
          simp only [X, Matrix.mul_assoc]
      _ = (ρ * (E * C * B)).trace := this.symm
      _ = (X * C * B).trace := by simp only [X, Matrix.mul_assoc]
  obtain ⟨α, hα⟩ := mem_range_scalar_of_trace_comm hX
  have hρα : ρ = α • G := by
    have h1 : ρ = X * G := by simp only [X, Matrix.mul_assoc, hEG, Matrix.mul_one]
    rw [h1, ← hα, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul]
  have hαZ : α = G.trace⁻¹ := by
    have := hρ
    rw [hρα, trace_smul, smul_eq_mul] at this
    exact eq_inv_of_mul_eq_one_left this
  rw [hρα, hαZ]
  rfl

end Lightlike.OperatorAlgebras
