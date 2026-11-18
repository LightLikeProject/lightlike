import QuantumInfo.Entropy.SSA
import QuantumInfo.States.Entanglement

/-!
# Entropy: strong subadditivity and the Bell-state trust checks

Bridge to Physlib's `QuantumInfo` (the von Neumann entropy `Sᵥₙ`, the conditional entropy `qConditionalEnt` and strong
subadditivity are in `QuantumInfo.Entropy.VonNeumann` and `QuantumInfo.Entropy.SSA`; this module imports them, it does not
port them). Milestone OP4: strong subadditivity for finite-dimensional density matrices (Lieb and Ruskai 1973), with the
trust checks on the Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2` (Physlib's `Ket.MES`): `S(A) = log 2`, `S(AB) = 0`, and the
classical inequality `S(AB) ≥ S(A)` fails for it (the quantum conditional entropy is negative).

* `strong_subadditivity`: `S(A|BC) ≤ S(A|B)` (Physlib's `qConditionalEnt_strong_subadditivity`).
* `bell_entropies`: `S(AB) = 0` and `S(A) = log 2` for the Bell state.
* `bell_conditional_entropy_neg`: `S(A|B) = -log 2 < 0`, so `S(AB) < S(B)`.
-/

namespace Lightlike.OperatorAlgebras

section

variable {d₁ d₂ d₃ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃] [DecidableEq d₁] [DecidableEq d₂]
  [DecidableEq d₃]

/-- **Strong subadditivity of the von Neumann entropy** (Lieb-Ruskai), in the form `S(A|BC) ≤ S(A|B)`. -/
theorem strong_subadditivity (ρ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ ≤ qConditionalEnt ρ.assoc'.traceRight :=
  qConditionalEnt_strong_subadditivity ρ

end

/-- **The Bell state has `S(AB) = 0` and `S(A) = log 2`**: a pure state has zero entropy, and its reduced state is maximally
mixed. -/
theorem bell_entropies :
    Sᵥₙ (MState.pure (Ket.MES (Fin 2))) = 0 ∧ Sᵥₙ (MState.pure (Ket.MES (Fin 2))).traceRight = Real.log 2 := by
  refine ⟨Sᵥₙ_of_pure_zero _, ?_⟩
  rw [traceRight_pure_MES, MState.uniform, Sᵥₙ_ofClassical ProbDistribution.uniform, Hₛ_uniform]
  simp

/-- **The classical inequality `S(AB) ≥ S(A)` fails for the Bell state**: `S(A|B) = S(AB) - S(B) = -log 2 < 0`. -/
theorem bell_conditional_entropy_neg : qConditionalEnt (MState.pure (Ket.MES (Fin 2))) < 0 := by
  have h := bell_entropies
  have hl : Sᵥₙ (MState.pure (Ket.MES (Fin 2))).traceLeft = Real.log 2 := by
    rw [Sᵥₙ_of_partial_eq]; exact h.2
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold qConditionalEnt
  rw [h.1, hl]
  linarith

end Lightlike.OperatorAlgebras
