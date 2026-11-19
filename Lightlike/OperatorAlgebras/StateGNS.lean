import Lightlike.OperatorAlgebras.FiniteStates
import Lightlike.OperatorAlgebras.GNSCyclic

/-!
# The GNS representation of every state on a matrix algebra

Jakšić, Ogata, Pautrat and Pillet, arXiv:1106.3786, Exercise 2.15, p. 61 (read), for every state `ν` (not only faithful ones): the
state `A ↦ tr(ν A)` of a density matrix is a positive linear functional (`densityState`), and Mathlib's GNS space of it, with the class of
`1`, is a cyclic representation with `⟪ζ, π(A) ζ⟫ = tr(ν A)` (`inner_gnsCyclicVec_densityState`, `denseRange_gnsCyclicVec`); it is unique up
to unitary equivalence (`gns_unique_cstar`). The C*-algebra structure of `Matrix n n ℂ` is Mathlib's (the operator norm on
`EuclideanSpace ℂ n`, scoped), the order the Loewner order (scoped).
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

namespace Lightlike.OperatorAlgebras

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The state `A ↦ tr(ν A)` of a positive semidefinite `ν`, as a positive linear functional. -/
noncomputable def densityState {ν : Matrix n n ℂ} (hν : ν.PosSemidef) : Matrix n n ℂ →ₚ[ℂ] ℂ :=
  .mk₀ ((traceLinearMap n ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ ν) fun _ hA => trace_mul_nonneg hν hA.posSemidef

lemma densityState_apply {ν : Matrix n n ℂ} (hν : ν.PosSemidef) (A : Matrix n n ℂ) : densityState hν A = (ν * A).trace :=
  rfl

/-- **GNS for every state** (Exercise 2.15 (1)-(2), for any density matrix `ν`): `⟪ζ, π(A) ζ⟫ = tr(ν A)` in the GNS space of
`A ↦ tr(ν A)`, and `ζ` is cyclic (`denseRange_gnsCyclicVec`). -/
theorem inner_gnsCyclicVec_densityState {ν : Matrix n n ℂ} (hν : ν.PosSemidef) (A : Matrix n n ℂ) :
    ⟪gnsCyclicVec (densityState hν), (densityState hν).gnsStarAlgHom A (gnsCyclicVec (densityState hν))⟫_ℂ =
      (ν * A).trace :=
  inner_gnsCyclicVec _ A

/-- A non-faithful example: the pure state `|0⟩⟨0|` on `2 × 2` matrices. -/
noncomputable def pureState0 : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec (Pi.single 0 1) (star (Pi.single 0 1))

lemma pureState0_posSemidef : pureState0.PosSemidef := posSemidef_vecMulVec_self_star _

lemma pureState0_not_posDef : ¬ pureState0.PosDef := by
  intro h
  have := (posDef_iff_dotProduct_mulVec.mp h).2 (x := Pi.single 1 1) (by simp)
  simp [pureState0, mulVec, dotProduct, vecMulVec_apply, Fin.sum_univ_two] at this

/-- **GNS for a non-faithful state**: for the pure state `|0⟩⟨0|`, `⟪ζ, π(A) ζ⟫ = A₀₀`. -/
theorem gns_pureState0 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ⟪gnsCyclicVec (densityState pureState0_posSemidef),
      (densityState pureState0_posSemidef).gnsStarAlgHom A (gnsCyclicVec (densityState pureState0_posSemidef))⟫_ℂ =
      A 0 0 := by
  rw [inner_gnsCyclicVec_densityState]
  simp [pureState0, trace, mul_apply, vecMulVec_apply, Fin.sum_univ_two]

end Lightlike.OperatorAlgebras
