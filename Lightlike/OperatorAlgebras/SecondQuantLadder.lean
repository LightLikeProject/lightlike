import Lightlike.OperatorAlgebras.SecondQuantFinite
import PhyslibAlpha.Mathematics.LadderSystem.Basic

/-!
# Alignment of `dΓ` with Physlib's ladder systems

Physlib's `LadderSystem ℂ V d` (`PhyslibAlpha.Mathematics.LadderSystem.Basic`) is the bosonic case of `IsModeAlgebra`:
`d` annihilation and creation endomorphisms of a vector space `V` with the CCR, the bilinears `E i j = acᵢ aⱼ` with
`lie_E` (the bosonic `commutator_number`), and the linear map `toGlHomLinear : gl(d) → End V`, `single i j 1 ↦ E i j`,
whose bracket law `toGlHomLinear_lie` is the bosonic `dGamma_commutator`. `IsModeAlgebra` also covers the CAR
(`ε = -1`) and any algebra over `ℂ`, which is why `SecondQuantFinite` does not build on `LadderSystem`.

* `isModeAlgebra_ladderSystem`: a ladder system is a mode algebra with `ε = 1`;
* `dGamma_ladderSystem`: `dΓ(x) = L.toGlHomLinear x`.
-/

namespace Lightlike.OperatorAlgebras.SecondQuantFinite

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {d : ℕ}

/-- **A Physlib ladder system is a mode algebra with `ε = 1`.** -/
theorem isModeAlgebra_ladderSystem (L : LadderSystem ℂ V d) :
    IsModeAlgebra (R := Module.End ℂ V) 1 L.a L.ac :=
  isModeAlgebra_ccr
    (fun j k => by rw [← LieRing.of_associative_ring_bracket]; exact L.comm_a_ac j k)
    (fun j k => sub_eq_zero.mp (by rw [← LieRing.of_associative_ring_bracket]; exact L.comm_a_a j k))
    (fun j k => sub_eq_zero.mp (by rw [← LieRing.of_associative_ring_bracket]; exact L.comm_ac_ac j k))

/-- **`dΓ(x) = L.toGlHomLinear x`**: on a ladder system, `dGamma` is Physlib's `gl(d)`-action. -/
theorem dGamma_ladderSystem (L : LadderSystem ℂ V d) (x : Matrix (Fin d) (Fin d) ℂ) :
    dGamma L.a L.ac x = L.toGlHomLinear x := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  have hs : ∀ i j, Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : ℂ) := fun i j => by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  simp only [hs, map_sum, map_smul, LadderSystem.toGlHomLinear_single, LadderSystem.E, dGamma]

end Lightlike.OperatorAlgebras.SecondQuantFinite
