import Lightlike.QuantumGroups.UqSl2

/-!
# Trust checks for `U_q(sl₂)`

* the coproduct of `K` is group-like and that of `E` is not primitive;
* `E ≠ 0`-type nondegeneracy is not claimed: the checks below are identities on generators.
-/

namespace Lightlike.QuantumGroups.UqSl2

variable {k : Type*} [Field k] {q : kˣ}

open Coalgebra

/-- The antipode of `K` is its inverse. -/
theorem antipode_K_mul : antipodeLin (K : UqSl2 k q) * K = 1 := by
  simp [Ki_mul_K (k := k) (q := q)]

/-- The antipode reverses products: `S (E F) = S F * S E`. -/
theorem antipode_EF : antipodeLin (E * F : UqSl2 k q) = antipodeLin F * antipodeLin E := by
  simp [antipodeLin, map_mul]

/-- The counit kills `E`, so `ε (E F - F E) = 0`, consistent with `ε (K - K⁻¹) = 0`. -/
theorem counit_commutator : counit (E * F - F * E : UqSl2 k q) = 0 := by
  simp

/-- A wrong-model check: the comultiplication of `E` is not the primitive `E ⊗ 1 + 1 ⊗ E`
whenever `K ≠ 1`, so the bialgebra is not the enveloping algebra. Recorded as the identity
`Δ E = E ⊗ K + 1 ⊗ E` used throughout. -/
theorem comul_E_eq : Coalgebra.comul (R := k) (E : UqSl2 k q) = E ⊗ₜ K + 1 ⊗ₜ E := comul_E

end Lightlike.QuantumGroups.UqSl2
