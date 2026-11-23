import Lightlike.Upstream.SU2Spin.SpinRep

/-!
# Trust checks for `Lightlike.Upstream.SU2Spin.SpinRep`

* Spin `0` is the trivial representation (known value).
* Spin `1/2` (`n = 1`) sends `-1 ∈ SU(2)` to `-1`, while spin `1` (`n = 2`) sends it to `1`
  (known values); a representation that ignored the parity of `n` would fail these.
* Wrong-model control: `spinMat 1` is not the trivial representation (`-1 ↦ -1 ≠ 1`).
* Non-vacuity: the irreducibility theorem applies to concrete spins.
-/

open Matrix

namespace SU2Spin.Tests

example (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 0 g = 1 := by
  have hk : kron 0 g = 1 := by
    ext s t
    have hst : s = t := Subsingleton.elim _ _
    subst hst
    simp [kron_apply]
  rw [spinMat, hk, Matrix.mul_one, emb_conjTranspose_mul_emb]

example : spinMat 1 negOne = -1 := by
  rw [spinMat_negOne]; simp

example : spinMat 2 negOne = 1 := by
  rw [spinMat_negOne]; simp

/-- Wrong-model control: spin `1/2` is not the trivial representation. -/
example : spinMat 1 negOne ≠ spinMat 1 1 := by
  rw [spinMat_negOne, spinMat_one]
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this
  norm_num at this

example : (spinRepresentation 1).IsIrreducible := spinRepresentation_isIrreducible
example : (spinRepresentation 2).IsIrreducible := spinRepresentation_isIrreducible

end SU2Spin.Tests
