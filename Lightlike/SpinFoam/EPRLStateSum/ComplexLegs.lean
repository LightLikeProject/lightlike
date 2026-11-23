import Lightlike.SpinFoam.EPRLStateSum.ComplexIncidence
import Lightlike.SpinFoam.EPRLStateSum.SharedTetLegs

/-!
# The hypotheses of `global_gluing_nodeI` for a closed 4-complex

`complexJ K col s` is `simplexJ` of the 4-simplex `s ∈ K.simps`. For the incidence bijection `e` of
`exists_complex_incidence`, `complex_hleg` shows that the sorted leg spins of the two incidences
of every tetrahedron agree, which is the hypothesis `hleg` of `global_gluing_nodeI`.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The triangle spins of the 4-simplices of `K` in the colouring `col`. -/
noncomputable def complexJ (K : Complex4 V) (col : Finset V → ℕ) (s : K.simps) :
    Fin 5 → Fin 5 → ℕ :=
  simplexJ s.1 (K.card_eq _ s.2) col

/-- **The leg hypothesis of the global gluing holds on a closed complex.** -/
theorem complex_hleg (K : Complex4 V) (col : Finset V → ℕ) (e : K.tets × Bool ≃ K.simps × Fin 5)
    (he : ∀ t b, incTet K (e (t, b)) = t) (t : K.tets) (k : Fin 4) :
    complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove k) =
      complexJ K col (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove k) := by
  have h : incSet K (e (t, false)) = incSet K (e (t, true)) :=
    (congrArg Subtype.val (he t false)).trans (congrArg Subtype.val (he t true)).symm
  exact simplexJ_succAbove_eq _ _ _ _ col _ _ h k

end Lightlike.SpinFoam.EPRLStateSum
