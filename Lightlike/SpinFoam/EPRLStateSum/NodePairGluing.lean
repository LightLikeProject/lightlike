import Lightlike.SpinFoam.EPRLStateSum.SimplexIntrinsic
import Lightlike.SpinFoam.EPRLStateSum.RecouplingTranspose

/-!
# Gluing two 4-simplices along a tetrahedron in the intrinsic basis

In a closed 4-complex each tetrahedron lies in exactly two 4-simplices. In the intrinsic basis
`nodeI` (`SimplexIntrinsic.lean`) the tetrahedron label `i` enters both vertices through the same
recoupling matrix, so the sum over `i` is the column orthogonality of that matrix:

* `sum_nodeI_mul_left`: for two nodes whose sorted leg spins agree,
  `Σ_i nodeI J a i l · nodeI J' a' i l' = δ_{ll'}` on the admissible `l`.
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

/-- **Gluing along a tetrahedron (intrinsic basis).** If the four leg spins of the node `a` of `J`
and of the node `a'` of `J'` agree in the sorted order, then summing the tetrahedron label `i` over
both node matrices gives the identity on the admissible `(02)(13)` labels `l`. -/
theorem sum_nodeI_mul_left (J J' : Fin 5 → Fin 5 → ℕ) (a a' : Fin 5)
    (h0 : J a (a.succAbove 0) = J' a' (a'.succAbove 0))
    (h1 : J a (a.succAbove 1) = J' a' (a'.succAbove 1))
    (h2 : J a (a.succAbove 2) = J' a' (a'.succAbove 2))
    (h3 : J a (a.succAbove 3) = J' a' (a'.succAbove 3)) (l l' : ℕ) :
    ∑ i ∈ range (J a (a.succAbove 0) + J a (a.succAbove 1) + 1), nodeI J a i l * nodeI J' a' i l' =
      if l = l' ∧ Pentagon.Tri (J a (a.succAbove 0)) (J a (a.succAbove 2)) l ∧
        Pentagon.Tri l (J a (a.succAbove 1)) (J a (a.succAbove 3)) then 1 else 0 := by
  unfold nodeI
  rw [← h0, ← h1, ← h2, ← h3]
  exact sum_fourRecoupling_mul_left _ _ _ _ l l'

/-- The same for a node glued to itself (`J' = J`, `a' = a`). -/
theorem sum_nodeI_mul_self (J : Fin 5 → Fin 5 → ℕ) (a : Fin 5) (l l' : ℕ) :
    ∑ i ∈ range (J a (a.succAbove 0) + J a (a.succAbove 1) + 1), nodeI J a i l * nodeI J a i l' =
      if l = l' ∧ Pentagon.Tri (J a (a.succAbove 0)) (J a (a.succAbove 2)) l ∧
        Pentagon.Tri l (J a (a.succAbove 1)) (J a (a.succAbove 3)) then 1 else 0 :=
  sum_nodeI_mul_left J J a a rfl rfl rfl rfl l l'

end Lightlike.SpinFoam.EPRLStateSum
