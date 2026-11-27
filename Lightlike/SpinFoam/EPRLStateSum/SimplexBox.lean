import Lightlike.SpinFoam.EPRLStateSum.PiFive
import Lightlike.SpinFoam.EPRLStateSum.GlobalGluing
import Lightlike.SpinFoam.EPRLStateSum.SimplexIntrinsic

/-!
# The vertex sum `simpEIAux` as a sum over a box of virtual spins

`simpBox J` is the box of the five virtual spins of `simpEIAux`, and `simpEIAux_eq_sum_box` writes
`simpEIAux J i` as `Σ_{l ∈ simpBox J} (Π_a nodeI J a (i a) (l a)) · ((-1)^(triPart J) · ampP J l)`,
which is the shape of the left side of `global_gluing_nodeI`.
-/

open Finset

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The box of the five virtual spins of the vertex sum `simpEIAux`. -/
def simpBox (J : Fin 5 → Fin 5 → ℕ) : Fin 5 → Finset ℕ :=
  ![range (J 0 1 + J 0 3 + 1), range (J 1 2 + J 1 4 + 1), range (J 2 3 + J 0 2 + 1),
    range (J 3 4 + J 1 3 + 1), range (J 0 4 + J 2 4 + 1)]

/-- The vertex weight of the virtual spins `l` in the sorted basis: `(-1)^(triPart J) * ampP J l`. -/
noncomputable def vertexF (J : Fin 5 → Fin 5 → ℕ) (l : Fin 5 → ℕ) : ℝ :=
  (-1) ^ triPart J * ampP J l

/-- The vertex weight of the virtual spins `l` in the positional basis: `recoupSign J l * ampP J l`, the
15j symbol with the cyclic-order intertwiners (`posF`). -/
noncomputable def vertexP (J : Fin 5 → Fin 5 → ℕ) (l : Fin 5 → ℕ) : ℝ :=
  recoupSign J l * ampP J l

/-- **`simpEIAux` as a sum over a box**, in the shape of `global_gluing_nodeI`. -/
theorem simpEIAux_eq_sum_box (J : Fin 5 → Fin 5 → ℕ) (i : Fin 5 → ℕ) :
    simpEIAux J i = ∑ l ∈ Fintype.piFinset (simpBox J),
      (∏ a, nodeI J a (i a) (l a)) * vertexF J l := by
  rw [sum_piFinset_five]
  unfold simpEIAux
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
    Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun l₃ _ =>
    Finset.sum_congr rfl fun l₄ _ => ?_
  simp only [Fin.prod_univ_five, vertexF]
  simp

end Lightlike.SpinFoam.EPRLStateSum
