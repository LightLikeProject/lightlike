import Lightlike.PL.PachnerPL

/-!
# The dimension of a bistellar move on a closed combinatorial manifold

`IsBistellar K A B` asks only that `A` and `B` be nonempty, disjoint, that `lk(A, K) = ∂B` and that
`B` not be a face. On a closed combinatorial `n`-manifold the link of a nonempty face `A` is a sphere
on `n + 2 − #A` vertices (`IsClosedCombManifold.link_face`), and the boundary of the simplex `B` is
a sphere on `#B` vertices; stellar equivalent complexes have the same dimension
(`StellarEquivIn.maxCard_eq`). So `#A + #B = n + 2`
(`IsClosedCombManifold.card_add_card_of_isBistellar`): `A` is an `r`-simplex and `B` an
`(n − r)`-simplex, and on closed combinatorial manifolds the moves are exactly those of Lickorish's
Definition 2.3 (*Simplicial moves on complexes and manifolds*, 1999).
-/

open Finset

namespace Lightlike.PL

namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- **The dimension of a bistellar move**: on a closed combinatorial `n`-manifold, a bistellar move
`κ(A, B)` has `#A + #B = n + 2`, i.e. `dim A + dim B = n`. -/
theorem IsClosedCombManifold.card_add_card_of_isBistellar {n : ℕ} {K : SComplex V}
    (hK : IsClosedCombManifold n K) {A B : Finset V} (h : IsBistellar K A B) : #A + #B = n + 2 := by
  obtain ⟨C, hC, hLC⟩ := hK.link_face h.mem h.nonempty_left
  rw [h.link_eq, lift_boundary] at hLC
  have hA := hK.card_le h.mem
  have hCne : C.Nonempty := card_pos.1 (by omega)
  have hmc := hLC.maxCard_eq
  rw [maxCard_boundary (h.nonempty_right.map), maxCard_boundary hCne, card_map] at hmc
  have hB := card_pos.2 h.nonempty_right
  omega

end SComplex

end Lightlike.PL
