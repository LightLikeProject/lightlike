import Lightlike.GFT.Bubble
import Lightlike.GFT.Euler
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Gurau degree of a colored graph (definitions)

A colored graph of dimension `D` (`Lightlike.GFT.ColoredGraph`) has `D + 1` colors.  A *jacket*
(Gurau 2011) is a cyclic ordering of the colors, up to reversal.  It turns the graph into a ribbon
graph, whose vertices are the vertices of the graph, whose edges are the lines, and whose faces are
the bicolored cycles of two colors that are neighbours in the cyclic ordering.  The *genus* of the
jacket is `g = 1 - χ / 2`, `χ = V - E + F`, and the *Gurau degree* is the sum of the genera of the
jackets.

Here a cyclic ordering is a permutation `τ` of the colors with a single orbit (`IsCyclicOrder`), the
neighbours of `c` are `τ c` and `τ⁻¹ c`, and the faces are counted by
`F_τ = ∑_c #(bicolored cycles of colors {c, τ c})`.  Both `τ` and `τ⁻¹` give the same jacket, so the
degree is half the sum over all cyclic orderings.

## Main definitions

* `Lightlike.GFT.IsCyclicOrder`: a permutation of the colors with a single orbit.
* `Lightlike.GFT.ColoredGraph.jacketFaces`, `jacketEuler`, `jacketGenus`: the face count, the Euler
  characteristic `V - E + F` and the genus of the jacket of `τ`.
* `Lightlike.GFT.ColoredGraph.gurauDegree`: the Gurau degree.

## References

- R. Gurau, *The 1/N expansion of colored tensor models*, Ann. Henri Poincaré 12 (2011) 829,
  arXiv:1011.2726 (`gurau-2011`).
-/

open Finset

namespace Lightlike.GFT

variable {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A **cyclic ordering of the colors**: a permutation `τ` of `Fin (D + 1)` with a single orbit. -/
def IsCyclicOrder (τ : Equiv.Perm (Fin (D + 1))) : Prop :=
  ∀ c d : Fin (D + 1), ∃ k : Fin (D + 1), (τ ^ (k : ℕ)) c = d

instance (τ : Equiv.Perm (Fin (D + 1))) : Decidable (IsCyclicOrder τ) := by
  unfold IsCyclicOrder; infer_instance

/-- The cyclic orderings of the colors. -/
def cyclicOrders (D : ℕ) : Finset (Equiv.Perm (Fin (D + 1))) :=
  univ.filter fun τ => IsCyclicOrder τ

namespace ColoredGraph

/-- The number of faces of the jacket of the cyclic ordering `τ`: the bicolored cycles of colors
`{c, τ c}`, for `c` running over the colors. -/
def jacketFaces (G : ColoredGraph D V) (τ : Equiv.Perm (Fin (D + 1))) : ℕ :=
  ∑ c, G.nBubbles {c, τ c}

/-- The Euler characteristic `V - E + F` of the jacket of `τ`: `V` vertices, `E = (D + 1) V / 2`
lines (`V` is even) and `F` faces. -/
def jacketEuler (G : ColoredGraph D V) (τ : Equiv.Perm (Fin (D + 1))) : ℤ :=
  (Fintype.card V : ℤ) - (((D + 1) * (Fintype.card V / 2) : ℕ) : ℤ) + G.jacketFaces τ

/-- The genus of the jacket of `τ`: `(2 - χ) / 2` (for a connected graph `χ` is even). -/
def jacketGenus (G : ColoredGraph D V) (τ : Equiv.Perm (Fin (D + 1))) : ℤ :=
  (2 - G.jacketEuler τ) / 2

/-- **The Gurau degree**: the sum of the genera of the jackets.  Each jacket is counted twice in
the sum over cyclic orderings (`τ` and `τ⁻¹`), hence the division by two. -/
def gurauDegree (G : ColoredGraph D V) : ℤ :=
  (∑ τ ∈ cyclicOrders D, G.jacketGenus τ) / 2

end ColoredGraph

/-! ### Examples -/

/-- The theta graph has one jacket, of genus `0`, in dimension `2`. -/
example : theta.gurauDegree = 0 := by decide +kernel

/-- The torus graph has one jacket, of genus `1`, in dimension `2`. -/
example : torus.gurauDegree = 1 := by decide +kernel

end Lightlike.GFT
