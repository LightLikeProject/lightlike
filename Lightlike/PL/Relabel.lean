import Lightlike.PL.Join
import Lightlike.PL.Manifold
import Lightlike.PL.StellarHomeo
import Lightlike.PL.Image

/-!
# Relabelling the vertices of a simplex

Two finite vertex sets of the same size are exchanged by a permutation of the vertex type, so the
simplices on them are PL homeomorphic (a simplicial isomorphism, Lickorish p. 301-302), and a PL ball
of dimension `n` is PL homeomorphic to the simplex on any `n + 1` vertices.

## Main results

* `Lightlike.PL.SComplex.PLHomeomorphic.of_isPLBallIn`
-/

open Finset

namespace Lightlike.PL
namespace SComplex

variable {V : Type*} [DecidableEq V]

/-- **Simplices on the same number of vertices are PL homeomorphic.** -/
theorem PLHomeomorphic.simplex_relabel {A B : Finset V} (h : #A = #B) :
    PLHomeomorphic (simplex A) (simplex B) := by
  obtain ⟨σ, hσ⟩ := exists_perm_map_eq h
  have := PLHomeomorphic.map (simplex A) σ.toEmbedding
  rwa [map_simplex, hσ] at this

/-- **A PL ball is PL homeomorphic to the simplex on any vertex set of the right size.** -/
theorem PLHomeomorphic.of_isPLBallIn {n : ℕ} {K : SComplex V} (h : IsPLBallIn n K) {B : Finset V}
    (hB : #B = n + 1) : PLHomeomorphic K (simplex B) := by
  obtain ⟨A, hA, hKA⟩ := h
  exact (PLHomeomorphic.of_stellarEquivIn hKA).trans (PLHomeomorphic.simplex_relabel (by omega))

end SComplex

end Lightlike.PL
