import Lightlike.PL.SimpleChain

/-!
# No polygonal drawing of `K₃,₃` in the plane

Statements only (not imported; `sorry`). This is the second claim of the proof of the weak Jordan
theorem by C. Thomassen, in the exposition of M. Klazar, arXiv:2604.04296, Section 2, Claim 2
(Klazar's numbering).

**The embedding notion.** A *polygonal drawing of `K₃,₃`* consists of six distinct points `u i`,
`v j` (`i, j ∈ Fin 3`) and nine **simple polygonal arcs**, one from `u i` to `v j` for each pair, each
a finite chain of straight segments (`IsSimpleChain`: consecutive points differ and no segment meets
the later ones except at the shared vertex), such that two different arcs meet **only in common
endpoints**. In particular an arc contains none of the six points except its own two ends. The
arcs are polygonal; the statement for arbitrary continuous arcs is a later step (Klazar, Claim 3).

**The proof route.** Klazar follows Thomassen with an orientation (left/right) argument. The proof
here splits the 6-cycle along polygonal chords (theta-split: a chord inside or outside a simple
polygon splits it into two simple polygons whose insides add up) instead.
-/

open Set

namespace Lightlike.PL

/-- A **polygonal drawing** in the plane of the bipartite graph with vertex classes of three
points and with the edges `E ⊆ Fin 3 × Fin 3`. With `E = Set.univ` this is a polygonal drawing of
`K₃,₃`. -/
structure PLDrawing (E : Set (Fin 3 × Fin 3)) where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The vertices of the arc from `u i` to `v j`, in order (used for `(i, j) ∈ E`). -/
  arc : Fin 3 → Fin 3 → List (ℝ × ℝ)
  /-- Each arc is a simple polygonal arc. -/
  simple : ∀ i j, (i, j) ∈ E → IsSimpleChain (arc i j)
  /-- Each arc starts at `u i`. -/
  head : ∀ i j, (i, j) ∈ E → (arc i j).head? = some (u i)
  /-- Each arc ends at `v j`. -/
  last : ∀ i j, (i, j) ∈ E → (arc i j).getLast? = some (v j)
  /-- Each arc has at least one segment. -/
  length_ge : ∀ i j, (i, j) ∈ E → 2 ≤ (arc i j).length
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ∈ E → (i', j') ∈ E → (i, j) ≠ (i', j') →
    chainSet (arc i j) ∩ chainSet (arc i' j') ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

/-- **There is no polygonal drawing of `K₃,₃` in the plane.** Six distinct points, joined across the
two classes by nine simple polygonal arcs that meet only in common endpoints, do not exist
(Thomassen's proof of the weak Jordan theorem; Klazar, Section 2, Claim 2, Klazar's numbering).

The proof splits the 6-cycle along polygonal chords instead of Thomassen's orientation argument. It
uses that the parity of the crossings of the horizontal ray, which is a count modulo 2, is additive
when a closed chain is cut along a chord and glued from the two halves: `chainParity_append` and
`chainParity_reverse` in `Lightlike/PL/Chain.lean` (the chord is counted twice, and `1 + 1 = 0`),
with `Polygon.parity_ofList` linking it to the parity of a polygon.

**Limits.** The arcs are polygonal arcs only; the statement for arbitrary continuous arcs is
Claim 3 (a later step). **Non-vacuity (planned).** The hypotheses can be satisfied: the drawing
with the edge `(2, 2)` removed, `PLDrawing (Set.univ \ {(2, 2)})`, is inhabited by eight explicit
segments in a convex position of the six points, so the disjointness hypotheses are not
contradictory; the example will be proved in `TestsPolygon.lean` when the theorem is imported. -/
theorem no_PL_K33 (d : PLDrawing Set.univ) : False := by
  sorry

end Lightlike.PL
