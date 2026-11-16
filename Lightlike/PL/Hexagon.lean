import Lightlike.PL.Interlaced

/-!
# A hexagon with chords

A polygonal hexagon with three chords joining opposite vertices: six points `p k`, six simple
polygonal arcs `H k` from `p k` to `p (k + 1)`, and chords `D k` from `p k` to `p (k + 3)`, two
different arcs or chords meeting only in common endpoints. This is the shape of a polygonal
drawing of `K₃,₃`.
-/

open Set Lightlike.PL.Polygon

namespace Lightlike.PL

/-- The chain of the arc `H k`: the points `p k`, the interior points `h k`, the point `p (k+1)`. -/
def hexArc (p : Fin 6 → ℝ × ℝ) (h : Fin 6 → List (ℝ × ℝ)) (k : Fin 6) : List (ℝ × ℝ) :=
  p k :: h k ++ [p (k + 1)]

/-- The chain of the chord `D k`. -/
def hexChord (p : Fin 6 → ℝ × ℝ) (d : Fin 6 → List (ℝ × ℝ)) (k : Fin 6) : List (ℝ × ℝ) :=
  p k :: d k ++ [p (k + 3)]

/-- A **hexagon with three chords**. The chord `D (k + 3)` is the chord `D k` traversed backwards. -/
structure Hex where
  /-- The six corners. -/
  p : Fin 6 → ℝ × ℝ
  /-- The interior points of the six sides. -/
  h : Fin 6 → List (ℝ × ℝ)
  /-- The interior points of the chords. -/
  d : Fin 6 → List (ℝ × ℝ)
  inj : Function.Injective p
  hrev : ∀ k, d (k + 3) = (d k).reverse
  simpleH : ∀ k, IsSimpleChain (hexArc p h k)
  simpleD : ∀ k, IsSimpleChain (hexChord p d k)
  /-- Two different sides meet only in common endpoints. -/
  interHH : ∀ i j, i ≠ j →
    chainSet (hexArc p h i) ∩ chainSet (hexArc p h j) ⊆ {p i, p (i + 1)} ∩ {p j, p (j + 1)}
  /-- A side and a chord meet only in common endpoints. -/
  interHD : ∀ i j,
    chainSet (hexArc p h i) ∩ chainSet (hexChord p d j) ⊆ {p i, p (i + 1)} ∩ {p j, p (j + 3)}
  /-- Two different chords meet only in common endpoints. -/
  interDD : ∀ i j, i ≠ j → i ≠ j + 3 →
    chainSet (hexChord p d i) ∩ chainSet (hexChord p d j) ⊆ {p i, p (i + 3)} ∩ {p j, p (j + 3)}

end Lightlike.PL
