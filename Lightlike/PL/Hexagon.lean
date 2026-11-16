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

namespace Hex

variable (H : Hex)

/-- Shifting the labels by one step. -/
def rot : Hex where
  p k := H.p (k + 1)
  h k := H.h (k + 1)
  d k := H.d (k + 1)
  inj := H.inj.comp (add_left_injective 1)
  hrev k := by
    have := H.hrev (k + 1)
    rw [show k + 1 + 3 = k + 3 + 1 by abel] at this
    exact this
  simpleH k := by
    have := H.simpleH (k + 1)
    simpa [hexArc] using this
  simpleD k := by
    have := H.simpleD (k + 1)
    simpa [hexChord, add_right_comm] using this
  interHH i j hij := by
    have := H.interHH (i + 1) (j + 1) (fun h => hij (add_right_cancel h))
    simpa [hexArc] using this
  interHD i j := by
    have := H.interHD (i + 1) (j + 1)
    simpa [hexArc, hexChord, add_right_comm] using this
  interDD i j hij hij3 := by
    have := H.interDD (i + 1) (j + 1) (fun h => hij (add_right_cancel h))
      (fun h => hij3 (by
        have : i + 1 = j + 3 + 1 := by rw [h]; abel
        exact add_right_cancel this))
    simpa [hexChord, add_right_comm] using this

end Hex

end Lightlike.PL
