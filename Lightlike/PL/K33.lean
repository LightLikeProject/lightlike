import Lightlike.PL.PolygonSplit

/-!
# No polygonal drawing of `K₃,₃` in the plane

Statements only (not imported; `sorry`). This is the second claim of the proof of the weak Jordan
theorem by C. Thomassen, in the exposition of M. Klazar, arXiv:2604.04296, Section 2, Claim 2
(Klazar's numbering): if nine polygonal arcs join the three points `u i` to the three points
`v j` and meet only at their endpoints, we get a contradiction. The argument takes the 6-cycle through
six of the arcs, a simple closed polygon with an inside and an outside; the three remaining arcs lie in
the inside or in the outside, two of them on the same side; the 4-cycle through one of the two and the
arcs of the 6-cycle, and the Jordan theorem for it, separate the endpoints of the third.

## Plan of the file

1. `PLArc`: a polygonal arc given by a function `Fin (m + 1) → ℝ × ℝ`.
2. `PLArc.cyclePolygon`: the polygon obtained by concatenating arcs end to end (`sorry`).
3. `isSimple_cyclePolygon`: arcs that meet only at consecutive endpoints give a simple polygon.
4. `no_PL_K33`.
-/

open Set

namespace Lightlike.PL

/-- The `i`-th segment of the polygonal path `γ`. -/
def pathSeg {m : ℕ} (γ : Fin (m + 1) → ℝ × ℝ) (i : Fin m) : Set (ℝ × ℝ) :=
  segment ℝ (γ i.castSucc) (γ i.succ)

/-- The union of the segments of a polygonal path. -/
def pathSet {m : ℕ} (γ : Fin (m + 1) → ℝ × ℝ) : Set (ℝ × ℝ) := ⋃ i, pathSeg γ i

/-- A **polygonal arc**: the segments are nondegenerate, segments that are not neighbours are
disjoint, and neighbouring segments meet only at their common vertex. -/
def IsPLArc {m : ℕ} (γ : Fin (m + 1) → ℝ × ℝ) : Prop :=
  (∀ i : Fin m, γ i.castSucc ≠ γ i.succ) ∧
  (∀ i j : Fin m, i ≠ j → (j : ℕ) ≠ i + 1 → (i : ℕ) ≠ j + 1 → Disjoint (pathSeg γ i) (pathSeg γ j)) ∧
  (∀ i j : Fin m, (j : ℕ) = i + 1 → pathSeg γ i ∩ pathSeg γ j = {γ i.succ})

/-- A **polygonal `K₃,₃`-configuration**: nine polygonal arcs `γ i j` from `u i` to `v j`, meeting
pairwise only in common endpoints. -/
structure PLK33 where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The number of segments of each arc. -/
  m : Fin 3 → Fin 3 → ℕ
  /-- The nine arcs. -/
  γ : ∀ i j, Fin (m i j + 1) → ℝ × ℝ
  arc : ∀ i j, IsPLArc (γ i j)
  start : ∀ i j, γ i j 0 = u i
  stop : ∀ i j, γ i j (Fin.last _) = v j
  /-- The arcs meet only in the points `u i` and `v j` they share. -/
  disj : ∀ i j i' j', (i, j) ≠ (i', j') →
    pathSet (γ i j) ∩ pathSet (γ i' j') ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The six points are distinct. -/
  inj_u : Function.Injective u
  inj_v : Function.Injective v
  uv_ne : ∀ i j, u i ≠ v j

/-- **There is no polygonal drawing of `K₃,₃` in the plane** (Thomassen; Klazar, Section 2, Claim 2,
Klazar's numbering). -/
theorem no_PL_K33 (c : PLK33) : False := by
  sorry

end Lightlike.PL
