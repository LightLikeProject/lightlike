import Mathlib
import Lightlike.Rows.G3_255.VertexOrders

/-!
# One-loop diagram classes of graviton exchange between two scalars, and "vertex diagrams"

Row G3-255 (target T-PG6, trust check "dropping the vertex diagrams shown to give another").
The one-loop corrections to scalar–scalar gravitational scattering fall into structural classes.
We record only which graviton self-vertices (`GravVertex`, from the expansion `g = η + κ h`
of the Einstein–Hilbert action) each class contains.  A diagram is a *vertex diagram* when it
contains at least one graviton self-vertex.  No per-diagram numerical coefficient is asserted
here: the repository holds only the total `41/(10π)` of Bjerrum-Bohr–Donoghue–Holstein (2003),
eq. (44), so the "dropping" statement is hypothesis-parametrised
(`sum_ne_sum_nonVertex`): if the vertex part of a sum of contributions is non-zero, dropping it
changes the sum.

The classes are named structurally (they describe the topology, not a numerical identification
with a specific figure of the paper).
-/

namespace Lightlike.Rows.G3_255

open GravVertex

/-- Structural classes of one-loop diagrams for scalar–scalar graviton exchange. -/
inductive OneLoopDiagram
  /-- Box: two graviton exchanges between the scalar lines. -/
  | box
  /-- Crossed box. -/
  | crossedBox
  /-- Triangle: a two-graviton–scalar–scalar (seagull) vertex on one line, two propagators
  on the other line. -/
  | triangle
  /-- Two seagull vertices, one on each scalar line. -/
  | doubleSeagull
  /-- Scalar line emits two gravitons that merge through a cubic graviton vertex into the
  exchanged graviton (vertex correction with a graviton triple vertex). -/
  | tripleVertexCorrection
  /-- Seagull on the scalar line whose two gravitons merge through a cubic vertex. -/
  | seagullTripleVertex
  /-- Graviton self-energy with two cubic vertices. -/
  | gravitonLoopCubic
  /-- Graviton self-energy tadpole with one quartic vertex. -/
  | gravitonLoopQuartic
  /-- Graviton self-energy from a loop of matter fields (no graviton self-vertex). -/
  | matterLoop
  /-- Scalar self-energy and external-leg insertions (no graviton self-vertex). -/
  | scalarSelfEnergy
  deriving DecidableEq, Repr

namespace OneLoopDiagram

/-- The graviton self-vertices contained in a diagram class. -/
def gravVertices : OneLoopDiagram → List GravVertex
  | box => []
  | crossedBox => []
  | triangle => []
  | doubleSeagull => []
  | tripleVertexCorrection => [GravVertex.cubic]
  | seagullTripleVertex => [GravVertex.cubic]
  | gravitonLoopCubic => [GravVertex.cubic, GravVertex.cubic]
  | gravitonLoopQuartic => [GravVertex.quartic]
  | matterLoop => []
  | scalarSelfEnergy => []

/-- A *vertex diagram*: one containing at least one graviton self-vertex. -/
def isVertexDiagram (d : OneLoopDiagram) : Prop := d.gravVertices ≠ []

instance (d : OneLoopDiagram) : Decidable d.isVertexDiagram := by
  unfold isVertexDiagram; infer_instance

/-- The box diagrams contain no graviton self-vertex. -/
theorem box_not_vertex : ¬ box.isVertexDiagram := by decide

theorem crossedBox_not_vertex : ¬ crossedBox.isVertexDiagram := by decide

theorem triangle_not_vertex : ¬ triangle.isVertexDiagram := by decide

/-- The triple-vertex correction is a vertex diagram. -/
theorem tripleVertexCorrection_vertex : tripleVertexCorrection.isVertexDiagram := by decide

theorem gravitonLoopCubic_vertex : gravitonLoopCubic.isVertexDiagram := by decide

theorem gravitonLoopQuartic_vertex : gravitonLoopQuartic.isVertexDiagram := by decide

/-- Total power of `κ` contributed by the graviton self-vertices of a diagram. -/
def selfVertexKappa (d : OneLoopDiagram) : ℕ := totalKappa d.gravVertices

theorem selfVertexKappa_pos_iff (d : OneLoopDiagram) :
    0 < d.selfVertexKappa ↔ d.isVertexDiagram := by
  cases d <;> decide

/-- Every diagram class is listed. -/
def all : List OneLoopDiagram :=
  [box, crossedBox, triangle, doubleSeagull, tripleVertexCorrection, seagullTripleVertex,
    gravitonLoopCubic, gravitonLoopQuartic, matterLoop, scalarSelfEnergy]

theorem mem_all (d : OneLoopDiagram) : d ∈ all := by
  cases d <;> decide

theorem nodup_all : all.Nodup := by decide

end OneLoopDiagram

open OneLoopDiagram

/-- Sum of the contributions `c d` over a list of diagram classes. -/
def diagramSum (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) : ℝ := (l.map c).sum

/-- The sum with the vertex diagrams dropped. -/
noncomputable def nonVertexSum (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) : ℝ :=
  diagramSum c (l.filter fun d => decide (¬ d.isVertexDiagram))

/-- The vertex part of the sum. -/
noncomputable def vertexSum (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) : ℝ :=
  diagramSum c (l.filter fun d => decide d.isVertexDiagram)

/-- The sum splits into vertex and non-vertex parts. -/
theorem diagramSum_split (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) :
    diagramSum c l = vertexSum c l + nonVertexSum c l := by
  induction l with
  | nil => simp [diagramSum, vertexSum, nonVertexSum]
  | cons d l ih =>
    unfold vertexSum nonVertexSum diagramSum at *
    by_cases h : d.isVertexDiagram
    · simp [h, ih]; ring
    · simp [h, ih]; ring

/-- Dropping the vertex diagrams changes the total exactly when the vertex part is non-zero. -/
theorem sum_ne_sum_nonVertex (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) :
    diagramSum c l ≠ nonVertexSum c l ↔ vertexSum c l ≠ 0 := by
  rw [diagramSum_split]
  constructor
  · intro h h0; apply h; rw [h0]; ring
  · intro h h0; apply h; linarith

/-- If the vertex diagrams are the only ones with total `v ≠ 0` and the full total is `T`, the
total without them is `T - v`. -/
theorem nonVertexSum_eq (c : OneLoopDiagram → ℝ) (l : List OneLoopDiagram) :
    nonVertexSum c l = diagramSum c l - vertexSum c l := by
  rw [diagramSum_split]; ring

end Lightlike.Rows.G3_255
