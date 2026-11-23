import Mathlib

/-! Scratch check that `Circle` is locally connected via its manifold structure (see `JordanLocConn.lean`). -/

open scoped Manifold ContDiff

example : LocallyConnectedSpace Circle :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 1)) Circle
