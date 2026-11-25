import Lightlike.GFT.Dual
import Lightlike.GFT.DualEuler
import Lightlike.GFT.DualSurface

/-!
# G2-033 check: the dual of a connected colored graph is a normal pseudo-manifold

Regression file for the row G2-033 (milestone GF1, Gurau 2010, Theorem 2). The object is
`Lightlike.GFT.ColoredGraph.dual_isNormalPseudoManifold`, proved in `Lightlike/GFT/Dual.lean`. This file
restates it for every dimension and connected graph, and checks that it depends on the standard axioms
only. It is not imported by `Lightlike.lean`.
-/

open Lightlike.GFT

/-- Every connected (D+1)-colored graph has a normal pseudo-manifold as its dual, of top rank `D + 1`. -/
example {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V] (G : ColoredGraph D V) (h : G.IsConnected) :
    (ColoredGraph.dual G).IsNormalPseudoManifold (D + 1) :=
  ColoredGraph.dual_isNormalPseudoManifold G h

/-- The trust check in `D = 2`: the Euler characteristic of the dual is that of the graph. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : ColoredGraph 2 V) :
    (ColoredGraph.dual G).eulerChar 3 = G.euler :=
  ColoredGraph.eulerChar_dual_eq_euler G

#print axioms ColoredGraph.dual_isNormalPseudoManifold
#print axioms ColoredGraph.eulerChar_dual_eq_euler
#print axioms badLines_not_proper
