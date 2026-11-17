# Colored graphs of group field theory

## Abstract (Alpha)

This API treats the combinatorics of colored graphs, the Feynman graphs of the colored group field
theory. A colored graph has vertices of two orientations and lines of one of several colors, with
exactly one line of each color at every vertex and every line joining opposite orientations. Its
connected pieces made of a given set of colors are the bubbles, and the graph is dual to a
triangulated pseudo-manifold whose simplices are the bubbles. In dimension two the Euler
characteristic of the dual, and so its genus, is computed from the number of vertices and of
bicolored cycles.

## Content (Alpha)

A colored graph of dimension `D` is given by one involution per color without fixed points and an
orientation that every involution flips [1]. The bubble of a vertex for a set of colors is the set of
vertices reachable along lines of those colors, and the `0`-bubbles are the vertices [1]. In
dimension two the dual complex has one triangle for each vertex, one edge for each line and one
vertex for each bicolored cycle, so its Euler characteristic is the number of bicolored cycles
minus half the number of vertices [1]. The graph with two vertices gives the 2-sphere and a graph
with six vertices gives the torus [1]. A graph with two lines of one color at a vertex is not a
colored graph [1]. The `1`-bubbles are the lines, a line has exactly two ends, every bubble contains a
vertex, and in a connected graph any two vertices are joined by a chain of lines [2]. The lines of `p`
colors restricted to a bubble form a colored graph of dimension `p - 1`, and it is connected [2]. The conditions for a complex with indexed
simplices to be a pseudo-manifold or a normal pseudo-manifold, and its Euler characteristic, are defined in
a form that keeps repeated simplices distinct [3]. The dual of a colored graph, with one simplex for each bubble of the
complementary colors, is pure and non-branching, strongly connected when the graph is connected, and
normal, so the dual of a connected colored graph is a normal pseudo-manifold, and every lower interval of the
dual is a Boolean lattice [4]. The link of a simplex of the dual is the dual of the bubble, as a colored graph, with the rank lowered
by that of the simplex [5]. In dimension two twice the Euler characteristic of the dual pseudo-complex is the count
from the faces [6], and it is an integer for every colored graph [7]. That
the dual of every colored graph is a normal simplicial pseudo-manifold, and
the identification of the bubbles with the links of the dual simplices, are due to Gurau {1}; they
are [TODO] here.

## Lean References

1. Lightlike/GFT/ColoredGraph.lean - `GFT.ColoredGraph`, `GFT.ColoredGraph.inv_ne`,
   `GFT.ColoredGraph.bubble`, `GFT.ColoredGraph.nBubbles`, `GFT.ColoredGraph.mem_bubble_iff`, `GFT.ColoredGraph.nBubbles_empty`, `GFT.ColoredGraph.even_card`,
   `GFT.not_nonempty_coloredGraph_fin3`,
   `GFT.ColoredGraph.twoChi2`, `GFT.theta`, `GFT.twoChi2_theta`, `GFT.torus`, `GFT.twoChi2_torus`,
   `GFT.IsProper`, `GFT.badLines_not_proper`
2. Lightlike/GFT/Bubble.lean - `GFT.ColoredGraph.mem_bubble_self`,
   `GFT.ColoredGraph.bubble_singleton`, `GFT.ColoredGraph.card_bubble_singleton`,
   `GFT.ColoredGraph.IsConnected`, `GFT.ColoredGraph.strongChain_of_connected`,
   `GFT.ColoredGraph.restrict`, `GFT.ColoredGraph.restrict_isConnected`
3. Lightlike/GFT/PseudoComplex.lean - `GFT.GradedPoset`, `GFT.GradedPoset.IsPseudoManifold`,
   `GFT.GradedPoset.link`, `GFT.GradedPoset.IsNormal`, `GFT.GradedPoset.f`,
   `GFT.GradedPoset.eulerChar`
4. Lightlike/GFT/Dual.lean - `GFT.ColoredGraph.DualSimplex`, `GFT.ColoredGraph.dual`,
   `GFT.ColoredGraph.dual_isPure`, `GFT.ColoredGraph.dual_isNonBranching`,
   `GFT.ColoredGraph.dual_isStronglyConnected`, `GFT.ColoredGraph.dual_isNormal`,
   `GFT.ColoredGraph.dual_isSimplicial`, `GFT.ColoredGraph.faceIso`,
   `GFT.ColoredGraph.dual_isNormalPseudoManifold`
5. Lightlike/GFT/DualLink.lean - `GFT.ColoredGraph.mem_bubble_restrict`,
   `GFT.ColoredGraph.linkTo`, `GFT.ColoredGraph.linkOf`, `GFT.ColoredGraph.linkIso`,
   `GFT.ColoredGraph.linkIso_rk`, `GFT.ColoredGraph.link_isDual`
6. Lightlike/GFT/DualEuler.lean - `GFT.ColoredGraph.dual_f`,
   `GFT.ColoredGraph.two_mul_nBubbles_singleton`, `GFT.ColoredGraph.eulerChar_dual`,
   `GFT.ColoredGraph.eulerChar_dual_eq_euler`
7. Lightlike/GFT/Euler.lean - `GFT.ColoredGraph.even_twoChi2`, `GFT.ColoredGraph.euler`,
   `GFT.ColoredGraph.two_mul_euler`

## References

1. R. Gurau, Lost in translation: topological singularities in group field theory, *Class. Quantum
   Grav.* 27 (2010) 235023, arXiv:1006.0714.
